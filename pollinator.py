#!/usr/bin/env python3
"""
Super-simple live polling webapp (no deps, in-memory) with key features:
- Upload poll JSON -> unique poll URL
- Students vote + optional free text
- Live results via SSE
- Free-text +1 upvotes
- Download results as JSON/CSV
- Auto-expiry of polls (default 24h)
- External templates in templates/ folder
"""

from __future__ import annotations

import argparse
import csv
import html
import io
import json
import os
import re
import secrets
import sys
import threading
import time
import uuid
from dataclasses import dataclass, field
from http import HTTPStatus
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, List, Optional, Tuple
import urllib.parse
from io import BytesIO
import qrcode

# -----------------------------
# In-memory state
# -----------------------------

@dataclass
class Poll:
    poll_id: str
    created_at: float
    spec: Dict[str, Any]

    # votes: option_id -> count
    counts: Dict[str, int] = field(default_factory=dict)

    # device_id -> option_id (enforces one vote per device if enabled)
    device_votes: Dict[str, str] = field(default_factory=dict)

    # free text entries
    # text_id -> {"text": str, "count": int, "created_at": float}
    texts: Dict[str, Dict[str, Any]] = field(default_factory=dict)

    # device_id -> set(text_id)
    device_upvotes: Dict[str, set] = field(default_factory=dict)

    # SSE clients: list of writer(payload_str) callables
    sse_clients: List[Any] = field(default_factory=list)

    lock: threading.Lock = field(default_factory=threading.Lock)


POLLS: Dict[str, Poll] = {}
POLLS_LOCK = threading.Lock()

# Set by main()
APP_DIR = os.path.dirname(os.path.abspath(__file__))
TEMPLATES_DIR = os.path.join(APP_DIR, "templates")
STATIC_DIR = os.path.join(APP_DIR, "static")

# Auto-expiry config (set by main)
POLL_TTL_SECONDS = 24 * 60 * 60
GC_EVERY_SECONDS = 60


# -----------------------------
# Helpers
# -----------------------------

def now() -> float:
    return time.time()


def gen_id(nbytes: int = 6) -> str:
    return secrets.token_urlsafe(nbytes).rstrip("=")


def url_decode(s: str) -> str:
    s = s.replace("+", " ")
    out = []
    i = 0
    while i < len(s):
        if s[i] == "%" and i + 2 < len(s):
            try:
                out.append(chr(int(s[i+1:i+3], 16)))
                i += 3
                continue
            except Exception:
                pass
        out.append(s[i])
        i += 1
    return "".join(out)


def read_form(handler: BaseHTTPRequestHandler, max_bytes: int = 256_000) -> Dict[str, str]:
    length = int(handler.headers.get("Content-Length", "0") or "0")
    if length < 0 or length > max_bytes:
        raise ValueError("Form too large")
    body = handler.rfile.read(length).decode("utf-8", errors="replace")
    out: Dict[str, str] = {}
    for pair in body.split("&"):
        if not pair:
            continue
        if "=" in pair:
            k, v = pair.split("=", 1)
        else:
            k, v = pair, ""
        out[url_decode(k)] = url_decode(v)
    return out


def parse_json_body(handler: BaseHTTPRequestHandler, max_bytes: int = 64_000) -> Any:
    length = int(handler.headers.get("Content-Length", "0") or "0")
    if length <= 0:
        raise ValueError("Empty body")
    if length > max_bytes:
        raise ValueError("Body too large")
    raw = handler.rfile.read(length)
    try:
        return json.loads(raw.decode("utf-8"))
    except Exception as e:
        raise ValueError(f"Invalid JSON: {e}") from e


def get_or_set_device_id(handler: BaseHTTPRequestHandler) -> Tuple[str, Optional[str]]:
    cookie = SimpleCookie()
    if "Cookie" in handler.headers:
        cookie.load(handler.headers["Cookie"])
    if "device_id" in cookie and cookie["device_id"].value:
        return cookie["device_id"].value, None

    device_id = str(uuid.uuid4())
    set_cookie = f"device_id={device_id}; Path=/; Max-Age=31536000; SameSite=Lax"
    return device_id, set_cookie


def escape_student_text(s: str) -> str:
    return html.escape(s, quote=True)


def validate_poll_spec(spec: Dict[str, Any]) -> None:
    if not isinstance(spec, dict):
        raise ValueError("Spec must be a JSON object")

    q = spec.get("question_html")
    if not isinstance(q, str) or not q.strip():
        raise ValueError("question_html must be a non-empty string")

    options = spec.get("options")
    if not isinstance(options, list) or not options:
        raise ValueError("options must be a non-empty list")

    if len(options) > 30:
        raise ValueError("Too many options (max 30)")

    seen = set()
    for opt in options:
        if not isinstance(opt, dict):
            raise ValueError("Each option must be an object")
        oid = opt.get("id")
        lab = opt.get("label_html")
        if not isinstance(oid, str) or not oid:
            raise ValueError("Each option must have string id")
        if oid in seen:
            raise ValueError(f"Duplicate option id: {oid}")
        seen.add(oid)
        if not isinstance(lab, str):
            raise ValueError("Each option must have label_html string")

    ft = spec.get("free_text", {}) or {}
    if not isinstance(ft, dict):
        raise ValueError("free_text must be an object if provided")
    if "enabled" in ft and not isinstance(ft["enabled"], bool):
        raise ValueError("free_text.enabled must be boolean")
    if "max_len" in ft:
        ml = ft["max_len"]
        if (not isinstance(ml, int)) or ml < 1 or ml > 2000:
            raise ValueError("free_text.max_len must be int 1..2000")

    settings = spec.get("settings", {}) or {}
    if not isinstance(settings, dict):
        raise ValueError("settings must be an object if provided")
    if "one_vote_per_device" in settings and not isinstance(settings["one_vote_per_device"], bool):
        raise ValueError("settings.one_vote_per_device must be boolean")


def poll_snapshot(p: Poll) -> Dict[str, Any]:
    options = p.spec["options"]
    counts = {opt["id"]: int(p.counts.get(opt["id"], 0)) for opt in options}

    free_text_spec = p.spec.get("free_text") or {}
    ft_enabled = bool(free_text_spec.get("enabled"))
    texts_list = []
    if ft_enabled:
        items = []
        for tid, rec in p.texts.items():
            items.append({
                "id": tid,
                "text": rec["text"],            # already escaped
                "upvotes": int(rec.get("count", 0)),
                "created_at": float(rec.get("created_at", 0.0)),
            })
        items.sort(key=lambda r: (-r["upvotes"], r["created_at"]))
        texts_list = items

    return {
        "poll_id": p.poll_id,
        "created_at": p.created_at,
        "expires_at": p.created_at + POLL_TTL_SECONDS,
        "spec": p.spec,
        "counts": counts,
        "texts": texts_list,
        "total_votes": int(sum(counts.values())),
    }


def sse_broadcast(p: Poll) -> None:
    payload = json.dumps({"type": "results", "data": poll_snapshot(p)}, separators=(",", ":"))
    dead = []
    for writer in list(p.sse_clients):
        try:
            writer(payload)
        except Exception:
            dead.append(writer)
    for w in dead:
        try:
            p.sse_clients.remove(w)
        except Exception:
            pass


# -----------------------------
# Templates
# -----------------------------

_TEMPLATE_CACHE: Dict[str, str] = {}
_TEMPLATE_LOCK = threading.Lock()

def load_template(name: str) -> Optional[str]:
    """
    Loads templates/<name> safely.
    Returns None if missing (no exception).
    """
    # prevent path traversal
    if "/" in name or "\\" in name or name.startswith("."):
        return None
    path = os.path.join(TEMPLATES_DIR, name)
    try:
        with open(path, "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        return None
    except Exception:
        return None


def render_template(name: str, ctx: Dict[str, str]) -> Optional[str]:
    """
    Very small {{key}} replacer.
    Returns None if template missing.
    """
    with _TEMPLATE_LOCK:
        tpl = _TEMPLATE_CACHE.get(name)
        if tpl is None:
            tpl = load_template(name)
            if tpl is None:
                return None
            _TEMPLATE_CACHE[name] = tpl

    out = tpl
    for k, v in ctx.items():
        out = out.replace("{{" + k + "}}", v)
    return out


# -----------------------------
# Auto-expiry GC
# -----------------------------

def gc_loop(stop_event: threading.Event) -> None:
    while not stop_event.is_set():
        stop_event.wait(GC_EVERY_SECONDS)
        if stop_event.is_set():
            break
        cutoff = now() - POLL_TTL_SECONDS
        expired: List[str] = []
        with POLLS_LOCK:
            for pid, p in list(POLLS.items()):
                if p.created_at < cutoff:
                    expired.append(pid)
            for pid in expired:
                del POLLS[pid]


# -----------------------------
# HTTP Handler
# -----------------------------

class Handler(BaseHTTPRequestHandler):
    server_version = "SimpleLivePoll/0.2"

    def log_message(self, fmt: str, *args: Any) -> None:
        sys.stderr.write("%s - - [%s] %s\n" % (
            self.client_address[0],
            self.log_date_time_string(),
            fmt % args
        ))

    def do_GET(self) -> None:
        try:
            if self.path == "/" or self.path.startswith("/?"):
                return self.handle_index()

            if self.path.startswith("/static/"):
                return self.handle_static()

            if self.path.startswith("/p/"):
                return self.handle_poll_get()

            return self.send_error_page(HTTPStatus.NOT_FOUND, "Not found")
        except Exception as e:
            return self.send_error_page(HTTPStatus.INTERNAL_SERVER_ERROR, f"Server error: {html.escape(str(e))}")

    def do_POST(self) -> None:
        try:
            if self.path == "/create":
                return self.handle_create()

            if self.path.startswith("/p/"):
                return self.handle_poll_post()

            return self.send_error_json(HTTPStatus.NOT_FOUND, "Not found")
        except Exception as e:
            return self.send_error_json(HTTPStatus.INTERNAL_SERVER_ERROR, f"Server error: {e}")

    # ---------- pages ----------

    def handle_index(self) -> None:
        page = render_template("index.html", {})
        if page is None:
            # template missing -> graceful error
            return self.send_error_page(
                HTTPStatus.INTERNAL_SERVER_ERROR,
                "Missing template: templates/index.html"
            )
        self.send_html(page, set_device_cookie=True)

    def handle_create(self) -> None:
        form = read_form(self)
        spec_raw = (form.get("spec") or "").strip()
        if not spec_raw:
            return self.send_error_page(HTTPStatus.BAD_REQUEST, "Missing 'spec' field")

        try:
            spec = json.loads(spec_raw)
            validate_poll_spec(spec)
        except Exception as e:
            return self.send_error_page(HTTPStatus.BAD_REQUEST, f"Invalid poll JSON: {html.escape(str(e))}")

        poll_id = gen_id()
        p = Poll(poll_id=poll_id, created_at=now(), spec=spec)
        for opt in spec["options"]:
            p.counts[str(opt["id"])] = 0

        with POLLS_LOCK:
            POLLS[poll_id] = p

        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", f"/p/{poll_id}")
        self.end_headers()

    def handle_poll_get(self) -> None:
        parts = self.path.split("?")[0].split("/")
        if len(parts) < 3:
            return self.send_error_page(HTTPStatus.NOT_FOUND, "Not found")
        poll_id = parts[2]
        tail = parts[3:] if len(parts) > 3 else []

        p = self.get_poll_or_404(poll_id)
        if p is None:
            return

        if not tail or tail == [""]:
            return self.render_poll_page(p)

        if tail == ["results"]:
            return self.render_results_page(p)

        if tail == ["snapshot"]:
            with p.lock:
                snap = poll_snapshot(p)
            return self.send_json(snap, set_device_cookie=True)

        if tail == ["events"]:
            return self.handle_sse(p)

        if tail == ["download.json"]:
            with p.lock:
                snap = poll_snapshot(p)
            data = json.dumps(snap, ensure_ascii=False, indent=2).encode("utf-8")
            return self.send_bytes(
                data,
                content_type="application/json; charset=utf-8",
                filename=f"poll_{poll_id}_results.json",
                set_device_cookie=True,
            )

        if tail == ["download.csv"]:
            with p.lock:
                snap = poll_snapshot(p)
            csv_bytes = self.make_csv(snap).encode("utf-8")
            return self.send_bytes(
                csv_bytes,
                content_type="text/csv; charset=utf-8",
                filename=f"poll_{poll_id}_results.csv",
                set_device_cookie=True,
            )

        if tail == ["qr.png"]:
            return self.send_qr_png(p)

        return self.send_error_page(HTTPStatus.NOT_FOUND, "Not found")

    def render_poll_page(self, p: Poll) -> None:
        tpl = render_template("poll.html", {})
        if tpl is None:
            return self.send_error_page(
                HTTPStatus.INTERNAL_SERVER_ERROR,
                "Missing template: templates/poll.html"
            )

        spec = p.spec
        poll_id = p.poll_id
        q_html = spec.get("question_html", "")
        options = spec.get("options", [])
        ft = spec.get("free_text") or {}
        ft_enabled = bool(ft.get("enabled"))
        ft_prompt = ft.get("prompt_html", "Other:")
        ft_max_len = int(ft.get("max_len", 240))

        opts_html = []
        for opt in options:
            oid = html.escape(str(opt["id"]), quote=True)
            lab = str(opt.get("label_html", ""))
            opts_html.append(
                f'<label class="opt"><input type="radio" name="option" value="{oid}" />'
                f'<span class="lab">{lab}</span></label>'
            )

        ft_block = ""
        if ft_enabled:
            ft_block = (
                '<div class="box">'
                f'<div class="muted">{ft_prompt}</div>'
                f'<textarea id="freeText" maxlength="{ft_max_len}" placeholder="Type here..."></textarea>'
                '<div class="muted" id="ftCount"></div>'
                '</div>'
            )

        # QR uses a public image generator for simplicity
        poll_url_expr = "location.origin + '/p/" + poll_id + "'"

        page = tpl
        page = page.replace("{{POLL_ID}}", html.escape(poll_id))
        page = page.replace("{{QUESTION_HTML}}", q_html)
        page = page.replace("{{OPTIONS_HTML}}", "\n".join(opts_html))
        page = page.replace("{{FREE_TEXT_BLOCK}}", ft_block)
        page = page.replace("{{POLL_URL_EXPR}}", poll_url_expr)
        page = page.replace("{{EXPIRES_AT}}", str(int(p.created_at + POLL_TTL_SECONDS)))

        self.send_html(page, set_device_cookie=True)

    def render_results_page(self, p: Poll) -> None:
        tpl = render_template("results.html", {})
        if tpl is None:
            return self.send_error_page(
                HTTPStatus.INTERNAL_SERVER_ERROR,
                "Missing template: templates/results.html"
            )
        page = tpl.replace("{{POLL_ID}}", html.escape(p.poll_id))
        self.send_html(page, set_device_cookie=True)

    # ---------- API ----------

    def handle_poll_post(self) -> None:
        parts = self.path.split("?")[0].split("/")
        if len(parts) < 4:
            return self.send_error_json(HTTPStatus.NOT_FOUND, "Not found")
        poll_id = parts[2]
        action = parts[3]

        p = self.get_poll_or_404(poll_id)
        if p is None:
            return

        device_id, set_cookie = get_or_set_device_id(self)

        if action == "vote" and len(parts) == 4:
            try:
                body = parse_json_body(self, max_bytes=32_000)
            except Exception as e:
                return self.send_error_json(HTTPStatus.BAD_REQUEST, str(e), set_cookie=set_cookie)

            option_id = body.get("option_id", None)
            free_text = str(body.get("free_text", "") or "")

            one_vote = bool((p.spec.get("settings") or {}).get("one_vote_per_device", True))

            with p.lock:
                # option
                if option_id is not None:
                    option_id = str(option_id)
                    valid_ids = {str(o["id"]) for o in p.spec["options"]}
                    if option_id not in valid_ids:
                        return self.send_error_json(HTTPStatus.BAD_REQUEST, "Invalid option_id", set_cookie=set_cookie)

                    if one_vote:
                        prev = p.device_votes.get(device_id)
                        if prev is not None and prev in p.counts:
                            p.counts[prev] = max(0, int(p.counts.get(prev, 0)) - 1)
                        p.device_votes[device_id] = option_id
                        p.counts[option_id] = int(p.counts.get(option_id, 0)) + 1
                    else:
                        p.counts[option_id] = int(p.counts.get(option_id, 0)) + 1

                # free text
                ft = p.spec.get("free_text") or {}
                if bool(ft.get("enabled")):
                    max_len = int(ft.get("max_len", 240))
                    txt = free_text.strip()
                    if txt:
                        txt = txt[:max_len]
                        safe = escape_student_text(txt)
                        tid = gen_id(6)
                        p.texts[tid] = {"text": safe, "count": 0, "created_at": now()}

                sse_broadcast(p)

            return self.send_json({"ok": True}, set_cookie=set_cookie)

        if action == "text" and len(parts) == 6 and parts[5] == "upvote":
            text_id = parts[4]
            ft = p.spec.get("free_text") or {}
            if not bool(ft.get("enabled")):
                return self.send_error_json(HTTPStatus.BAD_REQUEST, "Free text disabled", set_cookie=set_cookie)
            if not bool(ft.get("allow_upvotes")):
                return self.send_error_json(HTTPStatus.BAD_REQUEST, "Upvotes disabled", set_cookie=set_cookie)

            with p.lock:
                if text_id not in p.texts:
                    return self.send_error_json(HTTPStatus.NOT_FOUND, "Text not found", set_cookie=set_cookie)

                voted = p.device_upvotes.setdefault(device_id, set())
                if text_id in voted:
                    return self.send_error_json(HTTPStatus.CONFLICT, "Already upvoted", set_cookie=set_cookie)

                voted.add(text_id)
                p.texts[text_id]["count"] = int(p.texts[text_id].get("count", 0)) + 1

                sse_broadcast(p)

            return self.send_json({"ok": True}, set_cookie=set_cookie)

        return self.send_error_json(HTTPStatus.NOT_FOUND, "Not found", set_cookie=set_cookie)

    def handle_sse(self, p: Poll) -> None:
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", "text/event-stream; charset=utf-8")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.send_header("Access-Control-Allow-Origin", "*")

        _, set_cookie = get_or_set_device_id(self)
        if set_cookie:
            self.send_header("Set-Cookie", set_cookie)

        self.end_headers()

        wlock = threading.Lock()

        def writer(payload: str) -> None:
            with wlock:
                msg = f"data: {payload}\n\n".encode("utf-8")
                self.wfile.write(msg)
                self.wfile.flush()

        with p.lock:
            p.sse_clients.append(writer)
            try:
                writer(json.dumps({"type": "results", "data": poll_snapshot(p)}, separators=(",", ":")))
            except Exception:
                try:
                    p.sse_clients.remove(writer)
                except Exception:
                    pass
                return

        try:
            while True:
                time.sleep(15)
                with wlock:
                    self.wfile.write(b": ping\n\n")
                    self.wfile.flush()
        except Exception:
            with p.lock:
                try:
                    p.sse_clients.remove(writer)
                except Exception:
                    pass

    # ---------- static files ----------

    def handle_static(self) -> None:
        # Serve files under ./static safely, with proper 404 on missing.
        rel = self.path.split("?", 1)[0][len("/static/"):]
        rel = rel.lstrip("/")

        # prevent traversal
        if not rel or ".." in rel or rel.startswith(".") or "\\" in rel:
            return self.send_error_page(HTTPStatus.NOT_FOUND, "Not found")

        path = os.path.join(STATIC_DIR, rel)
        if not os.path.isfile(path):
            return self.send_error_page(HTTPStatus.NOT_FOUND, "Not found")

        # minimal content-type mapping
        ctype = "application/octet-stream"
        if path.endswith(".css"):
            ctype = "text/css; charset=utf-8"
        elif path.endswith(".js"):
            ctype = "application/javascript; charset=utf-8"
        elif path.endswith(".png"):
            ctype = "image/png"
        elif path.endswith(".jpg") or path.endswith(".jpeg"):
            ctype = "image/jpeg"
        elif path.endswith(".svg"):
            ctype = "image/svg+xml; charset=utf-8"

        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception:
            return self.send_error_page(HTTPStatus.INTERNAL_SERVER_ERROR, "Failed to read static file")

        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    # ---------- misc ----------

    def get_poll_or_404(self, poll_id: str) -> Optional[Poll]:
        # auto-expiry check on access too (nice behavior)
        with POLLS_LOCK:
            p = POLLS.get(poll_id)
            if not p:
                self.send_error_page(HTTPStatus.NOT_FOUND, "Poll not found")
                return None
            if p.created_at + POLL_TTL_SECONDS < now():
                del POLLS[poll_id]
                self.send_error_page(HTTPStatus.NOT_FOUND, "Poll expired")
                return None
        return p

    def send_html(self, content: str, *, set_device_cookie: bool = False) -> None:
        data = content.encode("utf-8")
        _, set_cookie = get_or_set_device_id(self) if set_device_cookie else ("", None)
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        if set_cookie:
            self.send_header("Set-Cookie", set_cookie)
        self.end_headers()
        self.wfile.write(data)

    def send_json(self, obj: Any, *, set_cookie: Optional[str] = None, set_device_cookie: bool = False) -> None:
        data = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        if set_device_cookie and set_cookie is None:
            _, set_cookie = get_or_set_device_id(self)
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        if set_cookie:
            self.send_header("Set-Cookie", set_cookie)
        self.end_headers()
        self.wfile.write(data)

    def send_qr_png(self, p: Poll) -> None:
        # Build absolute poll URL from request headers
        host = self.headers.get("Host", "")
        if not host:
            return self.send_error_page(HTTPStatus.BAD_REQUEST, "Missing Host header")

        poll_url = f"http://{host}/p/{urllib.parse.quote(p.poll_id)}"

        qr = qrcode.QRCode(
            version=None,
            error_correction=qrcode.constants.ERROR_CORRECT_M,
            box_size=8,
            border=2,
        )
        qr.add_data(poll_url)
        qr.make(fit=True)
        img = qr.make_image(fill_color="black", back_color="white")

        buf = BytesIO()
        img.save(buf, format="PNG")
        data = buf.getvalue()

        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", "image/png")
        self.send_header("Content-Length", str(len(data)))
        # Avoid caching stale QR across polls if you restart
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def send_bytes(self, data: bytes, *, content_type: str, filename: Optional[str] = None, set_device_cookie: bool = False) -> None:
        _, set_cookie = get_or_set_device_id(self) if set_device_cookie else ("", None)
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        if filename:
            self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
        if set_cookie:
            self.send_header("Set-Cookie", set_cookie)
        self.end_headers()
        self.wfile.write(data)

    def send_error_json(self, status: HTTPStatus, msg: str, *, set_cookie: Optional[str] = None) -> None:
        payload = json.dumps({"error": msg}, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        if set_cookie:
            self.send_header("Set-Cookie", set_cookie)
        self.end_headers()
        self.wfile.write(payload)

    def send_error_page(self, status: HTTPStatus, message: str) -> None:
        tpl = render_template("error.html", {})
        if tpl is None:
            # last-resort fallback (still no exception)
            body = f"<h1>{status.value} {html.escape(status.phrase)}</h1><p>{html.escape(message)}</p>"
        else:
            body = tpl.replace("{{STATUS}}", str(status.value)).replace("{{MESSAGE}}", html.escape(message))

        data = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def make_csv(self, snap: Dict[str, Any]) -> str:
        out = io.StringIO()
        w = csv.writer(out)

        w.writerow(["poll_id", snap.get("poll_id", "")])
        w.writerow(["created_at_unix", snap.get("created_at", 0)])
        w.writerow(["expires_at_unix", snap.get("expires_at", 0)])
        w.writerow([])

        w.writerow(["Option counts"])
        w.writerow(["option_id", "label_text", "count"])
        opts = snap.get("spec", {}).get("options", []) or []
        counts = snap.get("counts", {}) or {}
        for opt in opts:
            oid = opt.get("id", "")
            label = (opt.get("label_html", "") or "")
            label_text = re.sub(r"<[^>]*>", "", label).strip()
            w.writerow([oid, label_text, counts.get(oid, 0)])

        w.writerow([])
        w.writerow(["Free text"])
        w.writerow(["text_id", "text", "upvotes", "created_at_unix"])
        for t in (snap.get("texts", []) or []):
            w.writerow([t.get("id", ""), t.get("text", ""), t.get("upvotes", 0), t.get("created_at", 0)])

        return out.getvalue()


# -----------------------------
# Main
# -----------------------------

def main() -> None:
    global POLL_TTL_SECONDS, GC_EVERY_SECONDS

    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--ttl-hours", type=float, default=24.0, help="Poll expiry TTL in hours (default: 24)")
    ap.add_argument("--gc-seconds", type=int, default=60, help="Expiry GC interval seconds (default: 60)")
    args = ap.parse_args()

    POLL_TTL_SECONDS = max(60, int(args.ttl_hours * 3600))
    GC_EVERY_SECONDS = max(5, int(args.gc_seconds))

    stop_event = threading.Event()
    t = threading.Thread(target=gc_loop, args=(stop_event,), daemon=True)
    t.start()

    httpd = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"Serving on http://{args.host}:{args.port}")
    print(f"Poll TTL: {POLL_TTL_SECONDS} seconds; GC every {GC_EVERY_SECONDS} seconds")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down...")
    finally:
        stop_event.set()


if __name__ == "__main__":
    main()


#!/usr/bin/env python3
"""
Small stdlib-only HTTP wrapper for `sql_process`.

GET  /      serves a demo page.
POST /      accepts the JSON payload expected by LeanDatabase.Parser.checkEquiv
            and returns the JSON line produced by `sql_process`.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import queue
import subprocess
import sys
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any


PORT = 6767
REQUEST_TIMEOUT_SECONDS = 300.0
MAX_BODY_BYTES = 1_000_000


class SqlProcess:
    def __init__(
        self,
        repo_dir: Path,
        timeout: float = REQUEST_TIMEOUT_SECONDS,
        warmup: bool = True,
    ) -> None:
        self.repo_dir = repo_dir
        self.timeout = timeout
        self.warmup = warmup
        self.lock = threading.Lock()
        self.ready = threading.Event()
        self.stderr_lines: "queue.Queue[str]" = queue.Queue(maxsize=200)
        self.responses: "queue.Queue[Any]" = queue.Queue()
        self.proc: subprocess.Popen[str] | None = None
        self.start()

    def start(self) -> None:
        self.ready.clear()
        self._clear_responses()
        command = self._process_command()
        print(f"Starting {' '.join(command)}", file=sys.stderr, flush=True)
        self.proc = subprocess.Popen(
            command,
            cwd=self.repo_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,
        )
        threading.Thread(target=self._drain_stderr, daemon=True).start()
        threading.Thread(target=self._drain_stdout, daemon=True).start()

    def stop(self) -> None:
        proc = self.proc
        if proc is not None and proc.poll() is None:
            proc.terminate()

    def _process_command(self) -> list[str]:
        # `sql_process`'s native exe can't be linked on Windows with `supportInterpreter`
        # enabled (the PE format's 65535-exported-symbol limit, blown past by Mathlib),
        # but without it, `sql_process` fails at runtime on `IO.getRandomBytes` (no native
        # implementation without the interpreter fallback). Running the source file
        # through the interpreter sidesteps both problems: imports (Mathlib, LeanDatabase)
        # are still loaded from pre-built `.olean`s, only `sql_process.lean` itself is
        # interpreted, so startup is not meaningfully slower than the native exe.
        return ["lake", "env", "lean", "--run", "sql_process.lean"]
        return False

    def wait_until_ready(self) -> None:
        deadline = time.monotonic() + self.timeout
        next_notice = time.monotonic()
        while not self.ready.is_set():
            proc = self.proc
            if proc is not None and proc.poll() is not None:
                raise RuntimeError(
                    f"sql_process exited before readiness with code {proc.returncode}"
                )
            now = time.monotonic()
            if now >= deadline:
                raise TimeoutError(
                    "timed out waiting for sql_process readiness on stderr"
                )
            if now >= next_notice:
                print(
                    "Waiting for sql_process readiness...",
                    file=sys.stderr,
                    flush=True,
                )
                next_notice = now + 10.0
            self.ready.wait(timeout=min(1.0, deadline - now))
        print("sql_process is ready", file=sys.stderr, flush=True)

    def warm_up(self, payload: Any) -> None:
        started = time.monotonic()
        print(
            "Warming sql_process with a sample equivalence check...",
            file=sys.stderr,
            flush=True,
        )
        response = self.request(payload)
        elapsed = time.monotonic() - started
        if not (
            isinstance(response, dict)
            and response.get("status") == "ok"
            and response.get("equivalent") is True
        ):
            raise RuntimeError(f"sql_process warmup failed: {response!r}")
        print(
            f"sql_process warmup completed in {elapsed:.3f}s",
            file=sys.stderr,
            flush=True,
        )

    def _clear_responses(self) -> None:
        while True:
            try:
                self.responses.get_nowait()
            except queue.Empty:
                return

    def _drain_stderr(self) -> None:
        proc = self.proc
        if proc is None or proc.stderr is None:
            return
        for line in proc.stderr:
            line = line.rstrip("\n")
            print(f"[sql_process] {line}", file=sys.stderr, flush=True)
            if "Ready to process equivalence checks." in line:
                self.ready.set()
            try:
                self.stderr_lines.put_nowait(line)
            except queue.Full:
                try:
                    self.stderr_lines.get_nowait()
                except queue.Empty:
                    pass
                self.stderr_lines.put_nowait(line)

    def _drain_stdout(self) -> None:
        proc = self.proc
        if proc is None or proc.stdout is None:
            return
        for raw_line in proc.stdout:
            line = raw_line.rstrip("\n")
            stripped = line.strip()
            if not stripped:
                continue
            try:
                parsed = json.loads(stripped)
            except json.JSONDecodeError:
                print(f"[sql_process] {line}", file=sys.stderr, flush=True)
                continue
            if isinstance(parsed, dict) and parsed.get("status") in {"ok", "error"}:
                self.responses.put(parsed)
            else:
                print(f"[sql_process] {line}", file=sys.stderr, flush=True)

    def recent_stderr(self) -> list[str]:
        return list(self.stderr_lines.queue)

    def request(self, payload: Any) -> Any:
        encoded = json.dumps(payload, separators=(",", ":"))
        with self.lock:
            proc = self.proc
            if (
                proc is None
                or proc.poll() is not None
                or proc.stdin is None
                or proc.stdout is None
            ):
                self.start()
                proc = self.proc
                if proc is None or proc.stdin is None or proc.stdout is None:
                    raise RuntimeError("failed to start sql_process")

            if not self.ready.wait(timeout=self.timeout):
                raise TimeoutError(
                    "timed out waiting for sql_process readiness on stderr"
                )

            proc.stdin.write(encoded + "\n")
            proc.stdin.flush()

            deadline = time.monotonic() + self.timeout
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise TimeoutError("timed out waiting for sql_process")
                if proc.poll() is not None:
                    raise RuntimeError(
                        f"sql_process exited unexpectedly with code {proc.returncode}"
                    )
                try:
                    return self.responses.get(timeout=min(0.2, remaining))
                except queue.Empty:
                    continue


class Handler(BaseHTTPRequestHandler):
    server_version = "LeanDatabaseSqlServer/0.1"

    def do_OPTIONS(self) -> None:
        self.send_response(HTTPStatus.NO_CONTENT)
        self._cors_headers()
        self.end_headers()

    def do_GET(self) -> None:
        if self.path not in ("/", "/index.html"):
            self._send_json({"status": "error", "message": "Not found"}, HTTPStatus.NOT_FOUND)
            return
        body = demo_html().encode("utf-8")
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self) -> None:
        length_header = self.headers.get("Content-Length")
        if length_header is None:
            self._send_json(
                {"status": "error", "message": "Missing Content-Length"},
                HTTPStatus.LENGTH_REQUIRED,
            )
            return
        try:
            length = int(length_header)
        except ValueError:
            self._send_json(
                {"status": "error", "message": "Invalid Content-Length"},
                HTTPStatus.BAD_REQUEST,
            )
            return
        if length > MAX_BODY_BYTES:
            self._send_json(
                {"status": "error", "message": "Request body too large"},
                HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
            )
            return

        raw = self.rfile.read(length)
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            self._send_json(
                {"status": "error", "message": f"Invalid JSON: {exc}"},
                HTTPStatus.BAD_REQUEST,
            )
            return

        try:
            response = self.server.sql_process.request(payload)  # type: ignore[attr-defined]
        except Exception as exc:
            self._send_json(
                {
                    "status": "error",
                    "message": str(exc),
                    "recentStderr": self.server.sql_process.recent_stderr()[-20:],  # type: ignore[attr-defined]
                },
                HTTPStatus.BAD_GATEWAY,
            )
            return
        self._send_json(response, HTTPStatus.OK)

    def _cors_headers(self) -> None:
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")

    def _send_json(self, payload: Any, status: HTTPStatus) -> None:
        body = json.dumps(payload, indent=2).encode("utf-8")
        self.send_response(status)
        self._cors_headers()
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, format: str, *args: Any) -> None:
        print(
            f"{self.address_string()} - {self.log_date_time_string()} - {format % args}",
            file=sys.stderr,
        )


class SqlServer(ThreadingHTTPServer):
    sql_process: SqlProcess


DEFAULT_DEMO = {
    "schemas": [
        {
            "name": "table",
            "columns": [
                {"name": "age", "type": "Int"},
                {"name": "isActive", "type": "Bool"},
            ],
        }
    ],
    "queries": [
        "SELECT * FROM table WHERE age > 30 && isActive",
        "SELECT * FROM table WHERE age > 30 && isActive && age > 20",
    ],
}


TABLE_AGE_ACTIVE_HEIGHT = {
    "name": "table",
    "columns": [
        {"name": "age", "type": "Int"},
        {"name": "isActive", "type": "Bool"},
        {"name": "height", "type": "Float"},
    ],
}


EXAMPLE_GROUPS = [
    {
        "label": "Example0",
        "examples": [
            {
                "label": "Example0: AND reorder",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE age > 30 AND isActive",
                    "SELECT * FROM table WHERE isActive AND age > 30",
                ],
            },
            {
                "label": "Example0: AND idempotent",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE isActive AND isActive",
                    "SELECT * FROM table WHERE isActive",
                ],
            },
            {
                "label": "Example0: comparison reorder",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE age > 30 AND height < 180",
                    "SELECT * FROM table WHERE height < 180 AND age > 30",
                ],
            },
            {
                "label": "Example0: double negation",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE NOT (NOT isActive)",
                    "SELECT * FROM table WHERE isActive",
                ],
            },
            {
                "label": "Example0: De Morgan",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE NOT (age > 30 OR isActive)",
                    "SELECT * FROM table WHERE NOT (age > 30) AND NOT isActive",
                ],
            },
            {
                "label": "Example0: OR idempotent",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE isActive OR isActive",
                    "SELECT * FROM table WHERE isActive",
                ],
            },
            {
                "label": "Example0: repeated comparison",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE age > 30 AND age > 30",
                    "SELECT * FROM table WHERE age > 30",
                ],
            },
            {
                "label": "Example0: absorption",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE isActive OR (isActive AND age > 30)",
                    "SELECT * FROM table WHERE isActive",
                ],
            },
            {
                "label": "Example0: OR reorder",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE isActive OR age > 30",
                    "SELECT * FROM table WHERE age > 30 OR isActive",
                ],
            },
            {
                "label": "Example0: AND distributes over OR",
                "schemas": [TABLE_AGE_ACTIVE_HEIGHT],
                "queries": [
                    "SELECT * FROM table WHERE age > 30 AND (isActive OR height < 180)",
                    "SELECT * FROM table WHERE (age > 30 AND isActive) OR (age > 30 AND height < 180)",
                ],
            },
        ],
    },
    {
        "label": "Other examples",
        "examples": [
            {
                "label": "Example1: predicate pushdown through UNION",
                "schemas": [
                    {
                        "name": "r1",
                        "columns": [
                            {"name": "is_high_value", "type": "Bool"},
                            {"name": "val", "type": "Int"},
                        ],
                    },
                    {
                        "name": "r2",
                        "columns": [
                            {"name": "is_high_value", "type": "Bool"},
                            {"name": "val", "type": "Int"},
                        ],
                    },
                ],
                "queries": [
                    "SELECT * FROM (SELECT * FROM r1 UNION SELECT * FROM r2) AS u WHERE is_high_value",
                    "SELECT * FROM r1 WHERE r1.is_high_value UNION SELECT * FROM r2 WHERE r2.is_high_value",
                ],
            },
            {
                "label": "Example2: cascading selection",
                "schemas": [
                    {
                        "name": "table",
                        "columns": [
                            {"name": "is_active", "type": "Bool"},
                            {"name": "is_high_value", "type": "Bool"},
                        ],
                    }
                ],
                "queries": [
                    "SELECT * FROM (SELECT * FROM table WHERE is_active) AS r WHERE is_high_value",
                    "SELECT * FROM table WHERE is_high_value AND is_active",
                ],
            },
            {
                "label": "Example4: combined anti-set",
                "schemas": [
                    {
                        "name": "tableA",
                        "columns": [
                            {"name": "is_active", "type": "Bool"},
                            {"name": "is_banned", "type": "Bool"},
                        ],
                    },
                    {
                        "name": "tableB",
                        "columns": [
                            {"name": "is_active", "type": "Bool"},
                            {"name": "is_banned", "type": "Bool"},
                        ],
                    },
                ],
                "queries": [
                    "(SELECT * FROM tableA WHERE tableA.is_active UNION SELECT * FROM tableB WHERE tableB.is_active) EXCEPT SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB) AS u WHERE is_banned",
                    "SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB) AS u WHERE is_active AND NOT is_banned",
                ],
            },
            {
                "label": "Example5: EXISTS equals IN",
                "schemas": [
                    {
                        "name": "customers",
                        "columns": [
                            {"name": "customer_id", "type": "Int"},
                            {"name": "name", "type": "String"},
                        ],
                    },
                    {
                        "name": "orders",
                        "columns": [
                            {"name": "customer_id", "type": "Int"},
                            {"name": "total", "type": "Int"},
                        ],
                    },
                ],
                "queries": [
                    "SELECT * FROM customers WHERE EXISTS (SELECT * FROM orders WHERE orders.customer_id = customers.customer_id)",
                    "SELECT * FROM customers WHERE customers.customer_id IN (SELECT orders.customer_id FROM orders)",
                ],
            },
            {
                "label": "Example8: NOT IN equals NOT EXISTS",
                "schemas": [
                    {
                        "name": "customers",
                        "columns": [
                            {"name": "customer_id", "type": "Int"},
                            {"name": "name", "type": "String"},
                        ],
                    },
                    {
                        "name": "orders",
                        "columns": [
                            {"name": "customer_id", "type": "Int"},
                            {"name": "total", "type": "Int"},
                        ],
                    },
                ],
                "queries": [
                    "SELECT * FROM customers WHERE customers.customer_id NOT IN (SELECT orders.customer_id FROM orders)",
                    "SELECT * FROM customers WHERE NOT EXISTS (SELECT * FROM orders WHERE orders.customer_id = customers.customer_id)",
                ],
            },
            {
                "label": "Example10: OR equals UNION",
                "schemas": [
                    {
                        "name": "table",
                        "columns": [
                            {"name": "status", "type": "String"},
                            {"name": "priority", "type": "String"},
                        ],
                    }
                ],
                "queries": [
                    'SELECT * FROM table WHERE status = "open" OR priority = "high"',
                    'SELECT * FROM table WHERE status = "open" UNION SELECT * FROM table WHERE priority = "high"',
                ],
            },
            {
                "label": "Example10: OR equals disjoint UNION ALL",
                "schemas": [
                    {
                        "name": "table",
                        "columns": [
                            {"name": "status", "type": "String"},
                            {"name": "priority", "type": "String"},
                        ],
                    }
                ],
                "queries": [
                    'SELECT * FROM table WHERE status = "open" OR priority = "high"',
                    'SELECT * FROM table WHERE status = "open" UNION ALL SELECT * FROM table WHERE priority = "high" AND status <> "open"',
                ],
            },
            {
                "label": "Example13: UNION absorption",
                "schemas": [
                    {
                        "name": "table",
                        "columns": [
                            {"name": "age", "type": "Int"},
                            {"name": "isActive", "type": "Bool"},
                        ],
                    },
                    {
                        "name": "table2",
                        "columns": [
                            {"name": "age", "type": "Int"},
                            {"name": "isActive", "type": "Bool"},
                        ],
                    },
                ],
                "queries": [
                    "SELECT * FROM table UNION (SELECT * FROM table INTERSECT SELECT * FROM table2)",
                    "SELECT * FROM table",
                ],
            },
            {
                "label": "Example16: DISTINCT and cascading WHERE",
                "schemas": [
                    {
                        "name": "R",
                        "columns": [
                            {"name": "a", "type": "Int"},
                            {"name": "b", "type": "Int"},
                            {"name": "p", "type": "Bool"},
                            {"name": "q", "type": "Bool"},
                        ],
                    }
                ],
                "queries": [
                    "SELECT DISTINCT a + b AS g FROM (SELECT * FROM (SELECT * FROM R WHERE q) AS x WHERE p) AS y",
                    "SELECT a + b AS g FROM R WHERE p AND q",
                ],
            },
            {
                "label": "Example18: LIKE, ORDER BY, LIMIT",
                "schemas": [
                    {
                        "name": "table",
                        "columns": [
                            {"name": "name", "type": "String"},
                            {"name": "age", "type": "Int"},
                        ],
                    }
                ],
                "queries": [
                    'SELECT * FROM table WHERE name LIKE "%" ORDER BY age LIMIT 10',
                    "SELECT * FROM table",
                ],
            },
        ],
    },
]


def demo_html() -> str:
    initial = DEFAULT_DEMO
    initial_json = html.escape(json.dumps(initial, indent=2))
    examples_json = json.dumps(EXAMPLE_GROUPS)
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>LeanDatabase SQL Equivalence</title>
  <style>
    :root {{
      color-scheme: light dark;
      --bg: #f7f7f4;
      --panel: #ffffff;
      --text: #1d2428;
      --muted: #5f6b72;
      --line: #d8ddd8;
      --accent: #16615d;
      --accent-2: #2f6f31;
      --danger: #9e2f2f;
      --code: #eef3f1;
      font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
    }}
    @media (prefers-color-scheme: dark) {{
      :root {{
        --bg: #171b1c;
        --panel: #202627;
        --text: #edf1ef;
        --muted: #a7b1ad;
        --line: #384244;
        --accent: #6fb7aa;
        --accent-2: #8fc77f;
        --danger: #ef8f8f;
        --code: #141819;
      }}
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      background: var(--bg);
      color: var(--text);
      font-size: 15px;
      line-height: 1.45;
    }}
    header {{
      padding: 24px clamp(16px, 4vw, 48px) 14px;
      border-bottom: 1px solid var(--line);
      background: var(--panel);
    }}
    h1 {{
      margin: 0 0 4px;
      font-size: clamp(24px, 3vw, 36px);
      font-weight: 700;
      letter-spacing: 0;
    }}
    header p {{
      margin: 0;
      color: var(--muted);
      max-width: 760px;
    }}
    main {{
      display: grid;
      grid-template-columns: minmax(320px, 0.95fr) minmax(360px, 1.05fr);
      gap: 18px;
      padding: 18px clamp(16px, 4vw, 48px) 32px;
    }}
    section {{
      min-width: 0;
    }}
    .panel {{
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 16px;
    }}
    h2 {{
      margin: 0 0 12px;
      font-size: 16px;
      font-weight: 700;
      letter-spacing: 0;
    }}
    label {{
      display: block;
      margin: 12px 0 6px;
      font-weight: 650;
      color: var(--text);
    }}
    textarea, input, select {{
      width: 100%;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--panel);
      color: var(--text);
      font: inherit;
    }}
    textarea {{
      min-height: 104px;
      resize: vertical;
      padding: 10px 11px;
      font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      font-size: 13px;
      line-height: 1.5;
    }}
    input, select {{
      height: 38px;
      padding: 0 9px;
    }}
    .schema-card {{
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 12px;
      margin: 10px 0;
    }}
    .schema-title {{
      display: grid;
      grid-template-columns: minmax(120px, 1fr) 36px;
      gap: 8px;
      align-items: center;
      margin-bottom: 10px;
    }}
    .schema-head, .schema-row {{
      display: grid;
      grid-template-columns: minmax(92px, 1fr) 110px 36px;
      gap: 8px;
      align-items: center;
    }}
    .schema-head {{
      color: var(--muted);
      font-size: 12px;
      font-weight: 700;
      margin: 2px 0 6px;
    }}
    .schema-row {{ margin-bottom: 8px; }}
    .example-grid {{
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 8px;
      margin-bottom: 12px;
    }}
    button {{
      min-height: 38px;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--panel);
      color: var(--text);
      cursor: pointer;
      font: inherit;
      font-weight: 700;
      padding: 0 12px;
    }}
    button:hover {{ border-color: var(--accent); }}
    .primary {{
      background: var(--accent);
      border-color: var(--accent);
      color: #fff;
    }}
    .danger {{
      color: var(--danger);
      padding: 0;
      width: 36px;
    }}
    .actions {{
      display: flex;
      flex-wrap: wrap;
      gap: 8px;
      margin-top: 14px;
    }}
    .examples {{
      display: flex;
      flex-wrap: wrap;
      gap: 8px;
      margin: 8px 0 0;
    }}
    .examples button {{
      min-height: 32px;
      font-size: 13px;
      font-weight: 650;
    }}
    pre {{
      margin: 0;
      white-space: pre-wrap;
      overflow-wrap: anywhere;
      background: var(--code);
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 12px;
      min-height: 148px;
      font: 13px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    }}
    .status {{
      margin: 10px 0 0;
      color: var(--muted);
      min-height: 22px;
    }}
    .result-ok {{ color: var(--accent-2); font-weight: 700; }}
    .result-error {{ color: var(--danger); font-weight: 700; }}
    .stack {{
      display: grid;
      gap: 14px;
    }}
    @media (max-width: 880px) {{
      main {{ grid-template-columns: 1fr; }}
      .example-grid {{ grid-template-columns: 1fr; }}
    }}
  </style>
</head>
<body>
  <header>
    <h1>LeanDatabase SQL Equivalence</h1>
    <p>Build named schemas and SQL query pairs, then send the generated JSON to the Lean <code>sql_equiv</code>-backed checker.</p>
  </header>
  <main>
    <section class="panel">
      <h2>Query Pair</h2>
      <div class="example-grid">
        <div>
          <label for="example0Menu">Example0</label>
          <select id="example0Menu"></select>
        </div>
        <div>
          <label for="otherExampleMenu">Other examples</label>
          <select id="otherExampleMenu"></select>
        </div>
      </div>
      <div id="schemas"></div>
      <button type="button" id="addSchema">+ Table</button>

      <label for="first">First query</label>
      <textarea id="first" spellcheck="false"></textarea>

      <label for="second">Second query</label>
      <textarea id="second" spellcheck="false"></textarea>

      <div class="actions">
        <button class="primary" type="button" id="check">Check equivalence</button>
        <button type="button" id="reset">Reset</button>
      </div>
      <div id="status" class="status"></div>
    </section>

    <section class="stack">
      <div class="panel">
        <h2>JSON Sent</h2>
        <pre id="requestJson">{initial_json}</pre>
      </div>
      <div class="panel">
        <h2>JSON Received</h2>
        <pre id="responseJson">No request sent yet.</pre>
      </div>
    </section>
  </main>

  <script>
    const initial = {json.dumps(initial)};
    const exampleGroups = {examples_json};

    const schemasEl = document.querySelector("#schemas");
    const first = document.querySelector("#first");
    const second = document.querySelector("#second");
    const requestJson = document.querySelector("#requestJson");
    const responseJson = document.querySelector("#responseJson");
    const statusLine = document.querySelector("#status");

    function addSchema(schema = {{ name: "", columns: [] }}) {{
      const card = document.createElement("div");
      card.className = "schema-card";
      card.innerHTML = `
        <div class="schema-title">
          <input aria-label="Table name" class="schema-name" value="${{escapeAttr(schema.name || "")}}" placeholder="table">
          <button type="button" class="danger remove-schema" title="Remove table">x</button>
        </div>
        <div class="schema-head"><span>Column</span><span>Type</span><span></span></div>
        <div class="schema-rows"></div>
        <button type="button" class="add-column">+ Column</button>
      `;
      const rows = card.querySelector(".schema-rows");
      card.querySelector(".schema-name").addEventListener("input", updateRequest);
      card.querySelector(".remove-schema").addEventListener("click", () => {{
        card.remove();
        updateRequest();
      }});
      card.querySelector(".add-column").addEventListener("click", () => {{
        addRow(rows);
        updateRequest();
      }});
      (schema.columns || []).forEach(col => addRow(rows, col.name, col.type));
      schemasEl.appendChild(card);
    }}

    function addRow(rows, name = "", type = "Int") {{
      const row = document.createElement("div");
      row.className = "schema-row";
      row.innerHTML = `
        <input aria-label="Column name" class="col-name" value="${{escapeAttr(name)}}" placeholder="age">
        <select aria-label="Column type" class="col-type">
          <option>Int</option>
          <option>Bool</option>
          <option>String</option>
          <option>Float</option>
          <option>varchar</option>
          <option>text</option>
        </select>
        <button type="button" class="danger" title="Remove column">x</button>
      `;
      row.querySelector(".col-type").value = type;
      row.querySelector(".danger").addEventListener("click", () => {{
        row.remove();
        updateRequest();
      }});
      row.querySelectorAll("input, select").forEach(el => el.addEventListener("input", updateRequest));
      rows.appendChild(row);
    }}

    function escapeAttr(value) {{
      return String(value).replaceAll("&", "&amp;").replaceAll('"', "&quot;").replaceAll("<", "&lt;");
    }}

    function currentPayload() {{
      return {{
        schemas: [...schemasEl.querySelectorAll(".schema-card")].map(card => ({{
          name: card.querySelector(".schema-name").value.trim(),
          columns: [...card.querySelectorAll(".schema-row")].map(row => ({{
            name: row.querySelector(".col-name").value.trim(),
            type: row.querySelector(".col-type").value.trim()
          }})).filter(col => col.name && col.type)
        }})).filter(schema => schema.name && schema.columns.length),
        queries: [first.value, second.value]
      }};
    }}

    function updateRequest() {{
      requestJson.textContent = JSON.stringify(currentPayload(), null, 2);
    }}

    function loadPayload(payload) {{
      schemasEl.replaceChildren();
      (payload.schemas || []).forEach(addSchema);
      first.value = (payload.queries && payload.queries[0]) || "";
      second.value = (payload.queries && payload.queries[1]) || "";
      responseJson.textContent = "No request sent yet.";
      statusLine.textContent = "";
      updateRequest();
    }}

    function reset() {{
      loadPayload(initial);
    }}

    async function check() {{
      const payload = currentPayload();
      requestJson.textContent = JSON.stringify(payload, null, 2);
      responseJson.textContent = "Waiting for Lean...";
      statusLine.textContent = "Running equivalence check.";
      try {{
        const res = await fetch("/", {{
          method: "POST",
          headers: {{ "Content-Type": "application/json" }},
          body: JSON.stringify(payload)
        }});
        const text = await res.text();
        let data;
        try {{
          data = JSON.parse(text);
          responseJson.textContent = JSON.stringify(data, null, 2);
        }} catch {{
          responseJson.textContent = text;
          throw new Error(`HTTP ${{res.status}} returned non-JSON`);
        }}
        if (!res.ok || data.status === "error") {{
          statusLine.innerHTML = `<span class="result-error">Error:</span> ${{data.message || res.statusText}}`;
        }} else {{
          statusLine.innerHTML = data.equivalent
            ? `<span class="result-ok">Equivalent.</span>`
            : `<span class="result-error">Could not prove equivalent.</span>`;
        }}
      }} catch (err) {{
        statusLine.innerHTML = `<span class="result-error">Request failed:</span> ${{err.message}}`;
      }}
    }}

    document.querySelector("#addSchema").addEventListener("click", () => {{
      addSchema({{ name: "table" + (schemasEl.children.length + 1), columns: [] }});
      updateRequest();
    }});
    document.querySelector("#check").addEventListener("click", check);
    document.querySelector("#reset").addEventListener("click", reset);
    first.addEventListener("input", updateRequest);
    second.addEventListener("input", updateRequest);

    function fillMenu(selector, groupIndex) {{
      const menu = document.querySelector(selector);
      menu.append(new Option("Choose example...", ""));
      exampleGroups[groupIndex].examples.forEach((example, index) => {{
        menu.append(new Option(example.label, String(index)));
      }});
      menu.addEventListener("change", () => {{
        if (!menu.value) return;
        loadPayload(exampleGroups[groupIndex].examples[Number(menu.value)]);
        document.querySelector(groupIndex === 0 ? "#otherExampleMenu" : "#example0Menu").value = "";
      }});
    }}

    fillMenu("#example0Menu", 0);
    fillMenu("#otherExampleMenu", 1);
    reset();
  </script>
</body>
</html>"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", default=PORT, type=int)
    parser.add_argument("--timeout", default=REQUEST_TIMEOUT_SECONDS, type=float)
    parser.add_argument(
        "--no-warmup",
        action="store_true",
        help="skip the startup sample check that warms Lean's first-query path",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_dir = Path(__file__).resolve().parent
    os.chdir(repo_dir)

    server: SqlServer | None = None
    sql_process: SqlProcess | None = None
    try:
        sql_process = SqlProcess(
            repo_dir,
            timeout=args.timeout,
            warmup=not args.no_warmup,
        )
        sql_process.wait_until_ready()
        if sql_process.warmup:
            sql_process.warm_up(DEFAULT_DEMO)
        server = SqlServer((args.host, args.port), Handler)
        server.sql_process = sql_process
        print(f"Serving on http://{args.host}:{args.port}", file=sys.stderr, flush=True)
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        if server is not None:
            server.server_close()
        if sql_process is not None:
            sql_process.stop()


if __name__ == "__main__":
    main()

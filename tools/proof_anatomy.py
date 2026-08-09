#!/usr/bin/env -S uv run
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Serve the root-proof anatomy viewer against a real proof file.

Runs a tiny local web server that serves ``proof-anatomy.html`` (the
byte-exact icicle of the fixed wire layout) together with the given
``RootProofBytes`` file, so the page decodes and displays the actual field
values at every offset. Produce a proof file with::

    stark-v-bench recursion --elf <guest.elf> --proof-out proof.bin

Usage::

    uv run tools/proof_anatomy.py proofs/commit_once.root.proof
"""

from __future__ import annotations

import argparse
import http.server
import json
import logging
import threading
import webbrowser
from pathlib import Path

LOGGER = logging.getLogger("proof_anatomy")
ROOT_PROOF_BYTE_SIZE = 3_479_096
PAGE = Path(__file__).resolve().parent / "proof-anatomy.html"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Serve the proof-anatomy viewer for one root proof file."
    )
    parser.add_argument("proof", type=Path, help="path to a RootProofBytes file")
    parser.add_argument("--port", type=int, default=8378)
    parser.add_argument(
        "--no-open", action="store_true", help="do not open the browser"
    )
    return parser.parse_args()


def make_handler(proof: Path) -> type[http.server.BaseHTTPRequestHandler]:
    proof_bytes = proof.read_bytes()
    if len(proof_bytes) != ROOT_PROOF_BYTE_SIZE:
        LOGGER.warning(
            "proof is %d bytes, the frozen wire is %d — the page will refuse to decode it",
            len(proof_bytes),
            ROOT_PROOF_BYTE_SIZE,
        )
    meta = json.dumps({"name": proof.name, "size": len(proof_bytes)}).encode()
    page = PAGE.read_bytes()

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802 (http.server API)
            routes = {
                "/": (page, "text/html; charset=utf-8"),
                "/proof-anatomy.html": (page, "text/html; charset=utf-8"),
                "/proof.bin": (proof_bytes, "application/octet-stream"),
                "/meta.json": (meta, "application/json"),
            }
            body_type = routes.get(self.path.split("?")[0])
            if body_type is None:
                self.send_error(404)
                return
            body, content_type = body_type
            self.send_response(200)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, fmt: str, *args: object) -> None:
            LOGGER.debug(fmt, *args)

    return Handler


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    args = parse_args()
    if not args.proof.is_file():
        LOGGER.error("no such proof file: %s", args.proof)
        return 1
    server = http.server.ThreadingHTTPServer(
        ("127.0.0.1", args.port), make_handler(args.proof)
    )
    url = f"http://127.0.0.1:{server.server_address[1]}/"
    LOGGER.info("serving %s at %s (Ctrl-C to stop)", args.proof, url)
    if not args.no_open:
        threading.Timer(0.3, webbrowser.open, args=(url,)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        LOGGER.info("stopped")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

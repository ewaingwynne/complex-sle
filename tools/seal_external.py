#!/usr/bin/env python3
"""Seal a proved EXTERNAL anchor in place (ruling R30, M10).

Usage: seal_external.py ANCHOR_ID PROVIDER_MODULE PROVIDER_EXPORT "BODY"

The statement and ABI are unchanged. The frozen prefix gains `import PROVIDER_MODULE`, and its module docstring
now says the input is proved. The body `by sorry` becomes BODY, which must be at most 3 lines and 240 bytes. In
the manifest the state becomes SEALED, the provider is recorded and the prefix hash is refreshed. Run
`tools/check.sh` afterwards; the guard recomputes everything else.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "frozen-anchor-manifest.json"
PROOF_BEGIN = "-- FROZEN_ANCHOR_PROOF_BEGIN\n"
PROOF_END = "-- FROZEN_ANCHOR_PROOF_END\n"
ASSUMED = re.compile(r"Assumed,\s+not\s+proved:\s+its\s+body\s+is\s+a\s+permanent\s+`sorry`,\s+and\s+every\s+result"
                     r"\s+that\s+uses\s+it\s+is\s+reported\s+`PROVED_REL`\.")


def main() -> None:
    anchor_id, module, export, body = sys.argv[1:5]
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    anchor = next(a for a in data["anchors"] if a["id"] == anchor_id)
    if anchor.get("state") != "EXTERNAL":
        raise SystemExit(f"{anchor_id}: not EXTERNAL")
    path = ROOT / anchor["path"]
    text = path.read_text(encoding="utf-8")
    start = text.index(PROOF_BEGIN) + len(PROOF_BEGIN)
    end = text.index(PROOF_END)
    prefix, suffix = text[:start], text[end:]
    if text[start:end] != "  by sorry\n":
        raise SystemExit(f"{anchor_id}: unexpected body {text[start:end]!r}")
    imports = list(re.finditer(r"^(public )?import [^\n]+\n", prefix, flags=re.M))
    at = imports[-1].end()
    prefix = prefix[:at] + f"import {module}\n" + prefix[at:]
    prefix, count = ASSUMED.subn(f"Proved in-project (M10, ruling R30) by\n`{export}`.", prefix)
    if count != 1:
        raise SystemExit(f"{anchor_id}: docstring sentence not found")
    prefix = prefix.replace("# EXTERNAL input: ", "# Classical input (proved): ", 1)
    new_body = body.rstrip("\n") + "\n"
    if len(new_body.splitlines()) > 3 or len(new_body.encode()) > 240:
        raise SystemExit(f"{anchor_id}: body exceeds the seal limits")
    path.write_text(prefix + new_body + suffix, encoding="utf-8")
    anchor["state"] = "SEALED"
    anchor["implementation"] = {"module": module, "export": export}
    anchor["draft_allowlist"] = {"frozen_paths": [], "audit_paths": []}
    anchor["prefix_sha256"] = hashlib.sha256(prefix.encode("utf-8")).hexdigest()
    MANIFEST.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    digest = hashlib.sha256(MANIFEST.read_bytes()).hexdigest()
    for graph in (ROOT / "DEPGRAPH.md", ROOT / "graph" / "DEPGRAPH.header.md"):
        if graph.exists():
            graph.write_text(re.sub(r"(FROZEN_MANIFEST:[^\n]*sha256:)[0-9a-f]{64}", rf"\g<1>{digest}",
                                    graph.read_text(encoding="utf-8")), encoding="utf-8")
    print(f"sealed {anchor_id}; manifest sha256 {digest}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Assemble DEPGRAPH.md and DEPGRAPH_COVERAGE.md from slice packets (orchestrator only).

Usage: python3 -I tools/graph_merge.py [--lint-only]

Inputs:  graph/DEPGRAPH.header.md, graph/packets/*.md (each with `## Nodes` and/or
         `## Coverage` sections; other sections are ignored).
Outputs: DEPGRAPH.md, DEPGRAPH_COVERAGE.md (project root), then runs tools/proof_depgraph.py.

During initial one-writer drafting the packets are the editable working copy; after
publication, structural corrections go through append-only AMEND records instead.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKETS = ROOT / "graph" / "packets"
CORPUS = "source/arxiv-2411.06301v2/fixed-pt-finite-type.tex sha256:b0fb466bfd59b1fd0e03757eddca48f8e67aa194a43b66880d2caeb677061670"


def section(text: str, name: str) -> str:
    match = re.search(rf"(?ms)^## {name}\s*\n(.*?)(?=^## |\Z)", text)
    return match.group(1).strip() if match else ""


def blocks(body: str, key: str) -> list[str]:
    parts = re.split(rf"(?m)^(?={key}:)", body)
    return [p.strip() for p in parts if p.strip().startswith(f"{key}:")]


def main() -> None:
    nodes, items, ids, item_ids = [], [], {}, {}
    for packet in sorted(PACKETS.glob("*.md")):
        text = packet.read_text(encoding="utf-8")
        for block in blocks(section(text, "Nodes"), "NODE"):
            node_id = block.splitlines()[0].split(":", 1)[1].strip()
            if node_id in ids and node_id.startswith("ext:"):
                # External leaves may be proposed by several slices; keep the first block.
                print(f"note: external {node_id} also proposed in {packet.name}; keeping {ids[node_id]}")
                continue
            if node_id in ids:
                sys.exit(f"duplicate NODE {node_id} in {packet.name} and {ids[node_id]}")
            ids[node_id] = packet.name
            nodes.append(block)
        for block in blocks(section(text, "Coverage"), "ITEM"):
            item_id = block.splitlines()[0].split(":", 1)[1].strip()
            if item_id in item_ids:
                sys.exit(f"duplicate ITEM {item_id} in {packet.name} and {item_ids[item_id]}")
            item_ids[item_id] = packet.name
            items.append(block)
    header = (ROOT / "graph" / "DEPGRAPH.header.md").read_text(encoding="utf-8")
    amend_path = ROOT / "graph" / "AMENDMENTS.md"
    amend = amend_path.read_text(encoding="utf-8").strip() if amend_path.exists() else ""
    db = (header + "\n\n".join(nodes) + "\n\n## Append-only structural amendments\n\n" + (amend + "\n\n" if amend else "")
          + "<!-- BEGIN PROOF DEPGRAPH GENERATED -->\n<!-- END PROOF DEPGRAPH GENERATED -->\n")
    existing = (ROOT / "DEPGRAPH.md")
    if existing.exists():
        old = existing.read_text(encoding="utf-8")
        gen = re.search(r"(?s)<!-- BEGIN PROOF DEPGRAPH GENERATED -->.*<!-- END PROOF DEPGRAPH GENERATED -->", old)
        if gen:
            db = db.replace("<!-- BEGIN PROOF DEPGRAPH GENERATED -->\n<!-- END PROOF DEPGRAPH GENERATED -->", gen.group(0))
    existing.write_text(db, encoding="utf-8")
    cov = (f"# Proof-source coverage manifest — arXiv:2411.06301v2\n\nCORPUS: {CORPUS}\n\n"
           "Every theorem-like source unit, definition, reused display, citation, and candidate "
           "substantive proof paragraph receives exactly one disposition.\n\n## Inventory\n\n"
           + "\n\n".join(items) + "\n")
    (ROOT / "DEPGRAPH_COVERAGE.md").write_text(cov, encoding="utf-8")
    print(f"merged {len(nodes)} nodes and {len(items)} coverage items")
    flags = sys.argv[1:]
    cmd = [sys.executable, "-I", str(ROOT / "tools" / "proof_depgraph.py"), "--db", "DEPGRAPH.md",
           "--manifest", "DEPGRAPH_COVERAGE.md", "--source-root", "."] + (flags or ["--report"])
    result = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    sys.stdout.write(result.stdout[-6000:])
    sys.stderr.write(result.stderr[-6000:])
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()

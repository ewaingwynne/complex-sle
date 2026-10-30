#!/usr/bin/env python3
"""Apply a topology reviewer's replacement fragments to the slice packets (orchestrator only).

Usage: python3 -I tools/apply_review.py REVIEW.md [--dry-run]

Fragments are fenced blocks under `### <tag> <target-node-or-item>` headings:
  * a block starting `NODE:` (or `ITEM:`) replaces or adds that whole record;
  * otherwise each `FIELD: value` line replaces that field in the target record, and each
    `EDGE: <dep> | …` line replaces the EDGE for <dep> (or is added). When DEPS changes, EDGE
    lines for dropped dependencies are removed.
If the prose right before a block names a different record ("block `X`"), the fragment
targets X. Prose of the form "delete the EDGE line(s) to `a` and `b`" removes those edges.
Unapplied fragments are reported, never guessed.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKETS = ROOT / "graph" / "packets"


def load() -> dict[str, str]:
    return {p.name: p.read_text(encoding="utf-8") for p in sorted(PACKETS.glob("*.md"))}


def find(texts: dict[str, str], key: str, rid: str):
    for name, text in texts.items():
        m = re.search(rf"(?ms)^{key}: {re.escape(rid)}\n.*?(?=^NODE: |^ITEM: |^## |\Z)", text)
        if m:
            return name, m
    return None, None


def deps(block: str) -> list[str]:
    m = re.search(r"(?m)^DEPS:[ \t]*(.*)$", block)
    return [d.strip() for d in m.group(1).split(",") if d.strip() not in ("", "-")] if m else []


def set_edge(block: str, line: str) -> str:
    dep = line.split(":", 1)[1].split("|", 1)[0].strip()
    pat = rf"(?m)^EDGE: {re.escape(dep)} \|.*$"
    if re.search(pat, block):
        return re.sub(pat, lambda _: line, block, count=1)
    anchor = list(re.finditer(r"(?m)^EDGE:.*$", block)) or list(re.finditer(r"(?m)^ROUTE_FOR:.*$", block))
    e = anchor[-1]
    return block[:e.end()] + "\n" + line + block[e.end():]


def drop_edge(block: str, dep: str) -> str:
    return re.sub(rf"(?m)^EDGE: {re.escape(dep)} \|.*\n?", "", block)


def apply_fields(block: str, lines: list[str]) -> str:
    for line in lines:
        if not re.match(r"^[A-Z][A-Z0-9_]*:", line):
            continue
        field = line.split(":", 1)[0]
        if field == "EDGE":
            block = set_edge(block, line)
            continue
        if re.search(rf"(?m)^{field}:.*$", block):
            block = re.sub(rf"(?m)^{field}:.*$", lambda _: line, block, count=1)
        else:
            block = block.rstrip("\n") + "\n" + line + "\n"
    keep = set(deps(block)) | {r.strip() for r in re.search(r"(?m)^ROUTES:[ \t]*(.*)$", block).group(1).split(",")} \
        if re.search(r"(?m)^ROUTES:", block) else set(deps(block))
    for m in list(re.finditer(r"(?m)^EDGE: (\S+) \|", block)):
        if m.group(1) not in keep:
            block = drop_edge(block, m.group(1))
    return block


def main() -> None:
    review = Path(sys.argv[1]).read_text(encoding="utf-8")
    dry = "--dry-run" in sys.argv
    texts = load()
    reviewer_slice = re.search(r"slice-([A-Z])\.review", sys.argv[1])
    home = f"slice-{reviewer_slice.group(1)}.md" if reviewer_slice else "slice-O.md"
    applied, skipped = [], []
    for sec in re.finditer(r"(?ms)^### (\S+) (.*?)\n(.*?)(?=^### |^## |\Z)", review):
        tag, head, body = sec.group(1), sec.group(2), sec.group(3)
        target = head.split()[0].strip("`")
        pos = 0
        for fb in re.finditer(r"(?ms)^```[a-z]*\n(.*?)^```", body):
            prose = body[pos:fb.start()]; pos = fb.end()
            code = fb.group(1).strip("\n")
            named = re.findall(r"block `([^`]+)`", prose)
            tgt = named[-1] if named else target
            first = code.splitlines()[0] if code else ""
            if first.startswith(("NODE:", "ITEM:")):
                key, rid = first.split(":", 1)[0], first.split(":", 1)[1].strip()
                name, m = find(texts, key, rid)
                rec = code + "\n\n"
                if m:
                    texts[name] = texts[name][:m.start()] + rec + texts[name][m.end():]
                else:
                    section = "## Nodes" if key == "NODE" else "## Coverage"
                    t = texts[home]
                    i = t.find(section)
                    if i < 0:
                        t = t.rstrip("\n") + f"\n\n{section}\n\n"; i = t.find(section)
                    j = t.find("\n## ", i + 1)
                    j = len(t) if j < 0 else j
                    texts[home] = t[:j].rstrip("\n") + "\n\n" + rec + t[j:]
                applied.append(f"{tag}: {key} {rid} {'replaced' if m else 'added'}")
                continue
            key = "ITEM" if tgt.startswith("inv:") else "NODE"
            name, m = find(texts, key, tgt)
            if not m:
                skipped.append(f"{tag}: target {tgt} not found"); continue
            block = apply_fields(m.group(0), code.splitlines())
            texts[name] = texts[name][:m.start()] + block + texts[name][m.end():]
            applied.append(f"{tag}: fields of {tgt}")
        for d in re.findall(r"delete the EDGE lines? to ([^;)]+)", body):
            name, m = find(texts, "NODE", target)
            if not m:
                continue
            block = m.group(0)
            for dep in re.findall(r"`([^`]+)`", d):
                if dep in deps(block):
                    skipped.append(f"{tag}: {dep} still in DEPS of {target}; edge kept")
                else:
                    block = drop_edge(block, dep)
            texts[name] = texts[name][:m.start()] + block + texts[name][m.end():]
    if not dry:
        for name, text in texts.items():
            (PACKETS / name).write_text(text, encoding="utf-8")
    print("\n".join(applied))
    print("SKIPPED:\n" + "\n".join(skipped) if skipped else "SKIPPED: none")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Append author-approved anchors to `frozen-anchor-manifest.json`.

Usage: python3 -I tools/manifest_add.py SPEC.json

SPEC.json is a list of objects with the fields
  id, kind ("definition" | "theorem"), export, path, source_range, contract_id,
  approved_at, approval_ref, ruling_ref, split_group (optional, defaults to contract_id),
  split_mode (optional, defaults to NOT_SPLIT), closure (list of definition-anchor paths),
and, for theorems, implementation {module, export}.

The script computes every hash from the files as they are now (whole-file hash for
definitions; prefix/suffix hashes for theorems; elaborated ABI hash via a Lean probe)
and refuses to overwrite an existing anchor ID, path, or export. It is run only by the
orchestrator, immediately after a recorded author approval. It has no update mode:
a changed declaration needs a new versioned anchor.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "frozen-anchor-manifest.json"
sys.path.insert(0, str(ROOT / "tools"))
import leanprobe  # noqa: E402

REVISION = "arXiv:2411.06301v2 fixed-pt-finite-type.tex sha256:b0fb466bfd59b1fd0e03757eddca48f8e67aa194a43b66880d2caeb677061670"


def sha(path: str) -> str:
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def regions(path: str) -> tuple[str, str]:
    text = (ROOT / path).read_bytes().decode("utf-8")
    body_start = text.index("\n", text.index("FROZEN_ANCHOR_PROOF_BEGIN")) + 1
    body_end = text.rfind("\n", 0, text.index("FROZEN_ANCHOR_PROOF_END")) + 1
    digest = lambda s: hashlib.sha256(s.encode("utf-8")).hexdigest()
    return digest(text[:body_start]), digest(text[body_end:])


def main() -> None:
    spec = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    data = (json.loads(MANIFEST.read_text(encoding="utf-8")) if MANIFEST.exists() else
            {"schema_version": 1, "manifest_state": "AUTHOR_APPROVED",
             "seal_limits": {"max_body_lines": 3, "max_body_bytes": 240}, "anchors": []})
    taken = {(key, a[key]) for a in data["anchors"] for key in ("id", "path", "export")}
    for item in spec:
        for key in ("id", "path", "export"):
            if (key, item[key]) in taken:
                raise SystemExit(f"refusing to overwrite existing anchor {key}={item[key]}")
    pairs = [(".".join(Path(item["path"]).with_suffix("").parts), item["export"]) for item in spec]
    abis = leanprobe.abi_many(pairs)
    for item in spec:
        entry = {
            "id": item["id"],
            "kind": item["kind"],
            "author_approval": {"approved_by": "Ewain Gwynne", "approved_at": item["approved_at"],
                                "approval_ref": item["approval_ref"], "approval_version": "1"},
            "source": {"revision": REVISION, "range": item["source_range"]},
            "contract": {"id": item["contract_id"], "version": "1"},
            "path": item["path"],
            "export": item["export"],
            "split_policy": {"source_group": item.get("split_group", item["contract_id"]),
                             "mode": item.get("split_mode", "NOT_SPLIT"),
                             "ruling_ref": item["ruling_ref"]},
            "abi_sha256": abis[item["export"]],
            "definition_closure": [{"path": p, "sha256": sha(p)} for p in item["closure"]],
        }
        if item["kind"] == "definition":
            entry["state"] = "SEALED"
            entry["full_file_sha256"] = sha(item["path"])
        else:
            prefix, suffix = regions(item["path"])
            entry["implementation"] = item["implementation"]
            entry["state"] = "DRAFT_SORRY"
            entry["prefix_sha256"] = prefix
            entry["suffix_sha256"] = suffix
            entry["draft_allowlist"] = {"frozen_paths": [], "audit_paths": []}
        data["anchors"].append(entry)
    MANIFEST.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"added {len(spec)} anchors; manifest now has {len(data['anchors'])}")


if __name__ == "__main__":
    main()

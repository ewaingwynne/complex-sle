#!/usr/bin/env python3
"""Untracked Lean probes for the frozen-anchor workflow.

Subcommands (run from the project root):

  abi MODULE DECL     Print the elaborated ABI record of DECL and its SHA-256.
                      The record is the declaration kind, universe parameters,
                      elaborated type, and (for definitions) elaborated value,
                      rendered with `Expr.dbgToString`. The hash is what the
                      manifest stores as `abi_sha256`.
  abi-many MODULE:DECL...  ABI hashes of several declarations in one Lean run.
  verify-abi MANIFEST Recompute every anchor's ABI hash and fail on any drift.
  axioms MODULE DECL  Run `#print axioms DECL` and report the axiom list.
  sha FILE...         SHA-256 of raw file bytes (for `full_file_sha256`).
  regions FILE        SHA-256 of the frozen prefix and suffix of a theorem file.

Probe files are written under `.lake/probes/` (ignored by git and by the
frozen-anchor checker) and deleted after use, so they never become tracked
Lean source.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBES = ROOT / ".lake" / "probes"
ENV = dict(os.environ)
ENV["PATH"] = f"{Path.home()}/.elan/bin:{Path.home()}/.local/bin:" + ENV.get("PATH", "")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

ABI_PROBE = r"""import {module}

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let some ci := env.find? `{decl} | throwError "unknown constant {decl}"
  let kind := match ci with
    | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive"
    | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
  let value := match ci with
    | .defnInfo d => d.value.dbgToString
    | _ => ""
  IO.println "ABI_BEGIN"
  IO.println s!"kind={{kind}}"
  IO.println s!"levels={{ci.levelParams}}"
  IO.println s!"type={{ci.type.dbgToString}}"
  IO.println s!"value={{value}}"
  IO.println "ABI_END"
"""

AXIOM_PROBE = "import {module}\n\n#print axioms {decl}\n"


def run_probe(source: str) -> str:
    PROBES.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(suffix=".lean", dir=PROBES)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(source)
        result = subprocess.run(["lake", "env", "lean", name], cwd=ROOT, env=ENV,
                                capture_output=True, text=True)
    finally:
        os.unlink(name)
    if result.returncode != 0:
        sys.stderr.write(result.stdout + result.stderr)
        raise SystemExit(f"probe failed with exit code {result.returncode}")
    return result.stdout


def abi(module: str, decl: str) -> None:
    out = run_probe(ABI_PROBE.format(module=module, decl=decl))
    match = re.search(r"ABI_BEGIN\n(.*)\nABI_END", out, re.S)
    if not match:
        raise SystemExit("probe produced no ABI record:\n" + out)
    record = match.group(1)
    print(json.dumps({"decl": decl, "abi_sha256": hashlib.sha256(record.encode()).hexdigest(),
                      "record_bytes": len(record.encode())}))


def axioms(module: str, decl: str) -> None:
    out = run_probe(AXIOM_PROBE.format(module=module, decl=decl))
    text = " ".join(out.split())
    if "does not depend on any axioms" in text:
        found: list[str] = []
    else:
        match = re.search(r"depends on axioms: \[(.*?)\]", text)
        if not match:
            raise SystemExit("unexpected #print axioms output:\n" + out)
        found = [item.strip() for item in match.group(1).split(",") if item.strip()]
    extra = sorted(set(found) - STANDARD_AXIOMS)
    print(json.dumps({"decl": decl, "axioms": found, "nonstandard": extra}))
    if extra:
        raise SystemExit(1)


def regions(path: str) -> None:
    text = Path(path).read_bytes().decode("utf-8")
    body_start = text.index("\n", text.index("FROZEN_ANCHOR_PROOF_BEGIN")) + 1
    body_end = text.rfind("\n", 0, text.index("FROZEN_ANCHOR_PROOF_END")) + 1
    digest = lambda s: hashlib.sha256(s.encode("utf-8")).hexdigest()
    print(json.dumps({"prefix_sha256": digest(text[:body_start]),
                      "suffix_sha256": digest(text[body_end:]),
                      "body": text[body_start:body_end]}))


def abi_many(pairs: list[tuple[str, str]]) -> dict[str, str]:
    """ABI hashes for several (module, decl) pairs in a single Lean run."""
    imports = "\n".join(sorted({f"import {module}" for module, _ in pairs}))
    body = ABI_PROBE.split("\n", 1)[1]
    blocks = [body.format(module="", decl=decl).replace("ABI_BEGIN", f"ABI_BEGIN {decl}")
              for _, decl in pairs]
    out = run_probe(imports + "\n" + "\n".join(blocks))
    found = dict(re.findall(r"ABI_BEGIN (\S+)\n(.*?)\nABI_END", out, re.S))
    missing = [decl for _, decl in pairs if decl not in found]
    if missing:
        raise SystemExit(f"probe produced no ABI record for {missing}")
    return {decl: hashlib.sha256(record.encode()).hexdigest() for decl, record in found.items()}


def verify_abi(manifest: str) -> None:
    """Recompute every anchor's ABI hash and compare it with the manifest."""
    data = json.loads(Path(manifest).read_text(encoding="utf-8"))
    pairs = [(".".join(Path(a["path"]).with_suffix("").parts), a["export"]) for a in data["anchors"]]
    actual = abi_many(pairs)
    bad = [a["export"] for a in data["anchors"] if actual[a["export"]] != a["abi_sha256"]]
    if bad:
        raise SystemExit(f"ABI hash drift: {bad}")
    print(f"ABI OK ({len(pairs)} anchors)")


def main(argv: list[str]) -> None:
    if len(argv) >= 2 and argv[0] == "verify-abi":
        verify_abi(argv[1])
    elif len(argv) >= 2 and argv[0] == "abi-many":
        pairs = [tuple(item.split(":", 1)) for item in argv[1:]]
        print(json.dumps(abi_many(pairs), indent=1))
    elif len(argv) >= 3 and argv[0] == "abi":
        abi(argv[1], argv[2])
    elif len(argv) >= 3 and argv[0] == "axioms":
        axioms(argv[1], argv[2])
    elif len(argv) >= 2 and argv[0] == "sha":
        for path in argv[1:]:
            print(hashlib.sha256(Path(path).read_bytes()).hexdigest(), path)
    elif len(argv) == 2 and argv[0] == "regions":
        regions(argv[1])
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])

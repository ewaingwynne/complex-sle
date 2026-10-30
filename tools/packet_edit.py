"""Orchestrator merge edits on graph packets (drafting phase)."""
import re, sys
P = "graph/packets/slice-{}.md"
def load(s): return open(P.format(s)).read()
def save(s, t): open(P.format(s), "w").write(t)
def block_span(t, nid):
    m = re.search(rf"(?m)^NODE: {re.escape(nid)}\n", t)
    if not m: raise SystemExit(f"missing {nid}")
    end = re.search(r"(?m)^(NODE: |## )", t[m.end():])
    return m.start(), m.end() + (end.start() if end else len(t) - m.end())
def drop(s, nid):
    t = load(s); a, b = block_span(t, nid); save(s, t[:a] + t[b:])
def set_deps(s, nid, deps, edges):
    """Replace DEPS and all EDGE lines of node nid. edges: dict dep -> 'locator | rationale'."""
    t = load(s); a, b = block_span(t, nid); blk = t[a:b]
    old = dict(re.findall(r"(?m)^EDGE: (\S+) \| (.*)$", blk))
    blk = re.sub(r"(?m)^EDGE: .*\n", "", blk)
    lines = "".join(f"EDGE: {d} | {edges.get(d) or old[d]}\n" for d in deps)
    blk = re.sub(r"(?m)^DEPS: .*\n", f"DEPS: {', '.join(deps) if deps else '-'}\n", blk)
    blk = re.sub(r"(?m)^(ROUTE_FOR: .*\n)", lambda m: m.group(1) + lines, blk, count=1)
    save(s, t[:a] + blk + t[b:])

#!/usr/bin/env python3
"""Fingerprint project source dependencies in a pinned RKResearch checkout.

Usage:
  python3 source-closure.py REPO NEW_PACKET LEGACY_PACKET EDGES MODULE...
A packet argument is a root holding ai-generated/lean, such as publish/.
MODULE names are the Lean roots; stdout is a topological project source
list. EDGES is a TSV with direct external imports so their package lock
can be checked separately. Standard library implicit Prelude/Init are
fixed by the selected Lean compiler.
"""
import hashlib
import re
import sys
from pathlib import Path

repo, new, old, edges = map(Path, sys.argv[1:5])
sources = [
    (new / "ai-generated/lean", "ai-generated/lean"),
    (old / "ai-generated/lean", "ai-generated/lean"),
    (repo / "ai-generated/lean", "ai-generated/lean"),
    (repo, ""),
]
import_line = re.compile(r"^[ \t]*(?:(?:public|meta)\s+)*import[ \t]+([^\r\n]+)", re.M)
module_name = re.compile(r"[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*")
done = set()
external = set()

def source(m):
    p = Path(*m.split(".")).with_suffix(".lean")
    for root, prefix in sources:
        f = root / p
        if f.is_file():
            return f, (Path(prefix) / p).as_posix()
    return None

def visit(m):
    if m in done:
        return
    item = source(m)
    if item is None:
        if m.startswith(("RKCert.", "RKResearch.")):
            raise SystemExit(f"missing project module {m}")
        return
    f, display = item
    done.add(m)
    data = f.read_bytes()
    for line in import_line.findall(data.decode("utf8")):
        for t in line.split("--", 1)[0].strip().split():
            if not module_name.fullmatch(t):
                raise SystemExit(f"unexpected import token {t!r} in {f}")
            if source(t) is None:
                if t.startswith(("RKCert.", "RKResearch.")):
                    raise SystemExit(f"missing project import {t!r} in {f}")
                external.add((m, t))
            else:
                visit(t)
    print(m, display, hashlib.sha256(data).hexdigest(), sep="\t")

for module in sys.argv[5:]:
    visit(module)
edges.write_text("".join(f"{m}\t{t}\n" for m, t in sorted(external)), encoding="utf8")

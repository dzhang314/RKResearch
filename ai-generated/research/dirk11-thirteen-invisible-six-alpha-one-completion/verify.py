#!/usr/bin/env python3
"""Check exact dependency snapshots and independently replay the zero/low frontier."""
import argparse
import ast
import hashlib
import os
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("repo", type=Path)
ap.add_argument("--manifests-only", action="store_true")
args = ap.parse_args()
repo = args.repo.resolve()
generated = repo / "ai-generated"
r = generated / "research"
stem = "dirk11-thirteen-invisible-six-"

def hash_file(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def parse(line):
    h, name = line.split(None, 1)
    p = Path(name)
    assert len(h) == 64 and not p.is_absolute() and ".." not in p.parts
    return h, p

n = m = 0
for row in (here / "prior.sha256").read_text().splitlines():
    h, rel = parse(row)
    packet = repo / rel
    assert hash_file(packet) == h, packet
    n += 1
    for entry in packet.read_text().splitlines():
        want, item = parse(entry)
        if item.parts[0] == "ai-generated":
            p = repo / item
        elif item.parts[0] in {"research", "lean"}:
            p = generated / item
        else:
            p = packet.parent / item
        assert hash_file(p) == want, p
        m += 1
print(f"Checked {n} exact dependency manifests and all {m} listed files.", flush=True)
if args.manifests_only:
    raise SystemExit(0)
env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", SYMPY_GROUND_TYPES="flint")
def run(folder, file, *tail):
    subprocess.run([sys.executable, file, *tail], cwd=r / (stem + folder),
                   env=env, check=True)
run("constant-exclusion", "replay.py")
run("linear", "replay.py")
run("alpha1-five-zero", "replay.py")
for t in ("Fn0", "F10", "F1x", "F2x", "Fnx"):
    run("alpha-one-zero-cubic", "clock.py", t)
run("alpha-one-zero-cubic", "finite.py")
# Verify the precise affine-pivot source reused in the zero carrier towers.
def coeffs(p):
    entries = ast.parse(p.read_text()).body
    return ast.literal_eval(next(x.value for x in entries if isinstance(x, ast.Assign)
        and isinstance(x.targets[0], ast.Name) and x.targets[0].id == "A1_TERMS"))
q = r / (stem + "alpha-two-quadratic")
assert coeffs(q / "singular.py") == coeffs(r / (stem + "alpha-one-zero-cubic") / "clock.py")
run("alpha-two-quadratic", "check-old-pivot.py")
print("All lower-degree and zero-reciprocal exact replays exited successfully.", flush=True)

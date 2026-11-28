"""Recreate the portable data declarations from the two archived literal sets."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("out", type=Path)
args = parser.parse_args()
data = Path(__file__).resolve().parent.parent
args.out.mkdir(parents=True, exist_ok=True)
base, lift = (json.loads((data / f"{n}-literals.json").read_text())
              for n in ("prime", "square"))
assert len(base) == len(lift) == 130
module = "ERK10FifteenPrimeGeometry"
for k in range(0, len(base), 10):
    out = f"import {module}\n\nnamespace RKResearch.Certified.{module}\n"
    for v, w in zip(base[k:k+10], lift[k:k+10]):
        p = v["p"]
        assert p == w["p"]
        iv = [0] + [pow(j, -1, p*p) for j in range(1, 21)]
        d = v["guards"]["d_fixed_geometry_det"]
        out += f"""
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem prime{p} : verify {p} {iv} {v["geometry"]} {w["geometry"]} {d} = true := by
  decide +kernel
"""
    out += f"\nend RKResearch.Certified.{module}\n"
    (args.out / f"{module}Batch{k//10+1:02}.lean").write_text(out)

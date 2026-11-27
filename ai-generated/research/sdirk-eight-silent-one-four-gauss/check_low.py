"""Exact Gauss-only exclusions for a single invisible strict SDIRK8 stage."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal"):
 sys.path.insert(0,str(root/dep))
from five_on_four import main as five
from distinct_prefix import main as four_distinct
from repeated_prefix import verify
if __name__=='__main__':
 five()
 four_distinct()
 assert verify(1129,203)
 print('four active, all repeated prefix orientations excluded',flush=True)

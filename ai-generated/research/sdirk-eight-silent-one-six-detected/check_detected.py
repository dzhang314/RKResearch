"""All six active with a detected cubic defect: exact scalar gates."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal"):
 sys.path.insert(0,str(root/dep))
from six_gauss_terminal import main as gauss
from six_terminal_defect import main as defect
if __name__=='__main__':
 gauss()
 defect()

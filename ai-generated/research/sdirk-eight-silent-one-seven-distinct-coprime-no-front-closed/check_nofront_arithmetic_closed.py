"""Run the complete guarded all-orientation no-literal arithmetic replay."""
import sys
from pathlib import Path
from itertools import product

ROOT=Path(__file__).resolve().parent.parent
for p in sorted(ROOT.glob("sdirk-eight-*")):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from nofront_complete_checks import comprehensive
from leading_branch import check as tail_zero
from fourth_drop_branch import check4 as fourth_zero

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):
  assert not tail_zero(f,i,1103,161)
  assert not fourth_zero(f,i,1103,161)
  assert comprehensive(f,i)
 print('complete guarded no-active-literal arithmetic exclusions: 4')

"""Replay all four guarded sole-fifth star-rear modes."""
import sys
from pathlib import Path
from itertools import product
ROOT=Path(__file__).resolve().parent.parent
for p in sorted(ROOT.glob('sdirk-eight-*')):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from star_fifth import check_star
from fifth_fibers import run_star

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):
  assert check_star(f,i)
  assert not run_star(f,i)
 print('complete sole-nonliteral-fifth star-rear exclusions: 4')

"""Exact star and arithmetic closures for sole physical sixth or seventh transport."""
import sys
from pathlib import Path
from itertools import product
ROOT=Path(__file__).resolve().parent.parent
for p in sorted(ROOT.glob('sdirk-eight-*')):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from fibers_67 import fibers67

if __name__=='__main__':
 for f,i,r in product((True,False),(0,1),(True,False)):
  assert not fibers67(f,i,r)
 print('complete sole-nonliteral-sixth/seventh exclusions: 8')

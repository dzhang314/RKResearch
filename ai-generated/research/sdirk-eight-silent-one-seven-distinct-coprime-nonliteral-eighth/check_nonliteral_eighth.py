"""Verify the entire actual silent-eighth proof from exact source data."""
import sys
from pathlib import Path
from itertools import product
ROOT=Path(__file__).resolve().parent.parent
for p in sorted(ROOT.glob('sdirk-eight-*')):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from eighth_fibers import eighth_fibers
from eighth_projection import inputs8, Q, gcdp
from nonliteral_fourth_projection import s_phase

def check(f,i):
 p,t=(1103,161)
 if (f,i)==(False,1):
  J,B,*_=inputs8(f,i)
  J0,B0=(s_phase(F,Q(0)) for F in (J,B))
  assert len(J0)==J.degrees()[1]+1 and len(B0)==67 and len(gcdp(J0,B0))==1
  # The padded resultant at gamma=0 is also nonzero: J retains
  # its full s-degree. The reduced-zero contact at 1103 is incidental.
  p,t=(1129,203)
 assert not eighth_fibers(f,i,p,t)
 return True

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):assert check(f,i)
 print('complete sole-nonliteral-silent-eighth exclusions: 4')

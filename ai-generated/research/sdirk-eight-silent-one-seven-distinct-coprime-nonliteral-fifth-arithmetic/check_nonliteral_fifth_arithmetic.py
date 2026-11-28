"""Replay all four whole-diagonal arithmetic fifth exclusions."""
import sys
from pathlib import Path
from itertools import product
ROOT=Path(__file__).resolve().parent.parent
for p in sorted(ROOT.glob('sdirk-eight-*')):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from arithmetic_fibers import arith_fibers
from arithmetic_crt import arith_inputs,degree_safe_reduction

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):
  J,P,*_=arith_inputs(f,i)
  G=degree_safe_reduction(J,P,1103,161)
  assert G.degree()==(2300 if f else 2416)
  assert not arith_fibers(f,i,G,1103,161)
 print('complete sole-nonliteral-fifth arithmetic-rear exclusions: 4')

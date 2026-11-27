"""Exact scoped cuts of the five-distinct single-invisible case."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-one-row",
            "sdirk-eight-silent-one-six"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from zero_extra import repeated,silent_k0,tests,check_separate
from zero_reverse_active8 import derivative_test,early_fourth,raw,fifth_silent
if __name__=='__main__':
 for p,t in ((1103,161),(1129,203)):
  assert isprime(p) and (2*t*t-1)%p==0
 for f in (True,False):
  assert repeated(f,1103,161) and silent_k0(f,1103,161)
  assert check_separate(f,1129,203)
  for r in (True,False):assert tests(f,r,1129,203)
  print('both extra silent h zero: repeated and distinct physical charts excluded',f)
 for r,e in product((True,False),(1,-1)):
  S,H=raw(r,e)
  for M,k in S.factor_list()[1]:
   for f in (True,False):
    M=M.monic()
    assert fifth_silent(f,r,e,M,H,1103,161)
    assert early_fourth(f,r,e,M,H,1103,161)
    assert derivative_test(f,r,e,M,H,1103,161)
    print('zero reverse factor with active eighth: exact orientation excluded',f,r,e,M.degree())

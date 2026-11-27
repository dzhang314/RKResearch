"""Exact detected seven-active exclusions for five or fewer distinct clocks."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-one-row",
            "sdirk-eight-silent-one-six","sdirk-eight-silent-one-six-detected"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from triple_active8 import cr
from triple_silent8 import both_low,early_triple
from zero_factor_active8 import verify,raw
from early_repeated import fifth_silent
from early_fourth import check as fourth_silent
from six_gauss_terminal import main as gauss_terminal,L4
from six_terminal_defect import main as defect_terminal
if __name__=='__main__':
 assert isprime(1103) and (2*161*161-1)%1103==0
 gauss_terminal()
 defect_terminal()
 for g,e in product((100,214,916,1030),(1,-1)):
  for v in (2+2*e*203,3+4*e*203):
   assert L4(g*v)
 print('literal front non-Gauss at all Gauss diagonals')
 p,t=1103,161
 for f,i,j in product((True,False),(0,1),(9,10)):
  assert cr(f,i,j,p,t)
  for u in (2,1+2*t,1-2*t):
   assert both_low(f,j,i,p,t,u)
   assert early_triple(f,j,i,p,t,u)
  print('detected ordinary triple nonzero or zero k, silent eighth; nonzero k active eighth',f,i,j)
 for f,e in product((True,False),(1,-1)):
  T,H=raw(f,e)
  for M,q in T.factor_list()[1]:
   M=M.monic()
   for j in (True,False):
    assert fifth_silent(j,f,e,M,H,p,t)
    assert fourth_silent(j,f,e,M,H,p,t)
    assert verify(j,f,e,M,H,p,t)
    print('detected ordinary triple zero k active eighth',j,f,e,M.degree())

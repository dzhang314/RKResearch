"""Replay the complete unequal-residual two-invisible-stage exclusion."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for package in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic","sdirk-eight-silent-three-closure"):
 sys.path.insert(0,str(root/package))
import first_four
from gauss_triple import check as triple
from four_active import main as gauss_cubic
from unequal_finite import exact_fifth, exact_tail, verify7
from six import six
from eight import verify8
from sympy import isprime
if __name__=="__main__":
 triple()
 gauss_cubic()
 p,t=1009,285
 assert isprime(p) and (2*t*t-1)%p==0
 for front in (True,False):
  M=exact_fifth(front)
  six(front,M)
  for rear in (None,True,False):
   D=exact_tail(front,rear,M)
   assert len(D[1])-1=={None:6,True:4,False:7}[rear]
   assert verify7(front,rear,D,p,t)
   print("seven active excluded",front,rear,flush=True)
   if rear is not None:
    for n in (7,8):
     assert verify8(front,rear,D,p,t,n)
     print("eight active excluded",front,rear,n,flush=True)

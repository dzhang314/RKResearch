"""Exact anchored-front independent Gauss-double cases at one invisible stage."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from both_front_active8 import test_moments_base,transfer,Lf,G
from both_front_silent8 import verify as both_silent8
from both_front_k0 import verify_active,verify_silent
from front_root import verify as at_literal_front
from no_front_k0 import verify as no_active_front
if __name__=='__main__':
 p,t=1009,285
 assert isprime(p) and (2*t*t-1)%p==0
 assert [(q.degree(),e) for q,e in Lf(G).factor_list()[1]]==[(4,1)]
 for f in (True,False):
  for M,e in transfer(f).factor_list()[1]:
   M=M.monic()
   for rear,which in product((True,False),(0,8,9)):
    assert test_moments_base(f,M,rear,which,p,t)
    for idx in (0,1):assert at_literal_front(f,M,rear,which,idx,p,t)
   for rn in (False,True):assert both_silent8(f,M,rn,p,t)
   for orient in (1,-1):
    assert verify_silent(f,M,orient,p,t)
    for rear in (True,False):assert verify_active(f,M,rear,orient,p,t)
   print('both literal fronts active, all reverse and eighth placements excluded',
         f,M.degree(),flush=True)
  for idx,rear,orient in product((0,1),(True,False),(1,-1)):
   assert no_active_front(f,idx,rear,orient,p,t)
  print('neither literal front active and k=0 excluded',f,flush=True)

"""Finite one-front anchors for the independent six-active-clock Gauss double."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from both_front_active8 import transfer,model,Lf,G,ends,Lco,nmod_poly
from front_root import verify as tail_active
from front_shared_root import silent8 as tail_silent
from one_front_k0 import verify as fixed
from gauss_terminal_silent8 import verify as gauss_silent

def gauss_guard():
 p,t=1129,203
 L=nmod_poly(list(Lco),p)
 G=sorted(int(q) for q,m in L.roots() if m==1)
 assert G==[100,214,916,1030] and (2*t*t-1)%p==0
 for g,s in product(G,(-1,1)):
  for x in (2+2*s*t,3+4*s*t):
   assert L(g*x)
if __name__=='__main__':
 p,t=1009,285
 assert isprime(p) and (2*t*t-1)%p==0
 assert [(q.degree(),e) for q,e in Lf(G).factor_list()[1]]==[(4,1)]
 gauss_guard()
 for f in (True,False):
  A0,B0,_=ends(f,1)
  LA,LB=Lf(G*A0).monic(),Lf(G*B0).monic()
  assert LA.gcd(LB).degree()==0
  fs=[M.monic() for M,e in transfer(f).factor_list()[1]]
  assert LA in fs and LB in fs
  for M,silent in ((LA,1),(LB,0)):
   assert tail_silent(f,M,p,t)
   for rear,which in product((True,False),(0,8,9)):
    assert tail_active(f,M,rear,which,silent,p,t)
   print('nonzero k shared reverse root at literal silent front excluded',f,silent)
  for i in (0,1):
   assert gauss_silent(f,i,p,t)
   for orient in (1,-1):
    for rear in (None,True,False):
     assert fixed(f,i,rear,orient,False,p,t)
     if rear is not None:assert fixed(f,i,rear,orient,True,p,t)
   print('zero k with Gauss terminal or literal silent front terminal excluded',f,i)

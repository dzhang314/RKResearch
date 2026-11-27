"""Exact characteristic-zero projections and guarded finite unit replays."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal"):
 sys.path.insert(0,str(root/dep))
from fifth import *

EXPECTED={
 (True,None): (29,), (False,None): (29,),
 (True,True): (4,4,8,8,10), (False,True): (8,9,10,13),
 (True,False): (8,10,55), (False,False): (8,10,50)}
def verify(front,rear,H,p,t):
 n=0
 for V,data,base_degree in diag_models(front,rear,H,p,t):
  g,x,c,d,a,b,s,ha,hb,rr,lam,q,h4p=data
  pegs=[a*g,b*g,s*g,c,x]+([] if d is None else [d])
  if d is None:
   N,xi=linear_solve(pegs,g,q)
   ans,_,_,_,_=fifth(data,N)
   ans.inv()
  else:
   linear_solve(pegs,g,q).inv()
  n+=1
 return n

def main():
 for p,t in ((1009,285),(1039,315)):
  assert SY.isprime(p) and (2*t*t-1)%p==0
 for f,r in product((True,False),(None,True,False)):
  _,F=proj(f,r)
  assert tuple(sorted(H.degree() for H,e in F if e==1))==EXPECTED[f,r]
  for j,(H,e) in enumerate(F):
   assert e==1
   # The selected reduction can vary between exact diagonal factors.
   # The second fixed prime is needed for one degree-8 and one degree-13 factor.
   report=[]
   for p,t in ((1009,285),(1039,315)):
    try:n=verify(f,r,H.monic(),p,t)
    except (ArithmeticError,AssertionError,ValueError,ZeroDivisionError,TypeError) as E:
     report.append(repr(E));continue
    print('finite factor excluded',f,r,j,H.degree(),'at',p,t,'tail components',n,flush=True)
    break
   else:raise AssertionError((f,r,j,H.degree(),report))
if __name__=='__main__':main()

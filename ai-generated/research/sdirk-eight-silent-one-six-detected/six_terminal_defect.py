"""Detected-six one-invisible chart with nongaus terminal defect clock."""
from six_gauss_terminal import p,t,inv,L4,g3n
from itertools import product
from flint import nmod_poly
from unequal_finite import Bfield,nodal
from sympy import isprime

def gates(U,z,g,a,b,x):
 a0=nodal([a,b]);a1=nodal([a,b,x])
 def test(A):
  at=U(0);mt=U(0)
  for i,v in enumerate(A):
   at+=v*z**(i+1)/(i+1);mt+=v*z**i
  (at-g*mt).inv()
 test(a0)
 test(a1)
def main():
 assert isprime(p) and (2*t*t-1)%p==0
 L=[d for d in range(p) if not L4(d)]
 assert L==[100,214,916,1030]
 P=lambda qs:nmod_poly(qs,p)
 for c,d in product(L,L):
  if c==d:continue
  x=(2*c-d)%p;g=(1-x)%p
  # In the arithmetic active-eighth case, x=2*c9-c8 and g is the strict diagonal.
  assert g and g3n((x-c)*inv(g)%p)
 dcount=0
 for M,c,s,f,y in product((P([-1,-2,1]),P([2,1,-4,1])),L,(1,-1),(True,False),L):
  U=Bfield(M,p,t);u=U(P([0,1]))
  g=(1-c)/(1+u);x=1-g
  A=2+s*2*t;B=2-s*2*t if f else 3+s*4*t
  a,b=g*A,g*B
  (x-a).inv();(x-b).inv()
  gates(U,U(y),g,a,b,x)
  dcount+=1
 print('terminal-defect detected-six: exact scalar gate orientations',dcount)
if __name__=='__main__':main()

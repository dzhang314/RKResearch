"""Single invisible, five active at four Gauss sites: literal row-six test."""
from unequal_finite import *
from equal_detected import ends,h4
from equal_undetected_front import lagrange
from sympy import isprime

def check(front,p,t,g,roots):
 P=lambda q:nmod_poly(q,p)
 B0=Bfield(P([0,1]),p,t)
 cv=lambda q: int(B0.cast(Epoly(JJ(q)))[0]) if q else 0
 A,B,r=ends(front,1)
 h_a,h_b=(A-1)/2,(B-1-r)/2
 a,b,ha,hb=map(cv,(A,B,h_a,h_b))
 H=B0.cast(Epoly(h4(front)))
 L=P([v*pow(g,i,p)%p for i,v in enumerate(Lco)])
 ia,ib=int(L(a))*pow(ha,-1,p)%p,int(L(b))*pow(hb,-1,p)%p
 q1=(ib-ia)*pow((b-a)%p,-1,p)%p
 Q=P([ia-a*q1,q1])
 Z0,rr=divmod(Q*H-L,P([-a,1])*P([-b,1]))
 assert not rr and Z0.degree()==2
 Z0*=pow(int(Z0.leading_coefficient()),-1,p)
 U=Bfield(Z0,p,t);z=U(P([0,1]))
 a,b,ha,hb=map(U,(a,b,ha,hb));hz=U(H)
 (z-a).inv();(z-b).inv()
 # Check the stronger unit guard that row four is not at a Gauss site.
 U(L).inv()
 ns=[a,b,z];gs=[ha,hb,hz]
 B3=lagrange(ns)
 def feeds(cards,y):
  m=[y**(j+1)/(j+1)-y**j for j in range(len(cards))]
  return [sum(w*t for w,t in zip(w0,m)) for w0 in cards]
 for r in roots:
  y=U(r)/g
  ty=feeds(B3,y)
  ah=sum(w*z0 for w,z0 in zip(ty,gs))
  tau=y**3-y**4/4+sum(w*z0**3 for w,z0 in zip(ty,ns))
  ell=[ev(Q,y) for Q in B3]
  d_ah=-sum(w*z0 for w,z0 in zip(ell,gs))
  d_tau=y**3-sum(w*z0**3 for w,z0 in zip(ell,ns))
  (tau*d_ah-ah*d_tau).inv()
  B4=lagrange(ns+[y])
  for s in roots:
   if s==r:continue
   y2=U(s)/g
   (sum(w*z0 for w,z0 in zip(feeds(B4,y2),gs))).inv()
 return True
def main():
 p,t=1129,203
 assert isprime(p) and (2*t*t-1)%p==0
 L=nmod_poly(list(Lco),p)
 roots=sorted(int(v) for v,e in L.roots() if e==1)
 assert roots==[100,214,916,1030]
 for ft,g in product((True,False),roots):
  assert check(ft,p,t,g,roots)
  print('Gauss five-active phase and strict diagonal',ft,g,flush=True)
if __name__=='__main__':main()

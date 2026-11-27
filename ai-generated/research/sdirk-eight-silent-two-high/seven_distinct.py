"""Non-midpoint seven-active, seven distinct physical zero clocks."""
from equal_detected import h4,ends,Z
from unequal_finite import *
from variable_gamma import Lf
from off8_fibers import multicol
from sympy import isprime

def exact_gamma(star):
 A,B,r=ends(star,1)
 ha,hb,hs=(A-1)/2,(B-1-r)/2,h4(star).evaluate(Z,K.one)
 assert all((ha,hb,hs))
 la,lb,lz=Lf(G*A),Lf(G*B),Lf(G)
 M=(B-A)*ha*hb*lz-hs*((B-1)*hb*la+(1-A)*ha*lb)
 assert M.degree()==4 and M.gcd(G*(2*G-1)*lz).degree()==0
 Q1=ha*lb-hb*la
 Q0=G*(B*hb*la-A*ha*lb)
 share=70*Q0**4+140*Q0**3*Q1+90*Q0**2*Q1**2+20*Q0*Q1**3+Q1**4
 assert M.gcd(Q1*share).degree()==0
 D=M.factor_list()[1]
 assert [(p.degree(),e) for p,e in D]==[(4,1)]
 print('seven distinct diagonal degrees',star,[(p.degree(),e) for p,e in D],flush=True)
 for N,e in D:
  N=N.monic();F=ExField(Epoly(N))
  g=F(E(P([0,1])));x=1-g
  cv=lambda u:F(Epoly(JJ(u))) if u else F(0)
  a,b,gam=map(cv,(A,B,hs));a,b=a*g,b*g
  ha,hb=map(cv,(ha,hb))
  ha,hb,hs=ha*g**3,hb*g**3,gam*g**3
  L=list(map(F,Lco))
  Qa,Qb=ev(L,a)/ha,ev(L,b)/hb
  Dq=(Qb-Qa)/(b-a);q=[Qa-a*Dq,Dq]
  assert ev(q,g)*hs==ev(L,g) and not ev(q,g)==0
  assert ev(q,x) and ev(L,x)
  yield N,F,(g,a,b,ha,hb,hs,x,q)

def guard_strip(A,G):
 while True:
  B=gcdp(A,G)
  if len(B)<=1:break
  A,R=divp(A,B);assert not R
 D=gcdp(A,deriv(A));A,R=divp(A,D);assert not R
 return sc(A,A[-1].inv())

def exact_tail(star,M):
 H,F,(g,a,b,ha,hb,hs,x,q)=M
 u=[F(0),F(1)];c=[x,-g];L0=list(map(F,Lco));k=[F(1),F(2),F(-1)]
 Lc=sum_poly([sc(power(c,i),z) for i,z in enumerate(L0)])
 Lx=ev(L0,x);Qx=ev(q,x)
 Qc=sum_poly([sc(power(c,i),z) for i,z in enumerate(q)])
 D=add(sc(Lc,(x-g)*Qx),sc(mul(mul(k,add(c,[-g])),Qc),-Lx))
 assert D
 D=guard_strip(D,mul(mul(u,add(c,[-g])),Qc))
 print('seven distinct penultimate degree',star,len(D)-1,flush=True)
 E=add([2*(g-x)],sc(mul(k,[F(-2),F(1)]),-g))
 assert len(D)==4 and len(gcdp(D,E))==1 # all silent-eighth projections
 return D

def check_moments(M,D,back,p,t):
 H,F,vals=M
 B0=Bfield(nmod_poly([0,1],p),p,t);E0=B0.cast(Epoly(H))
 assert E0.degree()==H.degree() and E0.leading_coefficient()==1
 for m,e in E0.factor()[1]:
  assert e==1
  B=Bfield(m,p,t)
  U=Tower([B(v) for v in D]);u=U.gen()
  g,a,b,_,_,_,x,q=vals
  g,a,b,x=map(U,(g,a,b,x));q=list(map(U,q))
  c=x-g*u;d=x-g*(2-u if back else 2*u)
  pegs=[a,b,x,c,d]
  T=moment(U,pegs,q)
  det3(T).inv()
 return True
def run():
 p,t=1009,285
 assert isprime(p) and (2*t*t-1)%p==0
 for f in (True,False):
  for M in exact_gamma(f):
   D=exact_tail(f,M)
   for b in (True,False):
    assert check_moments(M,D,b,p,t)
    print('seven distinct profile excluded',f,b,p,t,flush=True)
if __name__=='__main__':run()

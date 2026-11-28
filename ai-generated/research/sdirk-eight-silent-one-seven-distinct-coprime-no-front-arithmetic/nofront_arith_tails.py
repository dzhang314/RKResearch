"""Exact tail guards for the coprime no-active-literal arithmetic rear."""
from shared_arith_projection import *
from exact_guard_cuts import e_sf,guard_coeffs
from shared_silent8_projection import enorm

@lru_cache(None)
def tail(f,i):
 A0,B0,m,ha,hb,a,b,hh,H4,*_=frontdata(f,i)
 # No ordinary active literal: a is actual sole transported at z.
 a=C(a)
 x=1-g;c=x-g*u;d=x-2*g*u;z=g*a
 L=lambda X:sum(p*X**j for j,p in enumerate(Lco))
 px,pc,pd=map(L,(x,c,d))
 k=1+2*u-u*u;H=-2+u+4*u*u-u**3;T=4*u**3-12*u*u+3*u+2
 A=can((x-z)*pc);B=can(k*(c-z)*px)
 F=exdiv(can(A-B),u)
 q1=-F;q0=can(g*B-q1*x)
 R=strip(strip(can(H*(x-z)*pd*(c-z)+T*(d-z)*(2*A-B)),u),g)
 q=lambda X:can(q0+q1*X)
 return R,q0,q1,[g,x-z,px,L(z)]

def guards(f,i):
 R,q0,q1,gg=tail(f,i)
 r=list(map(ef,Vcoeff(R)))
 C,D=guard_coeffs()
 W=list(map(lambda X:ef(Gcoeff(X)),gg))
 PG=[]
 for L in (C,D):
  y=syl(r,list(map(ef,L)));assert y
  z=e_sf(eguard(y,W))
  PG.append(z)
 deg=[z.degree() for z in PG];F=[[(v.degree(),m) for v,m in enorm(z).factor()[1]] for z in PG]
 assert deg==[32,32] and egcd(*PG).degree()==0
 assert F==[[(64,1)],[(40,1),(12,2)]]
 print('no-front arithmetic exact Gauss-tail projections:',f,i,deg,F,'gcd',egcd(*PG).degree(),flush=True)
 return PG

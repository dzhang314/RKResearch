"""Coprime rational profile, separate aggregate at the sole literal silent."""
from literal_shared_pole_late import *
from five_peg_checks import row5_elim
from extra_active import physical_guard

@lru_cache(None)
def patches(front,idx,star):
 A,B,m,ha,hb,H4,qA,qB,q0,q1,*_=phases(front)
 a,b=(A,B) if idx==0 else (B,A)
 L=lambda v:sum(w*v**j for j,w in enumerate(Lco))
 x=1-g;c=x-g*u;d=x-g*(2-u if star else 2*u)
 z=g*expr(b)
 k=1+2*u-u*u
 Q=lambda v:g*term(q0,g)+v*term(q1,g)
 B9=can((x-z)*L(c)*Q(x)-k*(c-z)*L(x)*Q(c))
 F9=exdiv(B9,u)
 if star:
  F8=exdiv(can((x-z)*L(d)*Q(x)-k*(d-z)*L(x)*Q(d)),u-2)
  F8=exdiv(can(F8+F9),u-1)
 else:
  H=-2+u+4*u*u-u**3;T=4*u**3-12*u*u+3*u+2
  R=can(H*(x-z)*L(d)*Q(x)+k*T*(d-z)*L(x)*Q(d))
  F8=exdiv(R,u)
  while True:
   T,R=divmod(F8,u)
   if can(R):break
   F8=can(T)
 U=exact_uc(F9);V=exact_uc(F8)
 G=mon(guarded(gcoeff(can(F9.resultant(F8,1))),physical_guard(front)))
 assert len(G)-1==(34 if star else 73)
 print('sole coprime literal diagonal:',front,idx,star,len(G)-1,flush=True)
 return G,U,V,a,b

def fast_degree_split(G,V):
 # Keep the same root set without squarefree reducing the whole high degree.
 for n in range(len(V)-1,-1,-1):
  if not V[n]:continue
  C=gcdp(G,V[n]);D=mon(guarded(G,[V[n]]))
  if len(D)>1:yield D,n
  G=C
  if len(G)<=1:return
 assert len(G)<=1

def case(front,idx,star,p,t):
 G,U,V,a,b=patches(front,idx,star)
 Z=Bfield(nmod_poly([0,1],p),p,t)
 n=0
 for R,d in fast_degree_split(G,U):
  Md=nmod_poly([int(Z(v).x[0]) for v in R],p)
  assert Md.degree()==len(R)-1
  for J,_ in Md.factor()[1]:
   F=Bfield(J,p,t);gg=F(nmod_poly([0,1],p))
   U0=trim([ev(list(map(F,v)),gg) for v in U])
   V0=[ev(list(map(F,v)),gg) for v in V]
   assert len(U0)==d+1
   U1=gcdp(U0,V0)
   if len(U1)<=1:continue
   W=Tower(U1);g0=W(gg);u0=W.gen()
   x=1-g0;c=x-g0*u0;d0=x-g0*(2-u0 if star else 2*u0)
   E,(A,B,q0,q1)=row5_elim(W,g0,front)
   n+=1
   q1.inv();xi=-g0*q0/q1
   N,_=moments(W,g0,xi,[g0*W(a),x,c,d0],3)
   polyres(W,N,E,3,3).inv()
 assert n
 print('verified sole coprime literal:',front,idx,star,p,n,flush=True)
 return True

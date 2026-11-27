"""Finite linear nodal completion using the actual reverse moment transport."""
from projection import *
from unequal_finite import *
from projection import R,u,g
from equal_detected import h4
from equal_undetected_front import Nested,lagrange,prod_i
from off8_fibers import cramer,multicol
from flint import fq_default_ctx,fq_default_poly_ctx,fmpz_mod_poly_ctx

def kcast(B,j):
 return B(Epoly(j)) if j else B(0)

def br(B,f):
 cf=[JJ(0) for i in range(f.degree(u)+1)]
 for (i,j),v in f.items():cf[i]+=v*G**j
 return trim([kcast(B,j) for j in cf])

def factors(B,E):
 F=fq_default_ctx(modulus=fmpz_mod_poly_ctx(B.p)([int(x) for x in B.M]),fq_type='FQ_NMOD')
 P0=fq_default_poly_ctx(F)
 p=P0([F([int(q) for q in v.x]) for v in E])
 assert p.degree()==len(E)-1
 for m,e in p.factor()[1]:
  cf=[B(nmod_poly([int(t) for t in z.polynomial()],B.p)) for z in m]
  assert cf[-1]==1
  yield cf,e

def IP(D):
 if not D:return []
 U=D[-1].A
 return [sum(U(D[k])/(k-j) for k in range(j+1,len(D))) for j in range(len(D)-1)]

def nodal_map(P,D):
 N=add(mul(P,IP(D)),sc(mul(IP(P),D),-1))
 assert len(N)<=4
 return N+[0]*(4-len(N))

def linear_solve(pegs,g,q):
 B=g.A
 P=list(map(B,Lco));D=list(map(B,nodal(pegs)))
 need=8-len(pegs)
 c0=mul([-g,B(1)],mul(q,q));c0+=[B(0)]*(4-len(c0))
 columns=[nodal_map(P,[B(0)]*j+D) for j in range(need)]
 columns.append(sc(c0,-1));columns[-1]+=[B(0)]*(4-len(columns[-1]))
 R0=nodal_map(P,[B(0)]*need+D)
 M=[list(r) for r in zip(*columns)]
 if need==2:return det([r+[x] for r,x in zip(M,R0)])
 v=det(M)
 iv=v.inv()
 p=[v*iv for v in cramer(M,[-x for x in R0])]
 return p[:3]+[B(1)],p[3]

def repeated_poly(a,n):
 r=[a[-1].A(1)]
 for j in range(n):r=mul(r,a)
 return r

def physical_L(b0):
 return sum_poly([sc(repeated_poly(b0,j),b0[-1].A(v)) for j,v in enumerate(Lco)])

def exact_degrees(H,front,F9,Q0,Q1):
 def true_deg(f):
  ci=[JJ(0)]*(f.degree(u)+1)
  for (i,j),v in f.items():ci[i]+=v*G**j
  return max((i for i,v in enumerate(ci) if v%H),default=-1)
 A,B,r=ends(front,1);ha,hb=(A-1)/2,(B-1-r)/2
 Z0=R.from_dict({(i,0):c for (i,),c in h4(front).items()})
 q0=R.from_dict({(0,i):c for (i,),c in Q0.items()})
 q1=R.from_dict({(0,i):c for (i,),c in Q1.items()})
 K4=(q0+q1*g*u)*Z0-g*(B-A)*ha*hb*Lf(g*u)
 K4=K4.exquo((u-A)*(u-B))
 return true_deg(F9),true_deg(K4)

def diag_models(front,rear,H,pp,tt):
 F9,F8,Q0,Q1,_=raw(front,rear)
 df9,df4=exact_degrees(H,front,F9,Q0,Q1)
 assert df9>0 and df4>0
 B0=Bfield(nmod_poly([0,1],pp),pp,tt);N=B0.cast(Epoly(H))
 assert N.degree()==H.degree() and N.leading_coefficient()==1
 A,C,r=ends(front,1);h_a,h_b=(A-1)/2,(C-1-r)/2
 for f,e in N.factor()[1]:
  assert e==1
  B=Bfield(f,pp,tt);g0=B(nmod_poly([0,1],pp))
  cv=lambda z:kcast(B,JJ(z))
  q0=[kcast(B,Q0),kcast(B,Q1)]
  a,b,ha,hb,rr=map(cv,(A,C,h_a,h_b,r))
  lam=g0*(b-a)*ha*hb
  h4p=[cv(z) for z in pol(h4(front),lambda v:v)]
  R4=add(mul([q0[0],g0*q0[1]],h4p),sc(physical_L([B(0),g0]),-lam))
  R4,rr0=qr(R4,nodal([a,b])); assert not rr0
  assert len(R4)-1==df4,(len(R4)-1,df4,H.degree(),f.degree())
  D9,D8=br(B,F9),br(B,F8)
  assert len(D9)-1==df9,(len(D9)-1,df9,H.degree(),f.degree())
  J0=gcdp(D9,D8)
  if len(J0)<=1:continue
  for P,e0 in factors(B,J0):
   U=Tower(P);u0=U.gen()
   g,a,b,ha,hb,rr,lam=map(U,(g0,a,b,ha,hb,rr,lam))
   q=list(map(U,q0))
   fid=[U(v) for v in R4]
   V=Nested(sc(fid,fid[-1].inv()))
   g,a,b,ha,hb,rr,lam,u0=map(V,(g,a,b,ha,hb,rr,lam,u0))
   q=list(map(V,q));h4p=list(map(V,h4p))
   x=1-g;c=x-g*u0;s=V.gen()
   d=(None if rear is None else x-g*(2-u0 if rear else 2*u0))
   yield V,(g,x,c,d,a,b,s,ha,hb,rr,lam,q,h4p),f.degree()

"""Shared literal, ordinary arithmetic eighth: exact diagonal from fourth and nodal pegs."""
from shared_star_projection import *
from shared_silent8_projection import epow,etry,eexact,pseudo_e
# The symbol v in the shared polynomial context is unused as a centered variable here:
# it denotes the actual gap u.
u=v


def bareiss(A):
 M=[list(r) for r in A];sg=1;n=len(M);old=E(1)
 for k in range(n-1):
  if not M[k][k]:
   q=next((j for j in range(k+1,n) if M[j][k]),None)
   if q is None:return E(0)
   M[k],M[q]=M[q],M[k];sg=-sg
  p=M[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    M[i][j]=eexact(p*M[i][j]-M[i][k]*M[k][j],old)
   M[i][k]=E(0)
  old=p
 return sg*M[-1][-1]

def syl(a,b):
 m,n=len(a)-1,len(b)-1
 M=[[E(0)]*(m+n) for _ in range(m+n)]
 for i in range(n):M[i][i:i+m+1]=a[::-1]
 for i in range(m):M[i+n][i:i+n+1]=b[::-1]
 return bareiss(M)

def coefficients_e(F):
 V={}
 for (i,j,k,l),a in can(F).to_dict().items():
  assert not i and l<=1
  v=V.setdefault(j,[{},{}])[l];v[k]=v.get(k,Q(0))+a
 def p(d):return P([d.get(k,Q(0)) for k in range(max(d,default=-1)+1)])
 return [E(*map(p,V.get(j,[{},{}]))) for j in range(max(V,default=-1)+1)]

def prim(F):
 V=coefficients_e(F)
 G=min((a for a in V if a),key=lambda a:a.degree()).monic()
 for b in V:
  if G.degree()==0:break
  if b and etry(b,G) is None:G=egcd(G,b)
 return G,[eexact(x,G) if x else x for x in V]

def strip(F,a):
 assert F
 while True:
  q,r=div(F,a)
  if r:return F
  F=q

@lru_cache(None)
def build_arith(f,i):
 A,B,m,ha,hb,a,b,hh,H4,*_=frontdata(f,i)
 a,b,hh=map(C,(a,b,hh))
 x=1-g;c=x-g*u;d=x-2*g*u;z=g*b
 k=1+2*u-u*u;H=-2+u+4*u*u-u**3;T=4*u**3-12*u*u+3*u+2
 L=lambda x:sum(p*x**j for j,p in enumerate(Lco))
 pc,pd,px=L(c),L(d),L(x)
 A=can((x-z)*pc);B=can(k*(c-z)*px)
 F=exdiv(can(A-B),u)
 q1=-F;q0=can(g*B-q1*x)
 Q=lambda X:can(q0+q1*X)
 R=strip(can(H*(x-z)*pd*(c-z)+T*(d-z)*(2*A-B)),u)
 phi=exdiv(can(L(g*a)*Q(g*s)*term(H4,s)-hh*Q(g*a)*L(g*s)),s-a)
 D=nodalR([g*a,x,c,d,g*s],q0,q1)
 P0=can(phi.resultant(D,0))
 assert P0
 print('raw arithmetic placements',f,i,R.degrees(),phi.degrees(),D.degrees(),P0.degrees(),flush=True)
 # Only strip factors whose literal nonzero coefficients are guaranteed.
 gs=[g,x-z,px,L(g*a),x-g*a]
 R=strip(R,g)
 P0=strip(strip(P0,g),u)
 qr,A=prim(R);qp,B=prim(P0)
 print('arith primitive R/P',len(A)-1,len(B)-1,qr.degree(),qp.degree(),flush=True)
 C0=pseudo_e(B,A)
 print('arith pseudo E degrees',f,i,[w.degree() for w in C0],flush=True)
 lc=A[-1]
 # Drop only the redundant leading multiplier introduced by pseudo-remainder.
 n,m,j=len(A)-1,len(B)-1,len(C0)-1
 ep=j+n*(m-n+1)-m
 Z=syl(A,C0)
 assert Z and ep>=0
 if ep:Z=eexact(Z,epow(lc,ep))
 print('arith deflated diagonal degree',f,i,Z.degree(),flush=True)
 GG=unef(eguard(Z*lc*qr*qp,list(map(lambda w:ef(Gcoeff(w)),gs))))
 assert len(GG)-1==557
 print('arith guarded projection degree',f,i,len(GG)-1,flush=True)
 return GG,phi,D,R,P0,q0,q1

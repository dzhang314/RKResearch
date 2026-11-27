"""Literal row-five polynomial pair with the prior active Gauss front."""
from one_front_zero import *
from both_front_silent8 import context as old_context
from flint import fmpq_mpoly_ctx
from arithmetic_nonzero import guarded
C0=fmpq_mpoly_ctx.get(['s','y','r','t'])
s,y,rr,tt=C0.gens()
# Small reduced multivariate expressions defined over Q(t,r)[s,y].
def expr(q):
 q=B0(q).v
 return sum(c*rr**i for i,c in enumerate(q.a))+tt*sum(c*rr**i for i,c in enumerate(q.b))

def exact_coefficients(F):
 R={}
 for (i,j,k,l),q in F.to_dict().items():
  H=R.setdefault(j,{}).setdefault(i,[[],[]])
  D=H[l%2]
  D.extend([Q(0)]*(k+1-len(D)));D[k]+=q/2**(l//2)
 z=[]
 for j in range(max(R,default=-1)+1):
  H=R.get(j,{})
  z.append(trim([B0(E(*map(P,H.get(i,([],[]))))) for i in range(max(H,default=-1)+1)]))
 return z

def term(a,v):return sum(expr(q)*v**j for j,q in enumerate(a))

@lru_cache(None)
def duplicate(front,slot):
 F=B0
 cv=lambda x:F(Epoly(JJ(x))) if x else F(0)
 A,B,m=map(cv,ends(front,1));anc=A if slot==0 else B
 ha,hb=(A-1)/2,(B-1-m)/2
 H4=[cv(w) for w in pol(h4(front),lambda q:q)]
 S,AA,e,TA,QA=old_context(F,A,B,m,ha,hb,None,H4)
 J=-F(4)/3+2*(A+B)-2*A*B
 TT=[2-F(4)/3*(A+B)+2*A*B-ev(TA,anc),J]
 AA=[1-2*S[0]-2*S[1]+J*e[0]-ev(QA,anc),J*e[1]]
 assert len(gcdp(TT,AA))==1
 print('chronological r copy affine slopes coprime',front,slot,flush=True)
 return True

@lru_cache(None)
def pair(front,slot):
 F=B0;cv=lambda x:F(Epoly(JJ(x))) if x else F(0)
 A,B,m=map(cv,ends(front,1));R=A if slot==0 else B
 ha,hb=(A-1)/2,(B-1-m)/2
 g=R0/R
 p=[q*g**j for j,q in enumerate(PX)]
 H4=[cv(v) for v in pol(h4(front),lambda q:q)]
 S,AA,e,TA,QA=old_context(F,A,B,m,ha,hb,None,H4)
 tR,aR=ev(TA,R),ev(QA,R)
 # Unscaled normalized physical row-four T and Ah polynomials.
 m0=add([F(-1),F(1)],sc(H4,-2));m1=add([F(0),F(-1),F(1)/2],sc(H4,-2))
 wa=sc(add(sc(m0,B),sc(m1,-1)),1/(B-A));wb=add(m0,sc(wa,-1))
 TT=sum_poly([[F(0),F(0),F(0),F(1),-F(1)/4],sc(H4,2),sc(wa,A**3),sc(wb,B**3)])
 AA=sum_poly([H4,sc(wa,ha),sc(wb,hb)])
 XT,rt=qr(add(TT,sc(H4,-tR)),[-R,F(1)])
 XA,ra=qr(add(AA,sc(H4,-aR)),[-R,F(1)])
 assert not rt and not ra
 aa,bb,rr0=map(expr,(A,B,R))
 pS=term(p,s);h0=term(H4,s)*term(p,y)
 # Normalized moments after the mandatory stage-one strict feed, multiplied by p(s).
 M0=(y-1)*pS-2*h0
 M1=(y*y/2-y)*pS-2*h0
 M2=(y**3/3-y*y)*pS-4*h0/3
 d2=M2-(aa+bb)*M1+aa*bb*M0
 T=(y**3-y**4/4)*pS+expr(2-tR)*h0+(aa+bb)*M2-aa*bb*M1+s*d2-term(XT,s)*(y-rr0)*term(p,y)
 J=expr(1-aR)*h0+expr(S[0])*M0+expr(S[1])*M1+term(e,s)*d2-term(XA,s)*(y-rr0)*term(p,y)
 # Reduction modulo t²=1/2 and L4(r)=0 is necessary before exact division.
 FF,J0=map(exact_coefficients,(T,J))
 def Qfactor(K):
  K=list(K);U=[[] for _ in range(len(K)-1)]
  for j in range(len(U)-1,-1,-1):
   U[j]=K[j+1]
   K[j]=add(K[j],[F(0)]+U[j])
  assert not K[0]
  return U
 TF,AF=Qfactor(FF),Qfactor(J0)
 print('front-pair y degrees',front,slot,len(TF)-1,len(AF)-1,flush=True)
 return TF,AF,p,H4

def substitute(F,co,x):
 return [ev(list(map(F,t)),x) for t in co]

@lru_cache(None)
def project(front,slot):
 TF,AF,p,H4=pair(front,slot)
 def cv(x):return B0(Epoly(JJ(x))) if x else B0(0)
 A,B,_=map(cv,ends(front,1))
 T=sum(term(w,s)*y**j for j,w in enumerate(TF))
 U=sum(term(w,s)*y**j for j,w in enumerate(AF))
 G=exact_coefficients(T.resultant(U,1))
 assert len(G)==1 and G[0]
 G=guarded(G[0],[[B0(-A),B0(1)],[B0(-B),B0(1)],p,H4])
 M=mon(G)
 print('front pair exact row-four projection',front,slot,len(M)-1,flush=True)
 print('degree-leading branch gcds',len(gcdp(M,TF[-1]))-1,len(gcdp(M,AF[-1]))-1,flush=True)
 return M

@lru_cache(None)
def split_project(front,slot):
 G=project(front,slot)
 TF,AF,_,_=pair(front,slot)
 cv=lambda x:B0(Epoly(JJ(x))) if x else B0(0)
 R=cv(ends(front,1)[slot])
 at=lambda fs:sum_poly([sc(q,R**j) for j,q in enumerate(fs)])
 J=gcdp(G,gcdp(at(TF),at(AF)))
 M=guarded(G,[J])
 assert len(J)==3 and len(M)==8
 print('front projection removes only padded y=r via split',front,slot,len(J)-1,len(M)-1,flush=True)
 return [(mon(J),True),(mon(M),False)]

"""Exact u projection for the coprime extra shared physically silent eighth."""
from literal_shared_pole_late import *
from flint import fmpq_mpoly_ctx

CX=fmpq_mpoly_ctx.get(['y','s','u','t'])
y,s,u,t=CX.gens()
L4=lambda X:sum(v*X**i for i,v in enumerate(Lco))
LT=t*t-CX.constant(Q(1)/2)
p0=L4
B0=F2
def C(M):
 if isinstance(M,int):M=CX.constant(M)
 return M%LT
def div(F,D):
 A,B=divmod(F,D)
 return C(A),C(B)
def exdiv(F,D):
 A,B=div(F,D);assert not B
 return A
def E0(v):
 a=F2(v).v
 return a.a[0]+t*a.b[0]
def term0(ps,w):return sum(E0(v)*w**i for i,v in enumerate(ps))
def termr(ps,w):return term0(ps,w)
def ats(F):
 return C(sum(a*s**(i+j)*u**k*t**m for (i,j,k,m),a in F.to_dict().items()))
def bsg(F):
 T={}
 for (i,j,k,l),v in C(F).to_dict().items():
  assert not i and l<=1
  e=E(v,0) if not l else E(0,v)
  d=T.setdefault(j,{});d[k]=d.get(k,B0(0))+B0(e)
 return [trim([T.get(j,{}).get(k,B0(0)) for k in range(max(T.get(j,{}),default=-1)+1)])
         for j in range(max(T,default=-1)+1)]
def bg(F):
 Q=bsg(F);assert len(Q)<=1
 return Q[0] if Q else []
def ef(a):
 return E(P([v.v.a[0] for v in a]),P([v.v.b[0] for v in a]))
def unef(a):return [F2(a.coeff(j)) for j in range(a.degree()+1)]
def enorm(a):
 return a.a*a.a-a.b*a.b/2
def red_e(a,p,t):
 def val(v):return int(v.p)*pow(int(v.q),-1,p)
 return nmod_poly([(val(a.a[j])+t*val(a.b[j])) % p for j in range(a.degree()+1)],p)
def red_coprime(a,b):
 for p,t in ((1103,161),(1129,203),(1559,529)):
  try:
   x,y=red_e(a,p,t),red_e(b,p,t)
   if x.degree()==a.degree() and y.degree()==b.degree() and x.gcd(y).degree()==0:return True
  except (ValueError,ZeroDivisionError):
   pass
 return False
def etry(a,b):
 m=enorm(b);n=a*E(b.a,-b.b)
 c,cr=divmod(n.a,m);d,dr=divmod(n.b,m)
 return None if cr or dr else E(c,d)
def eexact(a,b):
 z=etry(a,b)
 assert z is not None
 return z
def egcd(a,b):
 if not a:return b.monic() if b else b
 if not b:return a.monic()
 if min(a.degree(),b.degree())<=0 or red_coprime(a,b):return E(1)
 if a.degree()<b.degree():a,b=b,a
 if a.degree()>100 and b.degree()<70:
  if etry(a,b) is not None:return b.monic()
  normb=enorm(b);R0=E(normb/normb[normb.degree()])
  d=enorm(a%R0).gcd(normb)
 else:d=enorm(a).gcd(enorm(b))
 if d.degree()<=0:return E(1)
 R=E(d/d[d.degree()])
 return R.gcd(a%R).gcd(b%R)
def epow(a,k):
 z=E(1)
 while k:
  if k&1:z=z*a
  k//=2
  if k:a=a*a
 return z
def residue_valuation(a,b):
 for p,t in ((1103,161),(1129,203),(1559,529)):
  try:
   A,B=red_e(a,p,t),red_e(b,p,t)
   if A.degree()!=a.degree() or B.degree()!=b.degree():continue
   n=0
   while A.degree()>=B.degree():
    C,D=divmod(A,B)
    if D:break
    A=C;n+=1
   if n:return n
  except (ValueError,ZeroDivisionError):
   continue
 return 1
def strip_one(a,b):
 if not b or b.degree()<=0:return a
 while a.degree()>0:
  C=egcd(a,b)
  if C.degree()==0:break
  j=residue_valuation(a,C)
  if j>1:
   Z=etry(a,epow(C,j))
   if Z is not None:a=Z;continue
  a=eexact(a,C)
 return a
def norm_irreducible(b):
 m=enorm(b)
 f=m.factor()[1]
 return len(f)==1 and f[0][1]==1 and f[0][0].degree()==m.degree()
def eguard(a,bs):
 prev=[]
 for b in bs:
  if b.degree()>50 and prev:
   for c in prev:b=strip_one(b,c)
  if b.degree()>25 and a.degree()>100 and norm_irreducible(b):
   while True:
    j=residue_valuation(a,b)
    Z=etry(a,epow(b,j))
    if Z is not None:a=Z;continue
    if j>1:
     Z=etry(a,b)
     if Z is not None:a=Z;continue
    break  # b is irreducible over Q(t) since its rational norm is irreducible.
  else:a=strip_one(a,b)
  prev.append(b)
 return a.monic()
def pseudo_e(a,b):
 lc=b[-1]
 while len(a)>=len(b):
  m=len(a)-len(b);x=a[-1]
  a=[v*lc-(b[i-m]*x if m<=i<m+len(b) else E(0)) for i,v in enumerate(a)]
  while a and not a[-1]:a.pop()

 return a

def sylvester_e(a,b):
 m,n=len(a)-1,len(b)-1
 A=[[E(0)]*(m+n) for _ in range(m+n)]
 for i in range(n):A[i][i:i+m+1]=a[::-1]
 for i in range(m):A[i+n][i:i+n+1]=b[::-1]
 return det(A)

@lru_cache(None)
def profile(f,i):
 A,B,m,ha,hb,a,b,hh,*_=frontdata(f,i)
 a,b=map(E0,(a,b))
 k=1+2*u-u*u
 D=C(1+b-k*(u-2)/2)
 X=D-1;C9=X-u
 def P4(v):return C(sum(w*D**(4-j)*v**j for j,w in enumerate(Lco)))
 Px,Pc,Pa,Py=map(P4,(X,C9,a,y))
 AA=C((u-2)*Pc)
 BB=C((2*u+k*(u-2))*Px)
 F9=exdiv(C(AA-BB),u)
 q0=C(BB+F9*X);q1=-F9
 Qstar=lambda v:C(q0+q1*v)
 Qa,Qb=Qstar(a),Qstar(b)
 Q0=C(Pa*Qstar(y));P=C(E0(hh)*Qa*Py)
 guards=list(map(bg,[u,k,u-2,D,X-a,C9-a,Px,Pc,Pa,q1,Qa,Qb,AA,BB,C(Py.resultant(Qstar(y),0))]))
 return Q0,P,guards,bg(D),bg(q0),bg(q1),Py

@lru_cache(None)
def front_polys(f,i):
 A,B,m,ha,hb,a,b,hh,H4,L0,e,tau,ah,HS,XT,XA,DT,DA,T4,A4=frontdata(f,i)
 A,B,a=map(E0,(A,B,a))
 H=term0(H4,s);Q0,P,*_=profile(f,i)
 U=C(H*ats(Q0)-ats(P))
 Phi=exdiv(U,s-a)
 m0=y-1;m1=y*y/2-y;m2=y**3/3-y*y
 J=m2-(A+B)*m1+A*B*m0
 T0=C(y**3-y**4/4+(A+B)*m2-A*B*m1+s*J)
 A0=C(E0(L0[0])*m0+E0(L0[1])*m1+term0(e,s)*J)
 T1=C(H*(term0(DT,s)-E0(tau))-term0(exact_uc_y(XT),s)*(y-a))
 A1=C(H*(term0(DA,s)-E0(ah))-term0(exact_uc_y(XA),s)*(y-a))
 FT=exdiv(C(H*T0*Q0+T1*P),y-a)
 FA=exdiv(C(H*A0*Q0+A1*P),y-a)
 FT,FTR=div(FT,y-s);FA,FAR=div(FA,y-s)
 assert not C(FTR-ats(T0)*Phi) and not C(FAR-ats(A0)*Phi)
 return Phi,FT,FA

@lru_cache(None)
def project(f,i):
 Phi,FT,FA=front_polys(f,i)
 _,_,guards,*_=profile(f,i)
 E=C(FT.resultant(FA,0))
 assert E and not E.degrees()[0]
 print('shared silent8 front residual degrees',f,i,E.degrees(),flush=True)
 X=list(map(ef,bsg(Phi)));Y=list(map(ef,bsg(E)))
 assert len(X)==4
 Z=pseudo_e(Y,X)
 print("shared silent8 pseudo degrees",f,i,[a.degree() for a in Z],flush=True)
 Top=X[-1]
 # Retain the full pseudo-remainder, including all its contents.
 Rg=sylvester_e(X,Z)
 assert Rg
 n=len(X)-1;m=len(Y)-1;j=len(Z)-1
 extra=j+n*(m-n+1)-m
 assert extra>=0
 if extra:Rg=eexact(Rg,epow(Top,extra))
 assert Rg.degree()==1245
 print('shared silent8 deflated projection degree',f,i,Rg.degree(),flush=True)
 N=unef(eguard(Top*Rg,list(map(ef,guards))))
 assert len(N)-1==757
 print('shared literal silent8 exact gap projection',f,i,len(N)-1,flush=True)
 return N,Phi,FT,FA

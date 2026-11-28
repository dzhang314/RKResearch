"""Centered active rear star, actual fourth as the fifth ordinary nodal peg."""
from literal_shared_pole_front import *
from extra_active import bezout
from shared_silent8_projection import ef,unef,eguard,egcd,sylvester_e
from flint import fmpq_mpoly_ctx

CX=fmpq_mpoly_ctx.get(['s','v','g','t'])
s,v,g,t=CX.gens()
LT=t*t-CX.constant(Q(1)/2)
def can(M):
 if isinstance(M,int):return CX.constant(M)
 return M%LT
def div(M,D):
 q,r=divmod(M,D);return can(q),can(r)
def exdiv(M,D):
 q,r=div(M,D);assert not r
 return q
def C(a):
 z=F2(a).v
 return z.a[0]+t*z.b[0]
def term(a,X):return sum(C(w)*X**j for j,w in enumerate(a))
def centered(F):
 ans=CX.constant(0)
 for (j,k,m,n),a in can(F).to_dict().items():
  assert k%2==0
  ans+=a*s**j*v**(k//2)*g**m*t**n
 return ans
def Vcoeff(F):
 T={}
 for (i,j,k,l),a in can(F).to_dict().items():
  assert not i
  D=T.setdefault(j,{})
  D[k]=D.get(k,F2(0))+F2(E(a) if not l else E(0,a))
 return [trim([T.get(j,{}).get(k,F2(0)) for k in range(max(T.get(j,{}),default=-1)+1)])
         for j in range(max(T,default=-1)+1)]
def Gcoeff(F):
 A=Vcoeff(F);assert len(A)<=1
 return A[0] if A else []

def Scoeff(F):
 T={}
 for (i,j,k,l),a in can(F).to_dict().items():
  assert not j
  D=T.setdefault(i,{})
  D[k]=D.get(k,F2(0))+F2(E(a) if not l else E(0,a))
 return [trim([T.get(i,{}).get(k,F2(0)) for k in range(max(T.get(i,{}),default=-1)+1)])
         for i in range(max(T,default=-1)+1)]

def check_post(F,A,B):
 n=F.degrees()[1]
 return can(sum(a*s**i*A**j*B**(n-j)*g**k*t**l for (i,j,k,l),a in F.to_dict().items()))

def newton(pegs,n):
 R=[CX.constant(1)]+[CX.constant(0)]*n
 A=[]
 for y0 in pegs:
  R=list(R)
  for j in range(1,n+1):R[j]=can(R[j]+y0*R[j-1])
  A.append(list(R))
 return A

def detR(A):
 n=len(A)
 @lru_cache(None)
 def fi(i,mask):
  if not mask:return CX.constant(1)
  out=CX.constant(0);sg=1
  for j in range(n):
   if mask>>j&1:
    if A[i][j]:out+=sg*can(A[i][j]*fi(i+1,mask^(1<<j)))
    sg=-sg
  return can(out)
 return fi(0,(1<<n)-1)

def nodalR(pts,q0,q1):
 H=newton(pts,7);aa=bezout()
 Q=[can(q0*q0),can(2*q0*q1),can(q1*q1)]
 R=[can(sum(Q[j]*C(aa[j][k]) for j in range(3) if k<len(aa[j]))) for k in range(4)]
 E=[]
 for i in range(5):
  row=[can(sum(Lco[k]*H[i][k+j-i] for k in range(5) if k+j>=i)) for j in range(4)]
  row.append(can(sum(R[k]*H[i][k-i] for k in range(i,4))))
  E.append(row)
 return detR(E)

@lru_cache(None)
def build(f,i):
 A,B,m,ha,hb,a,b,hh,H4,*_=frontdata(f,i)
 a,b,hh=map(C,(a,b,hh))
 x=1-g;mid=x-g;c=mid-g*v;d=mid+g*v;z=g*b
 k=2-v*v
 L=lambda x:sum(p*x**j for j,p in enumerate(Lco))
 pc,pd,px=L(c),L(d),L(x)
 T=can(k*px*(c-z)*(d-z))
 S=can((x-z)*(pc*(d-z)+pd*(c-z)))
 q1=can(2*T-S);q0=can(2*g*T-q1*x)
 Q=lambda X:can(q0+q1*X)
 R0=can(q1-exdiv(can((x-z)*(pd*(c-z)-pc*(d-z))),v))
 R=centered(exdiv(R0,v*v-1))
 A,B=Vcoeff(R);assert len(A)==len(B)==7
 guards=list(map(Gcoeff,[g,x-z,px,L(g*a),x-g*a]))
 common=mon(guarded(gcdp(A,B),guards))
 print('centered star affine gap',f,i,len(A)-1,len(B)-1,'exception',len(common)-1,flush=True)
 assert len(common)==1
 P0,P1=-term(A,g),term(B,g)
 def get(X):return check_post(centered(can(X)),P0,P1)
 read=get(L(g*a)*Q(g*s)*term(H4,s)-hh*Q(g*a)*L(g*s))
 phi=exdiv(read,s-a)
 det=nodalR([g*a,x,c,d,g*s],q0,q1)
 D=get(det)
 print('exact centered star fourth/nodal degrees',f,i,phi.degrees(),D.degrees(),flush=True)
 # Return gauge, front projection and all known physical guards.
 cop=sum(w*(-q0)**j*q1**(4-j) for j,w in enumerate(Lco))
 extras=[q1,cop,Q(x),Q(c)*Q(d),Q(z),Q(g*a),pc*pd,(c-z)*(d-z),(c-g*a)*(d-g*a),v*v,v*v-1,2-v*v]
 W=[*guards,B,*list(map(lambda X:Gcoeff(get(X)),extras))]
 S=unef(eguard(sylvester_e(list(map(ef,Scoeff(phi))),list(map(ef,Scoeff(D)) )),list(map(ef,W))))
 assert len(S)-1==51
 print('exact centered star candidate diagonal degree',f,i,len(S)-1,flush=True)
 return S,phi,D,A,B,centered(q0),centered(q1)

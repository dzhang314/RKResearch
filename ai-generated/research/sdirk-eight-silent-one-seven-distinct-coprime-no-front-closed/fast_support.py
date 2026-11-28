"""Fast exact diagonal division over integral sqrt(2) coordinates."""
from regular_support import *
from exact_crt import height
from flint import fmpz_poly
from math import gcd

def int_group(A):
 _,_,(r,)=height([A])
 return fmpz_poly([a for a,b in r]),fmpz_poly([b for a,b in r])

def primitive(V):
 A,B=V
 d=gcd(int(A.content()),int(B.content()))
 assert d
 return (A//d,B//d) if d>1 else (A,B)

def prove_quotient(A,V):
 # A,V in Z[w][X], w^2=2. Divide A bar(V) by the primitive integer
 # norm of V; a zero remainder in each coordinate proves divisibility
 # in Q(w)[X], and the scalar content has no effect on roots.
 a,b=A;v,w=V
 n=v*v-2*w*w
 assert n
 c=n.content();n=n//c
 x0=a*v-2*b*w;x1=b*v-a*w
 q,r=divmod(x0,n)
 if r:return None
 z,r=divmod(x1,n)
 if r:return None
 assert q*n==x0 and z*n==x1
 return primitive((q,z))

def int_E(A):
 a,b=A
 return E(P(list(a)),P([2*x for x in b]))

def red_int(A,p,t):
 a,b=A
 A=nmod_poly([int(k)%p for k in a],p)
 B=nmod_poly([int(k)%p for k in b],p)
 return A+2*t*B

def mod_valuation(A,Z,p,t):
 N=red_int(A,p,t);D=red_e(Z,p,t)
 if not D or D.degree()<=0:return 0
 if D.degree()!=Z.degree() or N.degree()!=max(x.degree() for x in A):
  return N.degree()//D.degree()
 n=0
 while N.degree()>=D.degree():
  Q,R=divmod(N,D)
  if R:break
  n+=1
  N=Q
 return n

def split_g_fast(f,i,A,p=1103,t=161):
 parts,G0,R,Ph,Zp=support(f,i)
 W=primitive(int_group(A));rootdeg=A.degree()
 for B,flags in [(b,['literal-guard']) for b in G0]+parts:
  if B.degree()<=0:continue
  B=e_sf(B)
  # Candidate exponents can come from a reduction, but no such
  # exponent is ever used without a verified exact integer quotient.
  for Z in separate_components(B):
   m=mod_valuation(W,Z,p,t)
   while m>0:
    V=int_group(epow(Z,m))
    Q0=prove_quotient(W,V)
    if Q0 is not None:
     W=Q0
     print('exact integer Γ division',f,i,Z.degree(),flags,m,flush=True)
     break
    m-=1
 H=int_E(W).monic()
 print('exact integer regular Γ support',f,i,rootdeg,H.degree(),flush=True)
 return H,parts

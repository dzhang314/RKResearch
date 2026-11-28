#!/usr/bin/env python3
import sympy as S
from time import monotonic
from sympy.polys.rings import ring
u0=S.symbols('u')
Q=u0**3-3*u0**2+S.Rational(3,4)*u0+S.Rational(1,2)
assert S.Poly(Q,u0).is_irreducible
K=S.QQ.algebraic_field((S.Poly(Q,u0),u0));R,V,D=ring('v,D',K);u=K.unit
one=R.one;zero=R.zero
cst=lambda a,b=1:K.convert(S.Rational(a,b))
t0=monotonic()
def now(*a):print(round(monotonic()-t0,2),*a,flush=True)
def mul(P,Q):
 out=[zero for _ in range(len(P)+len(Q)-1)]
 for i,p in enumerate(P):
  for j,q in enumerate(Q):out[i+j]+=p*q
 return out
def tower(SD,M,input,moments,P4,phase,A):
 Y=SD.gens[0];Z=SD.zero;O=SD.one
 def trim(U):
  while U and not U[-1]:U=U[:-1]
  return U
 def ov(P):
  a=[Z]*((P.degree(V)+1) if P else 0)
  for (i,j),k in P.items():a[i]+=Y**j*k
  return trim([x%M for x in a])
 def inv(a):
  s,t,c=a.gcdex(M)
  assert c==O and a*s+t*M==O
  return s%M
 def rem(P,Q):
  P=list(P);d=inv(Q[-1])
  while len(P)>=len(Q):
   i=len(P)-len(Q);v=(P[-1]*d)%M
   for j,c in enumerate(Q):P[i+j]=(P[i+j]-v*c)%M
   P=trim(P)
  return P
 def gcd(P,Q):
  while Q:P,Q=Q,rem(P,Q)
  if not P:return []
  d=inv(P[-1]);return [(p*d)%M for p in P]
 F=gcd(ov(input[0]),ov(input[1]))
 if len(F)==1:return now(phase,'no rear for D degree',M.degree())
 assert len(F)==2 and F[1]==O
 w=-F[0]
 def at(f):
  v=Z
  for y in reversed(ov(f)):v=(v*w+y)%M
  return v
 m0,m1,*_=[at(c) for c in moments]
 if not m0:
  assert M.degree() in ((5,) if phase=='star' else (2,8))
  return now(phase,'D degree',M.degree(),'rank drop M0')
 b=(Y*m1*inv(m0))%M
 A=at(A)
 def native(e): return e.f if isinstance(e,E) else SD(e)
 class E:
  def __init__(self,f):self.f=native(f)%M
  def __add__(a,b):return E(a.f+native(b))
  __radd__=__add__
  def __neg__(a):return E(-a.f)
  def __sub__(a,b):return E(a.f-native(b))
  def __rsub__(a,b):return E(native(b)-a.f)
  def __mul__(a,b):return E(a.f*native(b))
  __rmul__=__mul__
  def __pow__(a,n):
   if n==0:return E(O)
   if n%2==0:return (a*a)**(n//2)
   return a*(a**(n-1))
  def __bool__(a):return bool(a.f)
 a,b,D0,v=E(A),E(b),E(Y),E(w)
 assert sum((E(at(z))*b**i for i,z in enumerate(P4)),E(0))
 def L(c):return 70*c**4-140*D0*c**3+90*D0**2*c*c-20*D0**3*c+D0**4
 def L3(c):return c**3-cst(3,2)*D0*c*c+cst(3,5)*D0**2*c-cst(1,20)*D0**3
 La=L(a)
 assert La
 # Arithmetic c=D-1-2v; in star adjoin W²=v and use c=D-2+W.
 # Pair operations over the D quotient; no assumption that adjoining W remains a field.
 class Pair:
  def __init__(self,a,b=0):self.a=E(a);self.b=E(b)
  def __neg__(a):return Pair(-a.a,-a.b)
  def __add__(a,b):
   b=prom(b);return Pair(a.a+b.a,a.b+b.b)
  __radd__=__add__
  def __sub__(a,b):return a+(-prom(b))
  def __rsub__(a,b):return prom(b)+(-a)
  def __mul__(a,b):
   b=prom(b);return Pair(a.a*b.a+v*a.b*b.b,a.a*b.b+a.b*b.a)
  __rmul__=__mul__
  def __pow__(a,n):
   if n==0:return Pair(1)
   if n%2==0:return (a*a)**(n//2)
   return a*(a**(n-1))
  def norm(a):return a.a*a.a-v*a.b*a.b
 def prom(a):return a if isinstance(a,Pair) else Pair(a)
 c=Pair(D0-2,1) if phase=='star' else Pair(D0-1-2*v)
 # Use Pair on the left when combining with E, keeping its algebra generic.
 def Lz(c):
  return 70*c**4-c**3*(140*D0)+c**2*(90*D0**2)-c*(20*D0**3)+D0**4
 def L3z(c):
  return c**3-c**2*(cst(3,2)*D0)+c*(cst(3,5)*D0**2)-D0**3*cst(1,20)
 def ev(P,t):return sum((t**i*q for i,q in enumerate(P)),prom(0) if isinstance(t,Pair) else E(0))
 def J(P,k,t):return sum((t**(i+k+1)*(q*cst(1,i+k+1)) for i,q in enumerate(P)),prom(0) if isinstance(t,Pair) else E(0))
 def gates(P):
  eta=a*ev(P,a)-J(P,1,a)
  g=La*(a*(J(P,0,b)-ev(P,b))+b*ev(P,b)-J(P,1,b))-L(b)*eta
  da=a*a*ev(P,a)-J(P,2,a)
  db=b*b*ev(P,b)+a*a*(J(P,0,b)-ev(P,b))-J(P,2,b)
  dc=(c*c*ev(P,c)+(J(P,1,c)-c*ev(P,c))*(a+b)-(J(P,0,c)-ev(P,c))*(a*b)-J(P,2,c))*La+Lz(c)*(eta*(a+b))
  gate=(Lz(c)*L3(b)-L3z(c)*L(b))*(La*da)+(L3z(c)*La-Lz(c)*L3(a))*(La*db)+dc*(L3(a)*L(b)-L3(b)*La)
  return g,gate
 R0=[E(1+u),E(-2-u),E(1)]
 P0=[E(-1),E(2),E(cst(-1,2))]
 g0,f0=gates(P0);g1,f1=gates(R0)
 h=f1*g0-f0*g1
 assert h.norm() and M.degree() in ((15,) if phase=='star' else (4,26))
 now(phase,'D degree',M.degree(),'no graph lambda; nonzero elimination norm')
def prog(phase):
 A=one*(1+2*u)
 if phase=='star':
  P4=mul(mul([-A,one],[-(D-1),one]),[(D-2)**2-V,-2*(D-2),one])
 else:
  P4=[one]
  for h in [A,D-1,D-1-V,D-1-2*V]:P4=mul(P4,[-h,one])
 m0,m1,m2,m3=[sum((q*D**j*cst(1,i+j+1) for j,q in enumerate(P4)),zero) for i in range(4)]
 f1=m0*m2-m1*m1;f2=m0*m3-m1*m2
 def guard(f):
  while f and all(j>0 for i,j in f.monoms()):f=f//D
  return f
 fs=[guard(f1),guard(f2)]
 r=fs[0].resultant(fs[1])
 now(phase,'moment resultant degree',r.degree())
 SD=r.ring;x=SD.gens[0]
 factors=r.factor_list()[1]
 assert [(q.degree(),e) for q,e in factors]==([(1,4),(5,1),(15,1)] if phase=='star' else [(1,8),(2,1),(4,1),(8,1),(26,1)])
 f=SD.one
 for q,e in factors:f*=q**e
 assert f==r.monic()
 now(phase,'factor degrees',[(q.degree(),e) for q,e in factors])
 for q,e in factors:
  if q==x:continue
  tower(SD,q,fs,[m0,m1,m2,m3],P4,phase,A)
for phase in ('star','arithmetic'):prog(phase)

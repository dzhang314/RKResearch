"""Exact double norm: b H4-algebra and r old-affinity cubic.

The only denominators in the b power basis are powers of h=lc(H4).
All reductions below are literal monic r and cleared quartic b reads.
"""
import sympy as S
from flint import fmpq_poly, fmpq
from itertools import permutations
z,X=S.symbols('z X')
J4=lambda y:42*y**4-84*y**3+56*y*y-14*y+1
J5=lambda y:(2*y-1)*(66*y**4-132*y**3+84*y*y-18*y+1)
H,rm=S.div(J5(z*X)*J4(z)-J4(z*X)*J5(z),X-1,X)
assert rm==0
assert S.expand(H).coeff(X,4)==S.expand(132*z**5*J4(z))
H=S.Poly(H,X,domain=S.QQ[z]); H0=[S.Poly(H.nth(i),z,domain=S.QQ) for i in range(5)]
# One shared h^d denominator in the quartic b algebra.
def fp(p):return fmpq_poly([fmpq(int(p.nth(i).p),int(p.nth(i).q)) for i in range(p.degree()+1)]) if not p.is_zero else fmpq_poly(0)
def sp(p):return sum(S.Rational(int(c.numer()),int(c.denom()))*z**i for i,c in enumerate(p))
h=[fp(t) for t in H0]; hl=h[4]; one=fmpq_poly([1]); zero=fmpq_poly(0); hp=[one]
def hpw(d):
 while len(hp)<=d:hp.append(hp[-1]*hl)
 return hp[d]
class B:
 def __init__(self,vec,d=0):
  self.v=tuple(vec);self.d=d
 @staticmethod
 def c(t):
  if isinstance(t,B): return t
  if not isinstance(t,fmpq_poly):t=fmpq_poly([t])
  return B([t,zero,zero,zero])
 @staticmethod
 def simp(vec,d):
  while d:
   qs=[divmod(p,hl) for p in vec]
   if any(r for q,r in qs): break
   vec,d=[q for q,r in qs],d-1
  return B(vec,d)
 def __neg__(self):return B([-p for p in self.v],self.d)
 def __add__(self,t):
  t=B.c(t);d=max(self.d,t.d)
  return B.simp([a*hpw(d-self.d)+b*hpw(d-t.d) for a,b in zip(self.v,t.v)],d)
 __radd__=__add__
 def __sub__(self,t):return self+-B.c(t)
 def __rsub__(self,t):return B.c(t)+-self
 def __mul__(self,t):
  t=B.c(t);v=[zero for j in range(7)]
  for i,a in enumerate(self.v):
   for j,b in enumerate(t.v):
    if a and b:v[i+j]=v[i+j]+a*b
  d=self.d+t.d
  for i in (6,5,4):
   a=v[i]
   if a:
    v=[p*hl for p in v]
    for j in range(4):v[i-4+j]=v[i-4+j]-a*h[j]
    v[i]=zero;d+=1
  return B.simp(v[:4],d)
 __rmul__=__mul__
 def __pow__(self,n):
  ans=B.c(1)
  for i in range(n):ans=ans*self
  return ans
b=B([zero,one,zero,zero])
hc=[B([h[i],zero,zero,zero],1) for i in range(4)]
c2=hc[3]+b;c1=hc[2]+b*c2;c0=hc[1]+b*c1
# a(r)=r³+am2 r²+am1 r+am0
am=[-9*c0,-fmpq(1,2)*(9*c0-6*c1),-fmpq(1,2)*(c0-c1+3*c2)]
class E:
 def __init__(self,cs):self.cs=cs
 @staticmethod
 def c(t):return t if isinstance(t,E) else E([B.c(t),B.c(0),B.c(0)])
 def __neg__(self):return E([-c for c in self.cs])
 def __add__(self,t):return E([a+b for a,b in zip(self.cs,E.c(t).cs)])
 __radd__=__add__
 def __sub__(self,t):return self+-E.c(t)
 def __rsub__(self,t):return E.c(t)+-self
 def __mul__(self,t):
  t=E.c(t);v=[B.c(0) for _ in range(5)]
  for i,a in enumerate(self.cs):
   for j,b in enumerate(t.cs):v[i+j]+=a*b
  for i in [4,3]:
   for j in range(3):v[i-3+j]-=v[i]*am[j]
  return E(v[:3])
 __rmul__=__mul__
 def __pow__(self,n):
  t=E.c(1)
  for i in range(n):t=t*self
  return t
r=E([B.c(0),B.c(1),B.c(0)])
U=r*(r+6)*E.c(c1)-r**3-(r+6)**2*E.c(c0)
na=U-r**3;nb=5*U-r**3
M=2*na*nb*((4*r+3)*E.c(b)-r)-10*(2*r+3)*na**2*E.c(b-1)-4*U*nb*r*E.c(b)
cols=[(M*r**j).cs for j in range(3)]
det=B.c(0)
for p in permutations(range(3)):
 sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
 det+=sign*cols[0][p[0]]*cols[1][p[1]]*cols[2][p[2]]
assert det.d==11 and [a.degree() for a in det.v]==[81,82,83,84]
T=S.Poly.from_dict({(i,):sp(p) for i,p in enumerate(det.v)},X,domain=S.QQ[z])
# Independent scalar specializations check the custom b power-basis norm.
# Here SymPy computes a direct univariate r resultant before reducing b.
rvar=S.Symbol('r')
for zv in (S.Rational(2,5),S.Rational(1,3),S.Rational(-1,3)):
    hs=S.Poly(H.as_expr().subs(z,zv),X,domain=S.QQ)
    hn=hs.monic()
    d2=hn.nth(3)+X; d1=hn.nth(2)+X*d2; d0=hn.nth(1)+X*d1
    Ac=rvar**3-(d0-d1+3*d2)*rvar*rvar/2-(9*d0-6*d1)*rvar/2-9*d0
    Uc=rvar*(rvar+6)*d1-rvar**3-(rvar+6)**2*d0
    Wa=Uc-rvar**3; Wb=5*Uc-rvar**3
    Mc=2*Wa*Wb*((4*rvar+3)*X-rvar)-10*(2*rvar+3)*Wa**2*(X-1)-4*Uc*Wb*rvar*X
    aa=S.Poly(Ac,rvar,domain=S.QQ[X]); bb=S.Poly(Mc,rvar,domain=S.QQ[X])
    check=S.Poly(aa.resultant(bb.rem(aa)),X,domain=S.QQ).rem(hn)
    stored=S.Poly(T.as_expr().subs(z,zv)/hs.LC()**det.d,X,domain=S.QQ)
    assert stored==check

g=S.Poly(S.gcd_list(T.all_coeffs(),z),z,domain=S.QQ)
assert g.monic()==S.Poly(z**28,z,domain=S.QQ)
T=S.Poly.from_dict({(i,): S.cancel(T.nth(i)/g.as_expr()) for i in range(T.degree()+1)},X,domain=S.QQ[z])
D=S.Poly(H.resultant(T),z,domain=S.QQ)
assert D.degree()==239
fs=D.factor_list()[1]
E4=66*z**4-144*z**3+108*z**2-32*z+3
assert S.expand(J5(z)+J4(z)-2*z*E4)==0
assert sorted((p.degree(),e) for p,e in fs)==[(1,15),(4,6),(4,11),(156,1)]
assert next(p for p,e in fs if p.degree()==1).monic()==S.Poly(z,z,domain=S.QQ)
assert next(p for p,e in fs if e==6).monic()==S.Poly(E4,z,domain=S.QQ).monic()
assert next(p for p,e in fs if e==11).monic()==S.Poly(J4(z),z,domain=S.QQ).monic()
D156=next(p for p,e in fs if p.degree()==156)
K=D156.monic()
assert K.is_irreducible
f,g=H,T
for j in (2,1):
    q,r0=f.pdiv(g)
    assert r0.degree()==j and f*g.LC()**(f.degree()-g.degree()+1)==q*g+r0
    f,g=g,r0
q0,q1=(S.Poly(g.nth(i),z,domain=S.QQ).rem(K) for i in (0,1))
assert S.gcd(q1,K).is_one
print("Exact double norm (including three independent scalar audits): irreducible degree156 after live origin/Jacobi guards; unique later clock ratio",flush=True)

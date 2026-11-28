"""Exact immediate origin gate: degree-four b and monic old-affinity r algebras.

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

def cleared(r,a,nb,c,D,z):
    W=a+c*z; p=2*r+3
    T=W*(2*nb*((4*r+3)-r*z)-10*p*a*(1-z))-D*nb*r*(1-z)
    return T*(D*(1-z)+W)-10*p*D*(a+c)*z*(1-z)*W

def origin_gate(r,U,c0,z):
    return cleared(r,U-r**3,5*U-r**3,-r*(r+6)*c0,4*U,z)

# Check the exact polynomial clearing independently of all clock identities.
rr,aa,nb,cc,DD=S.symbols('r a nb c D')
xs=1/z; a0=xs-1; el=(aa*xs+cc)/DD; e=(aa+cc)/DD
psi=((4*rr+3)*xs-rr)/(5*(2*rr+3)); xi=-rr*xs*(xs-1)/(10*(2*rr+3))
eK=el*(nb*psi/DD-aa*a0/DD)+nb*xi/DD
assert S.cancel(10*(2*rr+3)*DD**3*z**3*(eK*(a0+el)-e*a0*el)-
                cleared(rr,aa,nb,cc,DD,z))==0

M=origin_gate(r,U,E.c(c0),E.c(B.c(fp(S.Poly(z,z,domain=S.QQ)))))
cols=[(M*r**j).cs for j in range(3)]
det=B.c(0)
for p in permutations(range(3)):
    sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
    det+=sign*cols[0][p[0]]*cols[1][p[1]]*cols[2][p[2]]
assert det.d==16 and [f.degree() for f in det.v]==[120,121,122,123]
T=S.Poly.from_dict({(i,):sp(p) for i,p in enumerate(det.v)},X,domain=S.QQ[z])
# Three independent exact checks before using any arithmetic residue.
rvar=S.Symbol('r')
for zv in (S.Rational(2,5),S.Rational(1,3),S.Rational(-1,3)):
    hs=S.Poly(H.as_expr().subs(z,zv),X,domain=S.QQ)
    hn=hs.monic()
    d2=hn.nth(3)+X; d1=hn.nth(2)+X*d2; d0=hn.nth(1)+X*d1
    Ac=rvar**3-(d0-d1+3*d2)*rvar*rvar/2-(9*d0-6*d1)*rvar/2-9*d0
    Uc=rvar*(rvar+6)*d1-rvar**3-(rvar+6)**2*d0
    Mc=origin_gate(rvar,Uc,d0,zv)
    pa=S.Poly(Ac,rvar,domain=S.QQ[X]); pb=S.Poly(Mc,rvar,domain=S.QQ[X])
    check=S.Poly(pa.resultant(pb.rem(pa)),X,domain=S.QQ).rem(hn)
    stored=S.Poly(T.as_expr().subs(z,zv)/hs.LC()**det.d,X,domain=S.QQ)
    assert stored==check
g=S.Poly(S.gcd_list(T.all_coeffs(),z),z,domain=S.QQ)
assert g.monic()==S.Poly(z**44,z,domain=S.QQ)
T=S.Poly.from_dict({(i,):S.cancel(T.nth(i)/g.as_expr()) for i in range(T.degree()+1)},X,domain=S.QQ[z])
D=S.Poly(H.resultant(T),z,domain=S.QQ)
assert D.degree()==331
fs=D.factor_list()[1]
E4=66*z**4-144*z**3+108*z**2-32*z+3
assert S.expand(J5(z)+J4(z)-2*z*E4)==0
assert sorted((p.degree(),e) for p,e in fs)==[(1,15),(4,9),(4,19),(60,1),(144,1)]
assert next(p for p,e in fs if p.degree()==1).monic()==S.Poly(z,z,domain=S.QQ)
assert next(p for p,e in fs if e==9).monic()==S.Poly(E4,z,domain=S.QQ).monic()
assert next(p for p,e in fs if e==19).monic()==S.Poly(J4(z),z,domain=S.QQ).monic()
ds=sorted([p for p,e in fs if p.degree() in (60,144)], key=lambda p:p.degree())
assert all(f.is_irreducible for f in ds)
f,g=H,T
for jj in (2,1):
    q,rr=f.pdiv(g)
    assert rr.degree()==jj and f*g.LC()**(f.degree()-g.degree()+1)==q*g+rr
    f,g=g,rr
q0,q1=(S.Poly(g.nth(i),z,domain=S.QQ) for i in (0,1))
assert all(S.gcd(q1,p).is_one for p in ds)
print("Exact immediate-origin double norm and three scalar audits: irreducible degrees 60 and 144; live linear fifth ratio in both",flush=True)

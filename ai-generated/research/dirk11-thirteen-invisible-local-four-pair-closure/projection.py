"""Consecutive mismatched fifth: exact old-clock/r/fifth three-layer norm.

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

config=list(map(E.c,[c0,c1,c2]))
class Old:
    def __init__(self,v): self.v=v
    @staticmethod
    def c(a): return a if isinstance(a,Old) else Old([E.c(a),E.c(0),E.c(0)])
    def __neg__(self): return Old([-c for c in self.v])
    def __add__(self,a): return Old([b+c for b,c in zip(self.v,Old.c(a).v)])
    __radd__=__add__
    def __sub__(self,a): return self+-Old.c(a)
    def __rsub__(self,a): return Old.c(a)+-self
    def __mul__(self,a):
        vals=[E.c(0) for _ in range(5)]
        for i,b in enumerate(self.v):
            for j,c in enumerate(Old.c(a).v):vals[i+j]+=b*c
        for i in (4,3):
            for j in range(3): vals[i-3+j]-=vals[i]*config[j]
        return Old(vals[:3])
    __rmul__=__mul__
    def __pow__(self,k):
        y=Old.c(1)
        for i in range(k): y*=self
        return y

def norm3(cols,zero):
    a=zero
    for p in permutations(range(3)):
        sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        a+=sign*cols[0][p[0]]*cols[1][p[1]]*cols[2][p[2]]
    return a
def old_gate(r,x,b):
    F=3*(r+6)*x*x+4*r*(r+6)*x+6*r*r
    J=3*(r+6)*x*x+5*r*(r+6)*x+10*r*r
    n=x*J; d=5*(x-1)*F
    return 10*(2*r+3)*(b-1)*n*n-2*((4*r+3)*b-r)*n*d+r*b*(d-n)*d

# Confirm all primitive scalings and signs independently.
rr,y,BX=S.symbols('rr y B')
ss=rr**2/(rr+6)
P=y*(y*y+rr*y+ss)
F=S.integrate(P,y)/y
J=S.integrate(y*F,y)/y
Y=J/((y-1)*F)
d=5*(y-1)*(3*(rr+6)*y*y+4*rr*(rr+6)*y+6*rr*rr)
ps=((4*rr+3)*BX-rr)/(5*(2*rr+3))
xi=-rr/(10*(2*rr+3))
assert S.cancel(old_gate(rr,y,BX)-10*(2*rr+3)*d*d*((BX-1)*Y*Y-ps*Y-xi*BX*(1-Y)))==0
x=Old([E.c(0),E.c(1),E.c(0)])
P=old_gate(Old.c(r),x,Old.c(E.c(b)))
M=norm3([(P*x**j).v for j in range(3)],E.c(0))
det=norm3([(M*r**j).cs for j in range(3)],B.c(0))
assert det.d==31 and [f.degree() for f in det.v]==[225,226,227,228]
T=S.Poly.from_dict({(i,):sp(q) for i,q in enumerate(det.v)},X,domain=S.QQ[z])
# Independent scalar checks by nesting two exact resultants at fixed literal z.
rx,xx=S.symbols('rx xx')
for zv in (S.Rational(2,5),S.Rational(-1,3)):
    hs=S.Poly(H.as_expr().subs(z,zv),X,domain=S.QQ); hn=hs.monic()
    d2=hn.nth(3)+X; d1=hn.nth(2)+X*d2; d0=hn.nth(1)+X*d1
    Rx=S.Poly(xx**3+d2*xx**2+d1*xx+d0,xx,domain=S.QQ[X,rx])
    Kx=S.Poly(old_gate(rx,xx,X),xx,domain=S.QQ[X,rx])
    Nx=S.Poly(Rx.resultant(Kx.rem(Rx)),rx,domain=S.QQ[X])
    Ar=S.Poly(rx**3-(d0-d1+3*d2)*rx**2/2-(9*d0-6*d1)*rx/2-9*d0,rx,domain=S.QQ[X])
    audit=S.Poly(Ar.resultant(Nx.rem(Ar)),X,domain=S.QQ).rem(hn)
    actual=S.Poly(T.as_expr().subs(z,zv)/hs.LC()**det.d,X,domain=S.QQ)
    assert actual==audit
g=S.Poly(S.gcd_list(T.all_coeffs(),z),z,domain=S.QQ)
assert g.monic()==S.Poly(z**74,z,domain=S.QQ)
T=S.Poly.from_dict({(i,):S.cancel(T.nth(i)/g.as_expr()) for i in range(T.degree()+1)},X,domain=S.QQ[z])
D=S.Poly(H.resultant(T),z,domain=S.QQ)
assert D.degree()==631
fs=D.factor_list()[1]
E4=66*z**4-144*z**3+108*z**2-32*z+3
E8=2772*z**8-11088*z**7+18648*z**6-17136*z**5+9360*z**4-3096*z**3+604*z**2-64*z+3
assert S.expand(J5(z)+J4(z)-2*z*E4)==0
assert S.expand(S.diff(J5(z),z)*J4(z)-J5(z)*S.diff(J4(z),z)-2*E8)==0
assert sorted((q.degree(),a) for q,a in fs)==[(1,15),(4,18),(4,25),(8,3),(420,1)]
for key,v in ((15,z),(18,E4),(25,J4(z)),(3,E8)):
    assert next(f for f,e in fs if e==key).monic()==S.Poly(v,z,domain=S.QQ).monic()
f,g=H,T
for jj in (2,1):
    q,rr=f.pdiv(g)
    assert rr.degree()==jj and f*g.LC()**(f.degree()-g.degree()+1)==q*g+rr
    f,g=g,rr
q0,q1=(S.Poly(g.nth(i),z,domain=S.QQ) for i in (0,1))
Df=next(f for f,e in fs if f.degree()==420)
assert Df.is_irreducible
assert S.gcd(q1,Df).is_one
print("Exact triple norm (two independent nested rational audits): degree631 = z^15 E4^18 J4^25 E8^3 D420, irreducible D420 and a live linear fifth ratio",flush=True)

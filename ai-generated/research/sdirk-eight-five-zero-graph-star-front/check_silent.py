#!/usr/bin/env python3
import sympy as S
from sympy.polys.rings import ring
u,v,z=S.symbols('u v z')
Q=u**3-9*u**2+18*u-6
H=v**3-4*v**2-v+2
f=S.Poly(S.resultant(Q,H.subs(v,(z-u)/2),u),z).monic()
assert f.degree()==9 and f.is_irreducible
red=lambda p:S.rem(S.rem(S.expand(p),Q,u),H,v)
basis=[u**i*v**j for i in range(3) for j in range(3)]
vec=lambda a:S.Matrix([S.Poly(a,u,v).coeff_monomial(e) for e in basis])
C=S.Matrix.hstack(*(vec(red((u+2*v)**k)) for k in range(9)))
E=C.inv()
coU=E*vec(u);coV=E*vec(v)
assert red(sum(c*(u+2*v)**i for i,c in enumerate(coU))-u)==0
assert red(sum(c*(u+2*v)**i for i,c in enumerate(coV))-v)==0
assert red(f.as_expr().subs(z,u+2*v))==0
K=S.QQ.algebraic_field((f,z));S0,D=ring('D',K)
t=K.unit
U=sum((K.convert(c)*t**i for i,c in enumerate(coU)),K.zero)
V=sum((K.convert(c)*t**i for i,c in enumerate(coV)),K.zero)
assert U+2*V==t
T0,T=ring('T',S0.to_domain())
A=U;h=D-1-V;s=D-1
P=(T-T0(S0.one*A))*(T-T0(h))*(T-T0(s))
I=lambda P:sum((d*D**i*K.convert(S.Rational(1,i+1)) for (i,),d in P.items()),S0.zero)
m=[I(P*T**i) for i in range(5)]
m0,m1,m2,m3,m4=m
delta=m0*m2-m1*m1
Hm=m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2)
print('both cubic primitive polynomial',f.as_expr(),flush=True)
print('H_m degree',Hm.degree(),'factor degrees',[(g.degree(),n) for g,n in Hm.factor_list()[1]],flush=True)
g=Hm.gcd(delta)
print('singular gcd',g.as_expr(),flush=True)

qf=Hm.factor_list()[1]
assert len(qf)==2 and qf[0]==(D,6) and qf[1][0].degree()==9 and qf[1][1]==1
assert Hm.gcd(delta)==D**2
M=qf[1][0]
assert Hm.monic()==D**6*M
def invert(a):
 s,t,h=(a%M).gcdex(M)
 assert h==S0.one and (a%M)*s+t*M==h
 return s%M
scale=invert(delta)
k=((m1*m2-m0*m3)*scale)%M
q=((m1*m3-m2*m2)*scale)%M
assert all((m[i]*q+m[i+1]*k+m[i+2])%M==0 for i in range(3))
class E:
 def __init__(self,x):self.f=(x.f if isinstance(x,E) else S0(x))%M
 def __neg__(x):return E(-x.f)
 def __add__(x,y):return E(x.f+E(y).f)
 __radd__=__add__
 def __sub__(x,y):return x+-E(y)
 def __rsub__(x,y):return E(y)+-x
 def __mul__(x,y):return E(x.f*E(y).f)
 __rmul__=__mul__
 def __pow__(x,n):
  if n==0:return E(1)
  if n%2==0:return (x*x)**(n//2)
  return x*x**(n-1)
 def __bool__(x):return bool(x.f)
sd=E((k*k-4*q)*K.convert(S.Rational(1,4)))
class P2:
 def __init__(self,a,b=0):self.a=E(a);self.b=E(b)
 def __neg__(a):return P2(-a.a,-a.b)
 def __add__(a,b):
  b=push(b);return P2(a.a+b.a,a.b+b.b)
 __radd__=__add__
 def __sub__(a,b):return a+(-push(b))
 def __rsub__(a,b):return push(b)+(-a)
 def __mul__(a,b):
  b=push(b);return P2(a.a*b.a+sd*a.b*b.b,a.a*b.b+a.b*b.a)
 __rmul__=__mul__
 def __pow__(a,n):
  if n==0:return P2(1)
  if n%2==0:return (a*a)**(n//2)
  return a*(a**(n-1))
 def norm(a):return a.a*a.a-sd*a.b*a.b
def push(a):return a if isinstance(a,P2) else P2(a)
A0=P2(A);D0=P2(D);B=P2(-E(k)*K.convert(S.Rational(1,2)),1)
def L(t):return 70*t**4-140*D0*t**3+90*D0**2*t*t-20*D0**3*t+D0**4
P0=[P2(-1),P2(2),P2(K.convert(S.Rational(-1,2)))]
def ev(P,t):return sum((q*t**i for i,q in enumerate(P)),P2(0))
def J(P,k,t):return sum((q*t**(i+k+1)*K.convert(S.Rational(1,i+k+1)) for i,q in enumerate(P)),P2(0))
eta=A0*ev(P0,A0)-J(P0,1,A0)
g=L(A0)*(A0*(J(P0,0,B)-ev(P0,B))+B*ev(P0,B)-J(P0,1,B))-L(B)*eta
nr=g.norm()
assert nr and nr.f.degree()==8
print("second-zero orientation norm is nonzero, D-degree",nr.f.degree(),flush=True)

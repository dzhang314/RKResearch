"""Known first zero and two rear ordinary clocks, exact n=1 towers."""
import sys
import sympy as S
from time import monotonic
from sympy.polys.rings import ring
u,v,z=S.symbols('u v z')
rear=sys.argv[1]
mode=sys.argv[2]
Q=u**3-3*u**2+S.Rational(3,4)*u+S.Rational(1,2)
H=v**2-2*v-1
if mode=='third':
 f=S.Poly(S.resultant(Q,H.subs(v,(z-u)/2),u),z).monic()
 assert f.degree()==6 and f.is_irreducible
 red=lambda p:S.rem(S.rem(S.expand(p),Q,u),H,v)
 basis=[u**i*v**j for i in range(3) for j in range(2)]
 vec=lambda a:S.Matrix([S.Poly(a,u,v).coeff_monomial(e) for e in basis])
 C=S.Matrix.hstack(*(vec(red((u+2*v)**k)) for k in range(6)))
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
else:
 f=S.Poly(H,v)
 assert f.is_irreducible
 K=S.QQ.algebraic_field((f,v));S0,D=ring('D',K)
 V=K.unit
 U=None
T0,T=ring('T',S0.to_domain())
A=(1+2*U) if mode=='third' else K.convert(int(mode)+1)
W=2*V if rear=='arith' else 2-V
h=D-1-V;s=D-1-W
P=(T-T0(S0.one*A))*(T-T0(h))*(T-T0(s))
I=lambda P:sum((d*D**i*K.convert(S.Rational(1,i+1)) for (i,),d in P.items()),S0.zero)
m=[I(P*T**i) for i in range(5)]
m0,m1,m2,m3,m4=m
delta=m0*m2-m1*m1
Hm=m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2)
print(rear,mode,'primitive degree',f.degree(),'H_m degree',Hm.degree(),flush=True)
M=Hm
for guard in [D,delta,h-A,s-A,h-s]:
    while True:
        gg=M.gcd(guard)
        if gg.degree()==0:break
        M=M//gg
print("guarded nonzero H degree",M.degree(),flush=True)
assert M.degree()>0
M=M.monic()
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
A0=P2(A);D0=P2(D);B=P2(-E(k)*K.convert(S.Rational(1,2)),1);C0=P2(-E(k)*K.convert(S.Rational(1,2)),-1)
def L(t):return 70*t**4-140*D0*t**3+90*D0**2*t*t-20*D0**3*t+D0**4
def L3(t):return t**3-K.convert(S.Rational(3,2))*D0*t*t+K.convert(S.Rational(3,5))*D0**2*t-K.convert(S.Rational(1,20))*D0**3
La,Lb,Lc=L(A0),L(B),L(C0)
L3a,L3b,L3c=L3(A0),L3(B),L3(C0)
def ev(P,t):return sum((q*t**i for i,q in enumerate(P)),P2(0))
def J(P,k,t):return sum((q*t**(i+k+1)*K.convert(S.Rational(1,i+k+1)) for i,q in enumerate(P)),P2(0))
def gate(P):
 a,b,c=A0,B,C0
 eta=a*ev(P,a)-J(P,1,a)
 g=La*(a*(J(P,0,b)-ev(P,b))+b*ev(P,b)-J(P,1,b))-Lb*eta
 da=a*a*ev(P,a)-J(P,2,a)
 db=b*b*ev(P,b)+a*a*(J(P,0,b)-ev(P,b))-J(P,2,b)
 dc=(c*c*ev(P,c)+(a+b)*(J(P,1,c)-c*ev(P,c))-a*b*(J(P,0,c)-ev(P,c))-J(P,2,c))*La+Lc*(eta*(a+b))
 f=(Lc*L3b-L3c*Lb)*(La*da)+(L3c*La-Lc*L3a)*(La*db)+dc*(L3a*Lb-L3b*La)
 return (J(P,0,a)-ev(P,a)),g,f
if mode=='third':
 P0=[P2(-1),P2(2),P2(K.convert(S.Rational(-1,2)))]
 R0=[P2(1+U),P2(-2-U),P2(1)]
 f0,g0,h0=gate(P0);f1,g1,h1=gate(R0)
 forms=[g1*f0-g0*f1,h1*f0-h0*f1,h1*g0-h0*g1]
else:
 P0=[P2(0) for _ in range(int(mode))]+[P2(1)]
 fp,gp,hp=gate(P0)
 assert not fp.a and not fp.b
 forms=[gp,hp]
guardvals=[sd.f,La.norm().f,Lb.norm().f, L(P2(h)).norm().f,L(P2(s)).norm().f]
cc=M
for f in forms:
 cc=cc.gcd(f.norm().f)
 print("norm residue degrees",f.norm().f.degree(),"remaining",cc.degree(),flush=True)
for guard in guardvals:
 while True:
  q=cc.gcd(guard)
  if q.degree()==0:break
  cc=cc//q
print("final",cc.degree(),flush=True)
assert cc.degree()==0

"""Six zeros, four distinct silent off clocks and a repeated terminal zero."""
import sympy as S
from sympy.polys.rings import ring
from itertools import permutations
import sys
phase=sys.argv[1]
v=S.symbols('v')
h=S.Poly(v*v-2*v-1,v)
assert h.is_irreducible
K=S.QQ.algebraic_field((h,v));V=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
S0,D=ring('D',K);T,X=ring('X',S0.to_domain())
x=lambda z:T(S0(z))
t=D-1;s=t-V;r=t-(2*V if phase=='arith' else 2-V)
P3=(X-x(t))*(X-x(s))*(X-x(r))
def I(P):
 return sum((q*D**j*C(1,j+1) for (j,),q in P.items()),S0.zero)
def det(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
m0,m1,m2,m3,m4=[I(P3*X**i) for i in range(5)]
H=det([[m0,m1,m2],[m1,m2,m3],[m2,m3,m4]])
delta=m0*m2-m1*m1
def strip(a,guards):
 for z in guards:
  while True:
   k=a.gcd(z)
   if k.degree()==0:break
   a=a//k
 return a
# First zero at physical row 5, from the two possible monomial graphs.
for aa in (1,2):
 assert H.evaluate(D,K.convert(1+aa))
 P4=P3*(X-x(aa))
 q0,q1,q2,q3=[I(P4*X**i) for i in range(4)]
 P=(q0*q2-q1*q1).gcd(q0*q3-q1*q2)
 P=strip(P,[D,q0,t-aa,s-aa,r-aa])
 print(phase,"monomial first zero",aa,"ordinary gcd",P.degree(),flush=True)
 assert P.degree()==0
# First zero at physical row 4: its clock is one of the first three zero-label
# orders (duplicate terminal clock, and two other distinct early labels).
M=strip(H,[D,delta]).monic()
print("guarded H degree",M.degree(),flush=True)
def inv(a):
 s,t,h=(a%M).gcdex(M)
 assert h==S0.one and (a%M)*s+t*M==h
 return s%M
dd=inv(delta)
k=((m1*m2-m0*m3)*dd)%M
q=((m1*m3-m2*m2)*dd)%M
m=[m0,m1,m2,m3,m4]
assert all(not ((m[i]*q+m[i+1]*k+m[i+2])%M) for i in range(3))
class E:
 def __init__(self,x=0):self.f=(x.f if isinstance(x,E) else S0(x))%M
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
sg=E((k*k-4*q)*C(1,4))
class P2:
 def __init__(self,a=0,b=0):self.a=E(a);self.b=E(b)
 def __neg__(a):return P2(-a.a,-a.b)
 def __add__(a,b):
  b=push(b);return P2(a.a+b.a,a.b+b.b)
 __radd__=__add__
 def __sub__(a,b):return a+(-push(b))
 def __rsub__(a,b):return push(b)+(-a)
 def __mul__(a,b):
  b=push(b);return P2(a.a*b.a+sg*a.b*b.b,a.a*b.b+a.b*b.a)
 __rmul__=__mul__
 def __pow__(a,n):
  if n==0:return P2(1)
  if n%2==0:return (a*a)**(n//2)
  return a*(a**(n-1))
 def norm(a):return a.a*a.a-sg*a.b*a.b
def push(a):return a if isinstance(a,P2) else P2(a)
D0=P2(D);b0=P2(-E(k)*C(1,2),1);c0=P2(-E(k)*C(1,2),-1)
def L(t):return 70*t**4-140*D0*t**3+90*D0**2*t*t-20*D0**3*t+D0**4
def L3(t):return t**3-C(3,2)*D0*t*t+C(3,5)*D0**2*t-C(1,20)*D0**3
common_guards=[sg.f,L(P2(t)).norm().f,L(P2(s)).norm().f,L(P2(r)).norm().f,L(b0).norm().f,
               (b0-P2(t)).norm().f,(b0-P2(s)).norm().f,(b0-P2(r)).norm().f]
def gate(P):
    def ev(z):return sum((q*z**i for i,q in enumerate(P)),P2(0))
    def J(k,z):return sum((q*z**(i+k+1)*C(1,i+k+1) for i,q in enumerate(P)),P2(0))
    F=J(0,a)-ev(a)
    eta=a*ev(a)-J(1,a)
    G=La*(a*(J(0,b)-ev(b))+b*ev(b)-J(1,b))-Lb*eta
    da=a*a*ev(a)-J(2,a)
    db=b*b*ev(b)+a*a*(J(0,b)-ev(b))-J(2,b)
    dc=(c*c*ev(c)+(a+b)*(J(1,c)-c*ev(c))-a*b*(J(0,c)-ev(c))-J(2,c))*La+Lc*(eta*(a+b))
    H=(Lc*L3b-L3c*Lb)*(La*da)+(L3c*La-Lc*L3a)*(La*db)+dc*(L3a*Lb-L3b*La)
    return F,G,H
P0=[P2(-1),P2(2),P2(C(-1,2))]
R1=[P2(-1),P2(1)]
R2=[P2(1),P2(-2),P2(1)]
for i,cs in enumerate(((P2(t),b0,c0),(b0,P2(t),c0),(b0,c0,P2(t)))):
 a,b,c=cs
 La,Lb,Lc=L(a),L(b),L(c)
 L3a,L3b,L3c=L3(a),L3(b),L3(c)
 f0,g0,h0=gate(P0);f1,g1,h1=gate(R1);f2,g2,h2=gate(R2)
 D1=f1*g2-f2*g1;BN=f2*g0-f0*g2;AN=f0*g1-f1*g0
 X=D1*h0+BN*h1+AN*h2
 Y=-2*AN**3-BN*AN*AN+4*BN*BN*AN+BN**3+(3*BN*AN+2*AN*AN)*D1
 for name,L0 in [('front star',[f0,g0,h0]),('arith reg',[X,Y,X+Y]),('arith sing',[D1,AN,BN])]:
  H0=M
  for z in L0:H0=H0.gcd(z.norm().f)
  R0=strip(H0,common_guards)
  print(i,name,'gcd',H0.degree(),'guarded',R0.degree(),flush=True)
  assert R0.degree()==0

#!/usr/bin/env python3
"""One-variable exact gate projection when a physical zero is at c=1/2 and k != 0."""
import sympy as S
from flint import fmpq_poly,fmpq
from math import gcd,prod
q=fmpq_poly([0,1]);K=(35*q*q+42*q+15)/21
N=105*q**3+175*q*q-33*q-51
L=180*(q+1)*(7*q*q-3)
T=4*(35*q*q-3)/7
# Same normalization as T*P_monic, using Cramer scalar scaling.
p1=-(( -175*K*q-21*K+245*q**3+385*q*q+171*q+15)*fmpq(3,7))
p2=-3*(-5*K+15*q*q+10*q+3)
class F:
 def __init__(self,v=0,w=0):
  self.a=fmpq_poly([v]) if isinstance(v,(int,fmpq)) else v
  self.b=fmpq_poly([w]) if isinstance(w,(int,fmpq)) else w
 def __add__(self,v):
  if not isinstance(v,F):v=F(v)
  return F(self.a+v.a,self.b+v.b)
 __radd__=__add__
 def __neg__(self):return F(-self.a,-self.b)
 def __sub__(self,v):return self+-v
 def __rsub__(self,v):return v+-self
 def __mul__(self,v):
  if not isinstance(v,F):v=F(v)
  return F(self.a*v.a+K*self.b*v.b,self.a*v.b+self.b*v.a)
 __rmul__=__mul__
 def __pow__(self,n):
  if n==0:return F(1)
  r=self**(n//2);return r*r*(self if n%2 else F(1))
 def mirror(self):return F(self.a,-self.b)
 def norm(self):return self.a*self.a-K*self.b*self.b
k=F(0,1);Y=2*N-L
r=F(Y*Y+q*L*L)+k*F(Y*L)
d=r+F(4*N*N);u=2*r-2*F(N)*(F(4*N-2*L)+k*F(L))
Fa=-2*d**3+u*d*d+4*u*u*d-u**3-2*r*(3*u-2*d)*d
Q=4*u**3-12*u*u*d+3*u*d*d+2*d**3
z=2*F(N)*(d+2*u)-F(L)*d
db=F(L)*d
pin=z*(F(T)*z*z+k*F(p2)*z*db+F(p1)*db*db)
J0=(F(2+6*q)-3*k)*F(L)-F(12*N*q)
J1=F(6*q*L)-12*k*F(N)
J2=3*k*F(L)-F(12*N)
P2=k*F(p2)
a=2*F(L)*(P2*P2-F(T*p1))-J2*F(T)*P2+J1*F(T*T)
b=2*F(L*p1)*P2-J2*F(T*p1)+J0*F(T*T)
HN=F(T)*b*b-P2*a*b+F(p1)*a*a
H0=J0*HN
s=S.Symbol('q')
def sym(f):
 p=S.Poly.from_list([S.Rational(int(x.numerator),int(x.denominator)) for x in f.coeffs()[::-1]],s,domain=S.QQ)
 c,P=p.clear_denoms(convert=True)
 assert c
 for u in (2,3,5,7):
  while c%u==0:c//=u
 assert c==1
 return P
G=sym(q*K*T*p1*L*N*r.norm()*d.norm()*u.norm())
def strip(P):
 P=sym(P)
 while not P.is_zero:
  d=S.gcd(P,G).primitive()[1]
  if d.degree()==0:break
  P=P.exquo(d)
 return P
def nn(a):
 if a==0:return 0
 for p in (2,3,5,7):
  while a%p==0:a//=p
 return a
def both(v):return [v.a,v.b]
def minor(F,G):return F.a*G.b-G.a*F.b
parts={
  'AA':both(Fa)+both(H0)+[HN.norm()],
  'AZ':[Fa.norm(),Q.norm(),pin.norm(),minor(Fa,Q.mirror()),minor(Fa,pin.mirror()),HN.norm()]+both(H0),
  'ZZ':both(Q)+both(pin)+both(H0)+[HN.norm()],
}
supports={'AA':13**6,'AZ':13**12,'ZZ':13**12}
for n,fs in parts.items():
 ps=[strip(f) for f in fs]
 ns=gcd(*(abs(int(S.resultant(ps[0],p))) for p in ps[1:]))
 assert nn(ns)==supports[n]
 print(n,'gate degrees',[f.degree() for f in ps],'paid support',nn(ns))

from flint import nmod_poly
for name,fs in parts.items():
 ps=[strip(f) for f in fs]
 primes=(13,)
 for p in primes:
  f=nmod_poly([],p)
  for c in ps:
   cc=nmod_poly(list(reversed([int(j)%p for j in c.all_coeffs()])),p)
   f=f.gcd(cc)
  assert f==nmod_poly([1,2,1],p)
  print(name,'geometric p13 modulus',f)

x=S.symbols('x')
q0=8*x*x-8*x+1;k0=2-8*x
E0=21*k0*k0-35*q0*q0-42*q0-15
E1=180*x*(q0+1)*(7*q0*q0-3)-(105*q0**3+175*q0*q0-33*q0-51)
TT=4*(35*q0*q0-3)/7
P1=-( -175*k0*k0*q0-21*k0*k0+245*q0**3+385*q0*q0+171*q0+15)*S.Rational(3,7)
P2=-3*k0*(-5*k0*k0+15*q0*q0+10*q0+3)
hs=[]
for kk,pp in [(k0,P2),(-k0,-P2)]:
 H0=2-3*kk+6*q0-12*x*q0
 H1=6*q0-12*x*kk
 H2=3*kk-12*x
 a=2*(pp*pp-TT*P1)-H2*TT*pp+H1*TT*TT
 b=2*pp*P1-H2*TT*P1+H0*TT*TT
 hs.append((H0,TT*b*b-pp*a*b+P1*a*a))
ns=[]
for ff in (E1,hs[0][0]*hs[0][1]):
 R=abs(int(S.resultant(E0,ff,x).as_numer_denom()[0]))
 ns.append(nn(R))
assert ns==[219735220141,3139321086281830924014713] and gcd(*ns)==1
print('singular gap independent supports',ns,'gcd',gcd(*ns))

# Independent binding of the displayed Cramer and diagonal coefficients.
qq,kk,yy=S.symbols('q k y')
def avg(expr):
 return sum(c/S.Integer(j+1) for (j,),c in S.Poly(expr,yy).terms() if j%2==0)
rr=yy*yy+kk*yy+qq
mm=[avg(rr*yy**j) for j in range(6)]
B0=S.Matrix(3,3,lambda i,j:mm[i+j])
cf=[]
for ii in range(3):
 Bj=B0.copy();Bj[:,ii]=S.Matrix([-m for m in mm[3:]])
 cf.append(S.expand(Bj.det()*S.Rational(23625,4)))
TS=S.expand(B0.det()*S.Rational(23625,4))
assert S.expand(cf[0]-S.Rational(3,7)*kk*(-21*kk**2+35*qq**2+42*qq+15))==0
subk=lambda e:S.rem(S.expand(e),kk*kk-(35*qq**2+42*qq+15)/21,kk)
assert S.expand(subk(TS)-4*(35*qq**2-3)/7)==0
def fp_expr(f):
 return sum(S.Rational(int(c.numerator),int(c.denominator))*qq**j for j,c in enumerate(f.coeffs()))
assert S.expand(subk(cf[1])-fp_expr(p1))==0
assert S.expand(subk(cf[2])-kk*fp_expr(p2))==0
P0=TS*yy**3+cf[2]*yy*yy+cf[1]*yy+cf[0]
omega=TS*(mm[2]+mm[1]*yy+mm[0]*yy*yy)+cf[2]*(mm[1]+mm[0]*yy)+cf[1]*mm[0]
A0=S.Rational(7,2)*avg(rr*rr*S.diff(P0,yy))
B1=315*avg(rr*omega)
assert S.expand(subk(A0)+4*(qq+1)*(7*qq**2-3)*(35*qq**2-3)/21)==0
assert S.expand(subk(B1)+4*(35*qq**2-3)*(105*qq**3+175*qq**2-33*qq-51)/21)==0
print("signed Cramer and diagonal identities verified")

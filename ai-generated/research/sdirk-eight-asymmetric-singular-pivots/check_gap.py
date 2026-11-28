#!/usr/bin/env python3
"""General nonsymmetric gap-singular graph, without a midpoint zero."""
import sympy as S
from math import gcd
g,y=S.symbols('g y')
k=2-8*g;q=8*g*g-8*g+1
X=k*k
T=-105*X*q-15*X+175*q**3+255*q*q+105*q+9
p0=S.Rational(3,7)*k*(-21*X+35*q*q+42*q+15)
p1=-S.Rational(3,7)*(-175*X*q-21*X+245*q**3+385*q*q+171*q+15)
p2=-3*k*(-5*X+15*q*q+10*q+3)
P=T*y**3+p2*y*y+p1*y+p0
A=-63*X*X*q+21*X*X-70*X*q**3-210*X*q*q-138*X*q-30*X+245*q**5+805*q**4+986*q**3+546*q*q+129*q+9
B=-525*X*X*q+525*X*X-1750*X*q**3-5670*X*q*q-3150*X*q-630*X+3675*q**5+13825*q**4+17970*q**3+9990*q*q+2259*q+153
diag=180*g*A-B
h=lambda k:2*y**3+(3*k-12*g)*y*y+(6*q-12*g*k)*y+2-3*k+6*q-12*g*q
V=lambda w:S.Poly(w,g)
Jf=V(S.resultant(P,h(k),y));Jr=V(S.resultant(-P.subs(y,-y),h(-k),y))
r=(2*g-1)**2-k*(2*g-1)+q
R0=(2*g-1)**2+k*(2*g-1)+q
d=r+4*g*g;u=2*r-2*g*(4*g-2-k)
F=-2*d**3+u*d*d+4*u*u*d-u**3-2*r*(3*u-2*d)*d
Q=4*u**3-12*u*u*d+3*u*d*d+2*d**3
z=2*g*(d+2*u)-d
pin=T*z**3-p2*z*z*d+p1*z*d*d-p0*d**3
guard=k*g*T*p0*r*R0*d*u
def strip(n):
 if not n:return 0
 for p in (2,3,5,7):
  while n%p==0:n//=p
 return n
def make(w):
 C,W=S.Poly(w,g,domain=S.QQ).clear_denoms(convert=True)
 assert strip(int(C))==1
 return W
G=make(guard)
def trim(w):
 W=make(w)
 while not W.is_zero:
  t=S.gcd(W,G).primitive()[1]
  if t.degree()<=0:break
  W=W.exquo(t)
 return W
D=trim(diag);f=trim(Jf);b=trim(Jr)
r=lambda p,q:abs(int(S.resultant(p,q)))
s=strip(gcd(r(D,f),r(D,b)))
assert [v.degree() for v in (D,f,b)]==[11,27,27] and s==13**3*131**3
print('diagonal and two actual anchors paid support',s)
for nm,terms in [('A',[F]),('Z',[Q,pin])]:
 ns=s
 for v in terms:ns=gcd(ns,strip(r(D,trim(v))))
 assert ns==1
 print('rear',nm,'joint paid support',ns)

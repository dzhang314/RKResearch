#!/usr/bin/env python3
import sympy as S
u,y=S.symbols('u y')
Q=u**3-3*u*u+1
L=35*y**4-30*y*y+3
R0=u*(1+2*u-u*u)
R2=(u-2)*(u+1)**2
H=(1+u)*(R2*(y**3+1)+3*R0*(y+1))-3*(R2*y*y+R0)
R=S.resultant(L,H,y)
N=abs(int(S.resultant(Q,R,u)))
def paid(n):
 for p in (2,3,5,7):
  while n and n%p==0:n//=p
 return n
assert L.subs(y,-S.Rational(2,3))==-S.Rational(277,81)
assert paid(N)==2014914997
print('constant gap characteristic',277)
print('cubic gap characteristic',paid(N))

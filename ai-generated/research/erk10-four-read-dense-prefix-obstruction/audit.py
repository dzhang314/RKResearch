#!/usr/bin/env python3
"""Check the rational-function identities for the four-read dense-prefix obstruction."""
import sympy as S
q,r,s,u,v,y=S.symbols('q r s u v y')
F=S.Rational
N=q**4*(r-1)*u**2+q*(q+2*r+q*q-6*q*r+2*q*q*r)*u+r-q
D0=q*(3*q-2*r)*u+2*r-3
C=r*r*(1-q)*D0
V=S.cancel(-N/C)
check=lambda a,b: S.cancel(a-b)==0
ds=(-F(1,2),-F(1,2)/u,-F(1,2)/v)
g1=-F(1,3)
l21=q*q/2+ds[1]
g2=l21-q**3/3
h2=l21*ds[0]
interp=lambda z1,z2: (z1+(r-1)*(z2-z1)/(q-1))*ds[2]
g3=interp(g1/ds[0],g2/ds[1])
h3=interp(0,h2/ds[1])
p2=r*r/2+ds[2]; p3=r**3/3+g3
l31=(q*p2-p3)/(q-1)
l32=(p3-p2)/(q*(q-1))
assert check(l31*ds[0]+l32*ds[1]-h3,(N+C*v)/(12*q*u*v*(q-1)**2))
assert check(N.subs(u,(3-2*r)/(q*(3*q-2*r))),
 -12*r*(q-1)**2*(q-r)*(r-1)/(3*q-2*r)**2)
assert check(V.subs(u,1/q),1/r)
assert check(V.subs(u,1/q**2),1/r**2)
print('First-three equation, exceptional coefficient, and two singular roots verified.')

D=S.Poly(S.interpolate([(0,0),(1,ds[0]),(q,ds[1]),(r,ds[2])],y),y)
a,b,c=[S.factor(D.nth(k))for k in (1,2,3)]
c0=-(q*u-1)*(q*q*u-1)**2/(2*q*u*(q-1)*N)
assert check(c.subs(v,V),c0)
print('Cubic donor-pivot coefficient verified.')

K=-c*y**4/4-a*y**2/2-b*y**3/3
R=(c*c*q*r-(b+c*(1+q+r))*a)*y**2/2+((a-c*(q+r+q*r))*c-(b+c*(1+q+r))*b)*y**3/3
W=[1,q,r,s]
def detpoly(Q):
  B=S.factor(Q.subs(y,s)/S.prod(s-x for x in W[:3]))
  A=S.factor(sum(w*Q.subs(y,z)/S.prod(z-x for x in W if x!=z)
                 for w,z in zip((1,u,v),W)))
  return A,B
ka,kb=detpoly(K);ra,rb=detpoly(R)
fused=S.factor(ka*rb-kb*ra)
expected=-s*s*(q*u-1)**2*(q*q*u-1)**5/(
   32*q*q*u*u*(q-1)**2*(q-s)*(s-1)*D0*N*N)
assert check(S.factor(fused.subs(v,V)),expected)
print('Fourth-site terminal elimination identity verified.')

X=S.symbols('X')
for k,z in [(1,F(1,12)),(2,F(1,20))]:
  T=S.Poly(X*(1-X)**(k+1),X)
  assert sum(v/(e+1)for (e,),v in T.terms())==z
print('Both propagated singular branches contradict the paid bush moments.')

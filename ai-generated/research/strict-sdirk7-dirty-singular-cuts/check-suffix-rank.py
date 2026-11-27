#!/usr/bin/env python3
"""Exact reverse chronology and full-rank certificates for the final four active columns."""
import sympy as S
u,x,d=S.symbols('u x d')
M=u*u-4*u+2
T=u**3-7*u*u+10*u-2
L=lambda x:x*x/2-2*x+1
theta=1/M
f=lambda x:-S.Rational(4,3)+(2*theta-2)*(x-1)/3
assert all(T.subs(u,a)!=0 for a in (-2,-1,1,2))
for kind,v,rr in [
    ('reflection',4-u,L(u)),
    ('arithmetic',2*u-1,L(u)*(4*u**3-24*u*u+39*u-17)/T),
]:
 tap=(L(v)-d)/(u-1)
 other=v-1-tap
 second=v*v+tap*u*u+other-v**3/3-f(v)*d
 fourth=tap*L(u)-other/2-theta*(1-v)*d
 assert S.cancel(second.subs(d,rr))==0
 assert S.cancel(fourth.subs(d,rr))==0
 coeff=S.factor(S.diff(fourth,d))
 print(kind,"unique third ratio via fourth equation coefficient",coeff)
 correction=S.cancel((rr-L(v))/((v-1)*(v-u)))
 poly=S.Poly(S.expand(L(x)+correction*(x-1)*(x-u)),x)
 g=poly.nth(0)*(x-1)+poly.nth(1)*(x*x/2-x)+poly.nth(2)*(x**3/3-x*x)
 k=-poly.nth(1)+poly.nth(2)*f(x)-theta*(1-x)
 nonrank=S.factor(g+k*poly.as_expr())
 if kind=='reflection':
  want=-2*(u-x)*(x-1)*(x+u-4)/(3*M)
 else:
  want=-(u-x)*(x-1)*(u-3)*(u-2)**2*(u-1)**3*(2*u-1-x)/(3*M*T*T)
 assert S.cancel(nonrank-want)==0
 print(kind,"rank-drop test",nonrank)

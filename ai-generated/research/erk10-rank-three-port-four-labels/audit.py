#!/usr/bin/env python3
"""Exact arithmetic for the two positions of the sole non-origin clean row."""
import sympy as S
X,t,c,d,a,b=S.symbols("X t c d a b")
p=X*X+c*X+d
J=lambda p,z:S.integrate(p,(X,0,z))
# Last-clean chart: no tap can read it; these are the primitive/order-five moments.
assert S.expand(J(J(X*p,X),1)-(J(X*p,1)-J(X**2*p,1)))==0
P=X*X-S.Rational(6,5)*X+S.Rational(3,10)
assert S.factor(J(X*P,X))==X**2*(X-1)*(5*X-3)/20
print("last clean: J(XP0) =",S.factor(J(X*P,X)))
# Fifth-clean chart: recover the single marked coefficient gate.
expr=[J(X*p,t)/t**2,J((X-t)*X*p,1)]
sol=S.solve(expr,(c,d))
Q=12*t*t-20*t+9
L=30*t**3-80*t*t+75*t-24
assert S.factor(sol[c]+3*(15*t**3-10*t*t-15*t+12)/(5*Q))==0
assert S.factor(sol[d]-3*t*(20*t*t-35*t+16)/(10*Q))==0
assert S.factor(p.subs(sol).subs(X,t)-t*L/(10*Q))==0
w=S.factor(J(X*p,1).subs(sol)/(t*p.subs(sol).subs(X,t)))
assert S.factor(w+(t-1)*(5*t-3)/(2*t*t*L))==0
r=X*(X-2*t/3)
delta=S.factor(J((X-1)*r,1)-w*(t-1)*r.subs(X,t))
assert S.factor(delta-(10*t*t-15*t+6)*Q/(36*L))==0
print("fifth clean: monic c,d =", {q:S.factor(r)for q,r in sol.items()})
print("fifth clean output mass =",w)
print("fifth clean hull determinant =",delta)

#!/usr/bin/env python3
"""Universal old second-primitive split and the matched-fifth cleared gate."""
import sympy as S
X,r,s,lam,c0,c1,c2,b,U=S.symbols('X r s lam c0 c1 c2 b U')
m=X*X+r*X+s; F=X*(X*X/4+r*X/3+s/2);J=X*X*(X*X/20+r*X/12+s/6)
M=S.Matrix.hstack(*(S.Matrix([S.Poly(S.rem(F*X**j,m,X),X).nth(i)
                                for i in range(2)]) for j in range(2)))
assert S.expand(M.det()+s*s*(2*r*r-9*s)/144)==0
p=2*((4*r*r-21*s)*X-r*s); q=-X*((r*r-6*s)*X-r*s); d=10*(2*r*r-9*s)
assert S.expand(d*J-p*F-q*m)==0
subs={s:r*r/(r+6)}
assert S.cancel((p/d).subs(subs)-((4*r+3)*X-r)/(5*(2*r+3)))==0
assert S.cancel((q/d).subs(subs)+r*X*(X-1)/(10*(2*r+3)))==0
print("universal second primitive: exact split, determinant, and sharp normalized fourth coefficients")
A=((4*r+3)*b-r)/(5*(2*r+3))
C=-r/(10*(2*r+3))
g=lam*((1+lam)*A-lam*(b-1))+(1+lam)*C*b
expected=2*lam*(1+lam)*((4*r+3)*b-r)-10*(2*r+3)*lam**2*(b-1)-(1+lam)*r*b
assert S.cancel(10*(2*r+3)*g-expected)==0
assert S.expand(expected.subs(lam,-1)+10*(2*r+3)*(b-1))==0
assert expected.subs(lam,0)==-r*b
delta=S.symbols('delta')
l0=-delta*c0/s
ld=S.Rational(1,4)-delta
L=ld*X+l0
# Eliminate delta without division from the two nonconstant affine fits.
Eq2=delta*c2-(S.Rational(1,3)-ld)*r+l0
Eq1=delta*c1-(S.Rational(1,2)-ld)*s+l0*r
El=S.cancel((3*s*Eq2-r*Eq1).subs(subs)*(r+6)/delta)
assert S.expand(El-((r+6)*(r+3)*c0-r*(r+6)*c1+3*r*r*c2-2*r**3))==0
aff= r*(r+6)*c1-r**3-(r+6)**2*c0
assert S.cancel(4*r*(r+6)*Eq1.subs(subs)-(4*delta*aff-r**3))==0
print("matched fifth: cleared two-slope equation and old monic cubic, live-ratio delta formula")

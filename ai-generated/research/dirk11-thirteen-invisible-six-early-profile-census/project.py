#!/usr/bin/env python3
"""Exact unordered early reverse profile projection, before selecting chronology."""
import sympy as S
Y,c0,c1,c2,r,s=S.symbols("Y c0 c1 c2 r s")
R=Y**3+c2*Y**2+c1*Y+c0
m=Y**2+r*Y+s
P=Y*m;P0=Y*R
I=lambda f:S.Poly(f,Y).integrate().as_expr()
def v(f):
    a=S.Poly(S.rem(f,R,Y),Y)
    return S.Matrix([a.nth(i)for i in range(3)])
M=S.Matrix.hstack(*(v(m*Y**i)for i in range(3)))
N=S.factor(M.det())
w0=M.adjugate()*v(I(P0)/Y)
D=c0*r*r-(2*s*s+c1*s)*r+3*c2*s*s-3*c0*s
q=3*s*c2-4*r*s-3*c0
p=r*c0
H=sum(w0[i]*p**i*q**(2-i)for i in range(3))
A=S.rem(H,D,r)
raw=S.factor(S.resultant(D,A,r))
F1=96*s**3-80*c1*s*s+75*c0*c2*s-75*c0*c0
F2=s**3-c1*s*s+c0*c2*s-c0*c0
Fn=-c0*c1*c1-12*c0*c1*s+12*c0*c2*c2*s-36*c0*s*s-c1*c1*c2*s-4*c1*c2*s*s+12*c2*s**3
Fct=12*c0**2+8*c0*c1*c2-6*c0*c2**3+c1*c1*c2*c2
assert S.degree(A,r)==1
assert S.cancel(raw-S.Rational(3,100)*(c2*s-c0)**2*F1*F2**2*Fn)==0
h0=S.cancel(sum(w0[i]*(-c0)**i*(2*s-c1)**(2-i)for i in range(3)).subs({r:0,s:c0/c2}))
assert S.cancel(h0-c0**2*(c0-c1*c2)**2*(6*c0-5*c1*c2)/(15*c2**3))==0
hct=S.cancel(H.subs(r,s*(2*s+c1)/c0).subs(s,c0/c2))
assert S.cancel(hct+8*c0**4*(2*c0+c1*c2)**2*Fct/(5*c2**10))==0
for k,want in enumerate((-c0*c2/20,-3*c0**2/10,-c0**2*c1/6)):
    Mk=S.Matrix.hstack(*(v(Y**(k+i))for i in range(3)))
    assert S.expand((Mk.adjugate()*v(I(P0)/Y))[0]-want)==0
for rr,F in ((15*(c2*s-c0)/(16*s),F1),((c2*s-c0)/s,F2)):
    rnum,rden=S.cancel(A.subs(r,rr)).as_numer_denom()
    assert S.rem(rnum,F,s)==0
A1,A0=S.Poly(A,r).all_coeffs()
t1=c1+6*s
t0=6*c2*s
Q=3*(5*c0**4-10*c0**3*c2*s+5*c0**2*c2**2*s**2+47*c0**2*s**3-47*c0*c2*s**4+16*c1*s**5+32*s**6)/(10*c0)
assert S.cancel(A1*t0+A0*t1-Q*Fn)==0
assert all(S.expand(u.subs({c2:0,c1:-6*s}))==0 for u in (A1,A0))
print('Exact first-gap profile resultant, contact gates and both pivot-conditional branches checked')

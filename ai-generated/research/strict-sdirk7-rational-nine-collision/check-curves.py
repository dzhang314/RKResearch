#!/usr/bin/env python3
"""Exact replay of the scalar discriminants and finite arithmetic.
Requires SymPy for polynomial normalization, not for the integer test.
"""
from math import isqrt
from fractions import Fraction as F
from sympy import (
    Poly, Rational, diff, discriminant, expand, factor, factor_list, gcd, integrate,
    symbols, solve, S
)
y,z,u,d,T=symbols('y z u d T')
h=(y-1)*(y-u)
k=-(y**2-4*y+2)/2
P6=z**6-30*z**5+405*z**4-3190*z**3+14400*z**2-31500*z+25725
Q4=z**4-24*z**3+180*z**2-480*z+360
G8=24500*d**8-490700*d**7+3876985*d**6-15297290*d**5+31600324*d**4-33601568*d**3+18747248*d**2-5240640*d+580032
H8=86975*d**8-2030350*d**7+18454725*d**6-82924460*d**5+194230660*d**4-230935520*d**3+129356480*d**2-28040704*d+2052352

def I(f,Z):
    return expand(sum(c*Z**j[0]/(j[0]+1) for j,c in Poly(f,y).terms()))
def prime_minus_id(f):
    return integrate(f,(y,0,y))-f
def receipt(a,b,Z,kind):
    F2=(y-Z+a)*(y-Z+b)
    if kind==0: f=F2
    if kind==1: f=F2*(2*b*(Z-y)-6) # physical a=2, V=span(x,x²,g)
    if kind==2: f=F2*(Z-y-8+b)     # physical a=1, V=span(1,x,g)
    P=I(prime_minus_id(h)*f,Z)
    Q=I(prime_minus_id(k)*f,Z)
    W=k*P-h*Q
    L=[I(y**j*W*F2,Z) for j in range(3)]
    return expand(L[1]**2-L[0]*L[2])
def rational_square(c):
    c=F(c)
    return c>=0 and all(isqrt(v)**2==v for v in (c.numerator,c.denominator))
def equal_mod_square(actual,expect):
    q=factor(actual/expect)
    assert q.is_Rational and q and rational_square(q), q
def centered(t):
    return t**6+30*t**4-90*t**3-825*t**2+750*t+4475

if __name__=='__main__':
    r0=receipt(0,2,z,0)
    expect=(2*z**2*Q4)**2*P6
    equal_mod_square(discriminant(r0,u),z**16*expect)
    assert all(int(Q4.subs(z,i))%13 for i in range(13))
    assert all(not rational_square(centered(t)) for t in range(-600,601))
    assert expand(P6.subs(z,T+5)
       - ((T**3+15*T-45)**2-(1050*T**2-2100*T-2450)))==0

    r1=receipt(2,d,S(4),1)
    equal_mod_square(discriminant(r1,u),3*(35*d**2-209*d+105)**2*G8)
    assert not rational_square(209**2-4*35*105)

    r2=receipt(1,d,S(4),2)
    equal_mod_square(discriminant(r2,u),((7*d-48)*(7*d-8))**2*H8)
    for d0,want in [(Rational(48,7),Rational(-854814911,1190043009)),
                     (Rational(8,7),Rational(54545409,5276209))]:
        assert solve(r2.subs(d,d0),u)==[Rational(59,27)]
        F2=(y-3)*(y-4+d0)
        hh=h.subs(u,Rational(59,27))
        ah,bh,ch=[I(hh*F2*y**j,S(4)) for j in (1,0,2)]
        ak,bk,ck=[I(k*F2*y**j,S(4)) for j in (1,0,2)]
        determinant=bh*ak-bk*ah
        assert determinant!=0
        sum34=(bh*ck-bk*ch)/determinant
        prod34=(ah*ck-ak*ch)/determinant
        assert sum34**2-4*prod34==want and not rational_square(want)

    for pol,X,g in ((P6,z,2),(G8,d,3),(H8,d,3)):
        assert Poly(pol,X).degree()==2*g+2 and gcd(pol,diff(pol,X))==1
    print('Certified three squarefree curves of genera 2/3/3 and both degenerate constant-seed rejections.')
    print('The genus-two finite integer replay exhausts |z-5| <= 600; the analytic square gap handles the rest.')

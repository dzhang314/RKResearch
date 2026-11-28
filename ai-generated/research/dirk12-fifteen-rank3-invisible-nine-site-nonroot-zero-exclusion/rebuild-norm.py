#!/usr/bin/env python3
"""Rebuild the two exact characteristic-zero resultants and augmented moment determinant."""
import json
from pathlib import Path
import sympy as S


def eq(a,b=0):
    assert S.cancel(a-b)==0,S.factor(a-b)


def main():
    base=Path(__file__).resolve().parent
    data=json.loads((base/'first-gate-norm.json').read_text())
    T,a,h,b=S.symbols('T a h b')
    I=[S.Rational(1,i+4)-(2-a)/S.Integer(i+3)+(1-a)/S.Integer(i+2) for i in range(8)]
    M=S.Matrix([[I[i+j] for j in range(3)] for i in (1,2,3)])
    co=M.inv()*S.Matrix([-I[j+3] for j in (1,2,3)])
    ji=M.inv()*S.Matrix([1,S.Rational(2,3)*h,h*h/4])
    n0=S.factor(I[3]+sum(c*t for c,t in zip(co,I[:3])))
    n4=S.factor(I[7]+sum(c*t for c,t in zip(co,I[4:7])))
    b0=S.factor(h*sum(c*t for c,t in zip(ji,I[:3]))+S.Rational(31,12))
    b4=S.factor(sum(c*t for c,t in zip(ji,I[4:7]))-h**3/13)
    H=S.factor(b0*n4-h*n0*b4).as_numer_denom()[0]
    H0=sum(c*a**i*h**j for i,j,c in data['H'])
    eq(H,H0)
    targets=[1,S.Rational(2,3)*h,h*h/4,h**3/13]
    A=[[h*I[0],h*I[1],h*I[2],S.Rational(31,12),h*I[3]]]
    A.extend(I[i:i+3]+[-targets[i-1],I[i+3]] for i in range(1,5))
    eq(S.det(S.Matrix(A))*889056000*25945920,H)
    d=42*a**3-56*a*a+21*a-2
    n=42*a**4-84*a**3+56*a*a-14*a+1
    eq(S.Poly(H,h).LC(),792*n)
    assert S.gcd(d,n)==1
    eq(S.Poly(S.rem(H,n,a),h).nth(4))
    assert S.gcd(S.Poly(H,h).nth(3),n)==1
    print('literal augmented determinant, cubic and quartic typing and exact leading guard')
    Q=S.factor(T**3+sum(T**j*(c-h*n0/b0*v) for j,(c,v) in enumerate(zip(co,ji))))
    qn,qd=Q.as_numer_denom()
    L=S.diff(S.legendre(6,2*T-1),T)
    ab0=a**4*(2*b-a)*L.subs(T,b)-b**3*(2*b*b-6*a*b+5*a*a)*L.subs(T,a)
    ab,ar=S.div(ab0,b-a,b)
    assert not ar
    ab=S.factor(ab.subs(b,1-T))
    p=S.resultant(qn,ab,T)
    p0=sum(c*a**i*h**j for i,j,c in data['p'])
    eq(p,p0)
    pp=S.Poly(p,a,h)
    assert pp.degree_list()==(33,15) and len(pp.terms())==544
    r=S.Poly(S.resultant(H,p,h),a)
    raw=S.Poly(sum(c*a**i for i,c in enumerate(data['Q'])),a)
    expected=raw*S.Poly(n**15,a)
    assert r.degree()==192 and raw.degree()==132
    assert r==expected.mul_ground(r.LC()/expected.LC())
    print('actual stripped b gate, degree-(33,15) resultant, exact degree-132 ordinary clock factor')


if __name__=='__main__':
    main()

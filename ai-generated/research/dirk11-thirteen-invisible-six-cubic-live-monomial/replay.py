#!/usr/bin/env python3
"""Exact one-variable dead-factor test, after the live monomial chronologies."""
import sympy as S
B,Y,X=S.symbols('B Y X')
J4=lambda var:42*var**4-84*var**3+56*var**2-14*var+1
J5=lambda var:(2*var-1)*(66*var**4-132*var**3+84*var**2-18*var+1)
b=1-B
T5=S.Poly(J5(Y)*J4(B)-J5(B)*J4(Y),Y)
T4=T5.exquo(S.Poly(Y-B,Y))
q4=T4.as_expr(); q0,q1=T4.nth(0),T4.nth(1)
Uf=[T5.LC()*J4(Y)-42*q4,
    S.Poly(q0*J4(Y)-q4,Y).exquo(S.Poly(Y,Y)).as_expr(),
    S.Poly(q0*q0*J4(Y)-q4*(q0+(-14*q0-q1)*Y),Y).exquo(S.Poly(Y*Y,Y)).as_expr()]
S6=S.Poly(X*T5.as_expr().subs(Y,1-X),X)

def Ip(f):
    p=S.Poly(f,X)
    return sum(p.nth(k)*X**(k+1)/(k+1)for k in range(p.degree()+1))

for j,q in enumerate(Uf,1):
    u=S.Poly(q.subs(Y,1-X),X)
    print('case',j,'degrees',u.degree(),flush=True)
    lhs=S.Poly((X-1)*Ip(X*u.as_expr()),X).prem(u)
    rhs=S6.prem(u)
    minors=[lhs.nth(i)*rhs.nth(k)-lhs.nth(k)*rhs.nth(i) for i,k in ((0,1),(0,2),(1,2))]
    con=S.Poly(S.gcd_list(minors),B,domain=S.QQ).monic()
    print('det gcd:',S.factor_list(con.as_expr(),B),flush=True)
    assert not con.is_zero
    dead=S.Poly(B*(B-1)*J4(B)*q0*u.LC()*u.nth(0)*u.as_expr().subs(X,1)*u.as_expr().subs(X,b),B,domain=S.QQ)
    while True:
        p=con.gcd(dead)
        if p.degree()==0:break
        con=con.exquo(p).monic()
    assert con.degree()==0
    print('live det gcd:',S.factor(con.as_expr()),flush=True)

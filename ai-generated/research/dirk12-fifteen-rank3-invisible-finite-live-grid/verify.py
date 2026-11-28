#!/usr/bin/env python3
"""Exact scalar gate and universal affine-line noncontainment factors."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0,S.factor(f-g)


def main():
    d,v,u,A,B,C,s=S.symbols('d v u A B C s')
    AA=d+v+u;BB=d*v+u*(d+v);CC=d*v*u
    eq(BB*(AA-u)-6*CC,(v*v-4*d*v+d*d)*u+d*v*(d+v))
    k=u**3-A*u*u+B*u-C
    us=A-6*C/B
    E=(A*B-7*C)*B**3-6*C*(A*B-6*C)**2
    eq(k.subs(u,us),B*us-C-6*C*us**2/B)
    eq(B**3*k.subs(u,us),E)
    assert S.total_degree(E)==5
    print('actual third reverse gate, symmetric equation and total degree five')
    a0,a1,c0,c1,b0=S.symbols('a0 a1 c0 c1 b0')
    f=B*u-C-6*C*u*u/B
    g=S.Poly(f.subs({B:b0,C:c0+c1*s,u:a0+a1*s}),s)
    eq(g.nth(3),-6*c1*a1*a1/b0)
    eq(g.nth(2).subs(c1,0),-6*c0*a1*a1/b0)
    eq(g.nth(1).subs(a1,0),-c1*(1+6*a0*a0/b0))
    eq(g.nth(0).subs(a1,0)-c0*g.nth(1).subs(a1,0)/c1,b0*a0)
    print('complete constant-B line coefficient cases')
    alpha,beta,gamma,delta,eta=S.symbols('alpha beta gamma delta eta')
    ff=f.subs(u,us).subs({A:alpha*B+beta,C:gamma*B+delta})
    E1=S.Poly(S.cancel(B**3*ff),B)
    eq(E1.nth(0),-216*delta**3)
    h=S.Poly(ff.subs({delta:0,beta:eta+6*gamma}),B)
    eq(h.nth(0),-6*gamma*eta*eta)
    eq(h.nth(1).subs(eta,0),-gamma)
    print('variable-B pole, constant and linear-coefficient contradictions')


if __name__=='__main__':
    main()

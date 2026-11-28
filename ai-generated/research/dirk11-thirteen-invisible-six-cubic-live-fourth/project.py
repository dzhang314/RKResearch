#!/usr/bin/env python3
"""Exact fourth-clean coefficient identities and the slope-minus-one clock projection."""
import sympy as S

Y,V,c0,c1,c2,r,s,B=S.symbols('Y V c0 c1 c2 r s B')
R=Y**3+c2*Y**2+c1*Y+c0
P0=Y*R
m=s+r*Y+Y**2
P=Y*m

def vec(f):
    a=S.Poly(S.rem(f,R,Y),Y)
    return S.Matrix([a.nth(i)for i in range(3)])
def ev(v,x):return sum(co*x**i for i,co in enumerate(v))
def prim(f):
    p=S.Poly(f,Y)
    return sum(p.nth(i)*Y**(i+1)/S.Integer(i+1)for i in range(p.degree()+1))
M=S.Matrix.hstack(*(vec(m*Y**i)for i in range(3)))
den=S.factor(M.det())
adj=ev(M.adjugate()*S.Matrix([1,0,0]),Y)
r0,w,t=[S.factor(ev(vec(prim(p)/Y*adj),V))for p in (P,P0,prim(P))]
D=c0*r*r-(2*s*s+c1*s)*r+3*c2*s*s-3*c0*s

def quotient(n):
    return S.Poly(n,V).exquo(S.Poly(V*V*R.subs(Y,V),V)).as_expr()

J=quotient(r0*prim(P0).subs(Y,V)-w*prim(P).subs(Y,V))
J2=quotient(r0*prim(prim(P)).subs(Y,V)-t*prim(P).subs(Y,V))
A=S.rem(J,D,r)
assert S.degree(A,r)==1 and S.degree(A,V)==1
F1=96*s**3-80*c1*s*s+75*c0*c2*s-75*c0*c0
F2=s**3-c1*s*s+c0*c2*s-c0*c0
F3=(-3*V**2*c0**2-6*V**2*c0*c2*s+2*V**2*c1**2*s+8*V**2*c1*s*s
    -3*V**2*c2**2*s*s+8*V**2*s**3-3*V*c0*c1*s-6*V*c0*s*s
    +V*c1*c2*s*s+2*V*c2*s**3+c0*c0*s-c0*c2*s*s)
assert S.cancel(S.resultant(D,A,r)+F1*F2*F3/(14400*c0))==0
assert S.cancel(J2.subs({r:0,s:c0/c2})+V*c0**2*(c0-c1*c2)/(60*c2**3))==0
print("Exact three-cubic census and excluded zero-middle test",flush=True)

# Conditional slope -1, not the entire F1 factor.
rminus=15*(c2*s-c0)/(16*s)
Js,Js_den=S.cancel(J2.subs(r,rminus)).as_numer_denom()
assert S.Poly(Js_den,s,domain=S.QQ).monic()==S.Poly(s**3,s,domain=S.QQ)
SP=S.rem(Js,F1,s)
RN=S.factor_list(S.resultant(F1,SP,s),(V,c0,c1,c2))[1]
assert sorted((S.degree(f,V),k)for f,k in RN)==[(0,10),(3,1)]
assert any(f in (c0,-c0) and k==10 for f,k in RN)
F=next(f for f,k in RN if S.degree(f,V)==3)
j4=lambda y:42*y**4-84*y**3+56*y**2-14*y+1
j5=lambda y:(2*y-1)*(66*y**4-132*y**3+84*y**2-18*y+1)
T4=S.Poly(j5(V)*j4(B)-j5(B)*j4(V),V).exquo(S.Poly(V-B,V))
lead=T4.LC()
C2=T4.nth(3)+V*lead
C1=T4.nth(2)+V*C2
C0=T4.nth(1)+V*C1
Fx=S.Poly(F,c0,c1,c2)
g=S.Poly(sum(co*lead**(4-i-j-k)*C0**i*C1**j*C2**k
             for (i,j,k),co in Fx.terms()),V).prem(T4)
assert g.degree()==3
gcontent,gprim=g.primitive()
assert S.Poly(gcontent,B,domain=S.QQ).monic()==S.Poly(j4(B)**6,B,domain=S.QQ).monic()
G=gprim.as_expr()
b_factors=S.factor_list(S.resultant(T4.as_expr(),G,V),B)[1]
assert sorted((S.degree(f,B),k)for f,k in b_factors)==[(4,4),(60,1)]
ff=next(f for f,k in b_factors if k==4)
assert S.Poly(ff,B,domain=S.QQ).monic()==S.Poly(j4(B),B,domain=S.QQ).monic()
f60=S.Poly(next(f for f,k in b_factors if k==1),B,domain=S.QQ).monic()
print("Exact conditional slope −1 clock projection: primitive degree 60 only after J4(B)",flush=True)

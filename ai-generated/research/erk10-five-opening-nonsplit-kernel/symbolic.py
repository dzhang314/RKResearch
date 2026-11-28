#!/usr/bin/env python3
"""Exact generic opening and two independent pure pivot identities."""
import sympy as S
v,s,p,q=S.symbols('v s p q',nonzero=True)
u=((s-2*p)*v-3*p*s*s)/(2*p*s)
P=lambda x:x**3+u*x*x+v*x
alpha=p**2*(3*s-2*p)/s**3
beta=S.factor(P(q)/P(s))
assert S.cancel(P(p)-alpha*P(s))==0
assert S.cancel(P(s)+s*s*(p*s-v)/(2*p))==0
D=(p-alpha*s)*(q*q-beta*s*s)-(q-beta*s)*(p*p-alpha*s*s)
assert S.cancel(D-s*p*q*(p-s)*(q-s)*(q-p)/P(s))==0
j=p*p*(p-s)/s**2
assert S.cancel(j-(p*p-alpha*s*s)/(2*s))==0
b1=q*q/2-beta*s*s/2
b2=q**3/3-beta*s**3/3
qs=(p*b1-b2)/(s*(p-s))
qp=(b2-s*b1)/(p*(p-s))
G=(2*p-s)*v-3*q*s*s
PP=S.factor(alpha*(p-s)*(qs+alpha*qp)-beta*(q-s)*j)
assert S.cancel(PP-2*p**3*q*(p-q)*(p-s)*(q-s)*G/(3*s**6*(p*s-v)))==0
Q0=lambda x:(s+p)*x**3/3-s*p*x*x/2-x**4/4
K=S.factor(S.det(S.Matrix([[w,w*x,Q0(x)]for w,x in zip((1,alpha,beta),(s,p,q))])))
Z=S.factor(K.subs(v,3*q*s*s/(2*p-s)))
wanted=-3*p**2*q**2*(p-q)**2*(p-s)*(2*p-3*s)*(q-s)/(4*s*(2*p-s)*(p*s-3*q*s*s/(2*p-s)))
assert S.cancel(Z-wanted)==0
assert S.cancel(beta.subs(p,3*s/2).subs(v,3*s*q/2))==0
Vq=3*q*q*(3*p-2*q)/(4*p*p)
Vp=3*p/4
Qp=-p**4/36
Qq=5*p*q**3/9-p*p*q*q/3-q**4/4
assert S.expand(Qp*Vq-Qq*Vp-3*p*q*q*(p-q)**2/16)==0
print('generic quotient determinant checked')
print('first pure pivot',PP)
print('second pure pivot on first-pivot-zero branch',Z)
print('split clean-donor fallback p,q minor checked')

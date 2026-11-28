#!/usr/bin/env python3
"""Exact scalar receipts for the normalized DIRK11/13 r=1,d=5 reduction.

No numerical tableau or reduced characteristic-zero tableau is used.
Requires SymPy. All identities, degree/factor, and real-root counts use QQ.
"""
from sympy import (Poly, QQ, Rational as Q, S, cancel, expand, factor, factor_list,
                   fraction, gcd, integrate, resultant, subresultants, symbols)

u, v, w, V, k, X = symbols('u v w V k X')
mu = V*(V-u)*(V-u/2)
du = -u**3/(6*V*(V-u))
dv = v**3*(2*u-v)/(6*(u-2*v)*V*(V-u))
assert cancel((V*(V-u)*(V-v)-mu)*dv-v**3*(2*u-v)/12) == 0
assert cancel(du*V*(V-u)+u**3/6) == 0
nuu = (u+V)*mu + u*V*(V-u)*(5*V-3*u)/10
nuv = (V+u+v)*mu + v**3*(3*v**2-5*(V+u)*v+10*V*u)/(60*dv)
slope = 3*V*(u-V)*(u-v)**2/(5*(2*u-v))
assert cancel((nuv-nuu)/(v-u)-slope) == 0
nuw = nuu+slope*(w-u)
M = 4*w*u**2-13*w*u*v+4*w*v**2+u**2*v+u*v**2
L = 3*w**2-5*w*(u+v)+10*u*v
J = w*u**2-4*w*u*v+w*v**2+u**2*v+u*v**2
F = w**3*(2*u-v)*L
C = V*(V-u)*(V-v)*(V-w)-nuw+(u+v+w)*mu
assert cancel(C/(V*(V-u))+M/(10*(2*u-v))) == 0
assert cancel(C/slope-M/(6*(u-v)**2)) == 0
assert expand(integrate(X*(X-u)*(X-v)*(X-w),(X,0,w)) + w**3*L/60) == 0

k1, k2 = -u**3/6, v**3*(2*u-v)/(6*(u-2*v))
m1=lambda x:x**2/2
m2=lambda x,k:x**3/3-k
m3=lambda x,k:x**4/4-3*u*k/2
at2=lambda i,j,x,k:(m2(x,k)-j*m1(x))/(i*(i-j))
at3=lambda i,j,l:(m3(w,k)-(j+l)*m2(w,k)+j*l*m1(w))/(i*(i-j)*(i-l))
fv=factor((k1*at2(u,v,v,k2)+k2*at2(v,u,v,k2))/k2)
assert cancel(fv-(u**3-3*u*v**2+v**3)/(2*(u-2*v)*(2*u-v))) == 0
A=k*(u/2+(fv-u/2)*(w-u)/(v-u))-k1*at3(u,v,w)-k2*at3(v,u,w)-k*at3(w,u,v)
den=72*w*(u-2*v)*(u-w)*(2*u-v)*(v-w)
N=Poly(cancel(den*A),k)
assert N.degree()==2
q = symbols('q')
Nq=Poly(cancel(N.as_expr().subs(k,q/6)),q)
assert Nq.as_expr().is_polynomial(u,v,w,q)
assert expand(Nq.nth(2)*F**2+Nq.nth(1)*M*F+Nq.nth(0)*M**2
    -36*w**4*(u-w)**2*(2*u-v)*(v-w)**2*J**2)==0
assert expand(M*(3*w**4-4*(u+v)*w**3+6*u*v*w**2)+(2*v-u)*F
    -6*w**2*(u-w)*(v-w)*J)==0
assert expand(M-J-3*w*(u**2-3*u*v+v**2))==0
print('exact degree-four calibration, undivided affine/diagonal identities: PASS')

x,t= symbols('x t')
j4=lambda x:42*x**4-84*x**3+56*x**2-14*x+1
j5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x**2-18*x+1)
assert gcd(j4(x),j5(x))==1
for i in range(4):
    assert integrate(X*(1-X)*j5(X)*X**i,(X,0,1))==0
for i in range(4):
    assert integrate(X*(1-X)*j4(X)*X**i,(X,0,1))==0

d=4*t-1-t*t
n=x*t*(1+t)
p=cancel((j5(x)*j4(x*t)-j5(x*t)*j4(x))/(x*(1-t)))
J4z=42*n**4-84*n**3*d+56*n*n*d*d-14*n*d**3+d**4
J5z=(2*n-d)*(66*n**4-132*n**3*d+84*n*n*d*d-18*n*d**3+d**4)
r=cancel((j5(x)*J4z*d-J5z*j4(x))/(x*(d-t*(1+t))))
assert p.is_polynomial(x,t) and r.is_polynomial(x,t)
assert Poly(p,x).nth(0)==6
ss=subresultants(p,r,x)
res=Poly(ss[-1],t,domain=QQ)
assert res.degree()==96
unit, fs=factor_list(res)
assert len(fs)==4
mapping={tuple(a.monic().all_coeffs()):(a,k) for a,k in fs if a.degree()==1}
assert mapping[(1,0)][1]==20 and mapping[(1,-1)][1]==8 and mapping[(1,-2)][1]==8
[(f,mult)]=[(a,k) for a,k in fs if a.degree()!=1]
assert f.degree()==60 and mult==1 and f.is_irreducible
assert f.all_coeffs()==f.all_coeffs()[::-1]
for guard in [t,t-1,t-2,2*t-1,4*t-1-t*t,t*t-3*t+1]:
    assert gcd(f,Poly(guard,t,domain=QQ)).degree()==0
s1=Poly(ss[-2],x)
assert s1.degree()==1
fa=Poly(s1.nth(1),t,domain=QQ).rem(f)
fb=Poly(s1.nth(0),t,domain=QQ).rem(f)
assert gcd(fa,f).degree()==0 and gcd(fb,f).degree()==0
print('resultant: y^20*(y-1)^8*(y-2)^8 times irreducible reciprocal degree 60')
print('linear penultimate subresultant unique u: PASS; every guard coprime')
print('ratio polynomial leading coefficient =', f.clear_denoms()[1].LC())
assert f.count_roots(-S.Infinity,S.Infinity)==12
iv=f.intervals(eps=Q(1,10**8))
assert len(iv)==12 and all(mult==1 for _,mult in iv)
print('12 ordered real ratio isolating intervals (exact rational endpoints):')
for box,m in iv:
    print('  ',box)

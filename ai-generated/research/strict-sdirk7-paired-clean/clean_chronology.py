#!/usr/bin/env python3
import sympy as S
from math import isqrt
x,y,u,z,t,d=S.symbols('x y u z t d')
def chart(t,a):
    qden=t**3-4*t*t-t+2
    r=-2*t*(3*t-2)/qden
    X=[1,1+t,1+2*t]
    A=S.Matrix([[1,0,0],[t,1,0],[2*t-r,r,1]])
    C=S.diag(*X)
    X=S.Matrix(X)
    g=2*A*X-X.multiply_elementwise(X)
    E=3*A*X.multiply_elementwise(X)-X.applyfunc(lambda x:x**3)
    assert S.det(S.Matrix.hstack(g,C*g,A*g))==0
    assert S.det(S.Matrix.hstack(g,C*g,E))==0
    q=S.interpolate(list(zip(X,g)),x)
    assert S.integrate(q,(x,0,a))==q.subs(x,a)
    print('head',t,a,'diag1 tap',r,'g',tuple(g),'q',q,flush=True)
    lam=lambda p:S.expand(sum(w*p.subs(x,x0)/g0 for w,x0,g0 in zip((1,-2,1),X,g)))
    F2=(x-a)*(x-d)
    f=S.expand(F2*(x*lam(F2)-lam(x*F2)))
    return S.expand(f),q,lam
def I(f,r=0):
    return S.expand(sum(v*z**(j+r)/(j+r+1) for (j,),v in S.Poly(f,y).terms()))
def T(f):
    return S.integrate(f,(y,0,y))-f
h=(y-1)*(y-u)
k=-(y*y-4*y+2)/2
def chronology(t,a,rel):
    f,q,la=chart(t,a)
    F2=(y-z+a)*(y-z+d)
    F2=S.expand(F2.subs(d,rel))
    f=S.expand(f.subs(d,rel).subs(x,z-y))
    P=I(T(h)*f); Q=I(T(k)*f)
    W=S.expand(k*P-h*Q)
    L=tuple(I(W*F2,j) for j in range(3))
    e=S.Poly(S.expand(L[1]*L[1]-L[0]*L[2]),u,z,d)
    e=e.clear_denoms()[1].primitive()[1].as_expr()
    fac=S.factor_list(e)
    assert S.expand(e-fac[0]*S.prod(g**k for g,k in fac[1]))==0
    return L,fac

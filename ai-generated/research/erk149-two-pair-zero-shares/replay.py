#!/usr/bin/env python3
"""Exact scalar consequences for the zero-share raw-transpose extension."""
import sympy as S
a,b,c,s,t,k,l,m,pc,pa,pb,e,f = S.symbols("a b c s t k l m pc pa pb e f")
def eq(lhs,rhs=0):
    assert S.cancel(lhs-rhs)==0, (lhs,rhs)

first=3*a/2
K=lambda t: t**2*a**2/2-t**4/4
eq(K(first)/(first**2/(2*a)),-a**3/8)
ka=(a+first)*s**3/3-a*first*s**2/2-s**4/4
va=s**2*(3*first-2*s)/(6*a*(first-a))
eq(ka+a**3*va/8,-s**2*(2*s-3*a)**2/16)
def D(x,w,w1,w2,u):
    return S.Matrix([w1-w*x**2/2,x*(w1-w*x**2/2),w2-w*x**3/3,u])
dc=D(c,1,0,0,0)
da=D(a,e,k*c,k*c**2,-k*c**2/2)
db=D(b,f,l*c+m*e*a,l*c**2+m*e*a*a,-l*c**2/2+m*(k*c-e*a**2/2))
U,V=pa*k+pb*l,pb*m
r=pc*dc+pa*da+pb*db
ms=lambda j: pc*c**j+pa*e*a**j+pb*f*b**j
eq(r[0],c*U+e*a*V-ms(2)/2)
eq(r[2],c**2*U+e*a*a*V-ms(3)/3)
eq(r[3],-(c*c*U+e*a*a*V)/2+V*k*c)
eq(r[1]-b*r[0],(a-b)*pa*k*c+b*ms(2)/2-ms(3)/2)
for ea,eb in [(1,0),(0,1)]:
    v=r.subs({e:ea,f:eb})
    eq(v[0],(c*U+ea*a*V)-ms(2).subs({e:ea,f:eb})/2)
    eq(v[2],(c*c*U+ea*a*a*V)-ms(3).subs({e:ea,f:eb})/3)
eq((6*b*c-4*(b+c)*t+3*t*t).subs(t,2*c),2*c*(2*c-b))
eq(((b+c)*s**3/3-b*c*s**2/2-s**4/4).subs(b,2*c),-s**2*(s-2*c)**2/4)
w0,w1,w2,yt=S.symbols("w0 w1 w2 yt")
row=S.Matrix([[0,0,0],[w0,0,0],[w1,w2,0]])
Y=S.diag(0,c,a)
W=S.Matrix([1,1,0])
# For path length one/two the weighted target is paid by T W=Y W.
Ua=row*Y*W-Y**2*W/2
Ga=row*Y**2*W-Y**3*W/3
Ha=row*Ua
paid={w0:c,w1:-w2}
assert (row*W-Y*W).subs(paid).applyfunc(S.cancel)==S.zeros(3,1)
assert (row*(S.eye(3)-Y)*W-(Y-Y**2/2)*W+Ua).subs(paid).applyfunc(S.cancel)==S.zeros(3,1)
assert (row**3*W-Y**3*W/6-Ga/2-Ha).subs(paid).applyfunc(S.cancel)==S.zeros(3,1)
print("Raw ghost-word identities, weighted-donor resonance and both strict cubic-square obstructions verified exactly.")

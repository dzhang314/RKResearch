#!/usr/bin/env python3
"""Exact characteristic-zero arithmetic for the middle live-fourth packet."""
import sympy as S
x,Y,z,r,s=S.symbols('x Y z r s')

def primitive(p,X):
    return S.Add(*(c*X**(i+1)/S.Integer(i+1)
                   for (i,),c in S.Poly(p,X).terms()))
def integral_moments(p,X,n):
    P=S.Poly(p,X)
    return [sum(c/S.Integer(i+k+1) for (i,),c in P.terms()) for k in range(n)]

# Normalize Y=z*x and the cubic gauge. Exact rho interpolation on R
# is multiplication by m in the 3-dimensional quotient; use no inverse
# before exhibiting its determinant and adjugate identities.
m=x*x+r*x+s
P=x*m
F=S.cancel(primitive(P,x)/x)
R=S.expand(S.Rational(4,5)*(F+(x-1)*m))
rhs=S.cancel(primitive(primitive(P,x),x)/x)
def row(f):
    a=S.Poly(S.rem(f,R,x),x)
    return S.Matrix([a.nth(i) for i in range(3)])
M=S.Matrix.hstack(*(row(x**j*m) for j in range(3)))
D=S.expand(M.det(method="domain-ge"))
N=S.expand(sum(M.adjugate()*row(rhs)))
assert S.expand(D+S.Rational(1,225)*s**2*(2*r*r-9*s))==0
assert S.expand(10*(2*r*r-9*s)*N+(r*r-r*s-6*s)*D)==0
print("exact slope −1: rho(1)=0 forces r²=(r+6)s with live old multiplication determinant",flush=True)

ma=Y*Y+r*z*Y+s*z*z
Fa=S.cancel(primitive(Y*ma,Y)/Y)
Ra=S.Rational(4,5)*(Fa+(Y-z)*ma)
clear=S.cancel((r+6)*Ra.subs(s,r*r/(r+6)))
assert S.denom(clear) in S.QQ
# z is fifth ordinary site. B=z, V is the only other non-old site.
h=integral_moments(Y*(1-Y)*(Y-z)*clear,Y,5)
f=lambda i,j:S.expand(h[i]*h[j+1]-h[i+1]*h[j])
gcd=S.Poly(S.resultant(f(0,1),f(0,2),r),z,domain=S.QQ)
for i,j in [(0,3),(1,2)]:
    gcd=S.gcd(gcd,S.Poly(S.resultant(f(0,1),f(i,j),r),z,domain=S.QQ))
assert gcd.monic()==S.Poly(z**12,z,domain=S.QQ)
print("fifth twin: three necessary rank-two resultants have exact gcd z^12 (no moment pivot inversions)",flush=True)

# z is the actual origin clock, and V,B are both distinct nonendpoint;
# the masked hull is Y*(1-Y)*R*(Y-V)*(Y-B), without double endpoint.
j=integral_moments(Y*(1-Y)*clear.subs(z,1),Y,6)
H=S.Matrix(4,3,lambda i,k:j[i+k])
first=H[[0,1,2],:].det(method="domain-ge")
second=H[[0,1,3],:].det(method="domain-ge")
assert S.Poly(S.gcd(first,second),r,domain=S.QQ).is_one
print("origin: the two necessary rank-three ordinary minors are exactly coprime",flush=True)

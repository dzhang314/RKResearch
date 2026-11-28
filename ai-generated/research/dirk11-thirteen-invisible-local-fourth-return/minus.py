#!/usr/bin/env python3
"""Exact rational identities and all clock resultants for slope minus one."""
from functools import reduce
from itertools import combinations
import sympy as S

Y,r,s,z,a=S.symbols('Y r s z a')
def integral(q):
    return S.Add(*(v*Y**(i+1)/S.Integer(i+1) for (i,),v in S.Poly(q,Y).terms()))
def moments(q,n):
    p=S.Poly(q,Y)
    return [sum(v/S.Integer(i+k+1) for (i,),v in p.terms()) for k in range(n)]
def hankel_minors(M):
    H=S.Matrix(4,3,lambda i,j:M[i+j])
    return [H[list(t),:].det(method='domain-ge') for t in combinations(range(4),3)]
def gcdpoly(fs,x):
    return reduce(S.gcd,[S.Poly(q,x,domain=S.QQ) for q in fs]).monic()
def res_gcd(fs,which,eliminate,keep):
    return gcdpoly([S.resultant(fs[0],fs[i],eliminate) for i in which],keep)

m=Y*Y+r*Y+s
P=Y*m
F=S.cancel(integral(P)/Y)
J=S.cancel(integral(integral(P))/Y)
v=S.Matrix.hstack(*(S.Matrix([S.Poly(S.rem(F*Y**j,m,Y),Y).nth(i)
                                for i in range(2)]) for j in range(2)))
assert S.expand(v.det()+s*s*(2*r*r-9*s)/144)==0
c=2*r*r-9*s
psiN=2*((4*r*r-21*s)*Y-r*s)
xiN=-Y*((r*r-6*s)*Y-r*s)
assert S.expand(10*c*J-psiN*F-xiN*m)==0
assert S.cancel((psiN/(10*c)).subs(s,r*r/(r+6))-
                ((4*r+3)*Y-r)/(5*(2*r+3)))==0
print("minus normalized affine second primitive and remainder: exact coefficient certificate",flush=True)

# Earlier old repeated/old-twin contact with ell=−(Y−a) forces t=6/25.
Ra=(Y-a)*(Y*Y-S.Rational(27,25)*a*Y+S.Rational(6,25)*a*a)
assert gcdpoly(hankel_minors(moments(Y*(1-Y)*Ra,6)),a).is_one
print("minus common old root: all four exact Hankel minors have gcd 1",flush=True)

# Earlier weighted fifth or origin common root. Here Xi(1)=0 gives
# s=r²/(r+6) after scaling by the literal common-root clock z.
mh=(r+6)*Y**2+r*(r+6)*z*Y+r*r*z*z
Fh=Y*((r+6)*Y*Y/4+r*(r+6)*z*Y/3+r*r*z*z/2)
Rh=Fh+(Y-z)*mh
M=moments(Y*(1-Y)*(Y-z)*Rh,5)
ff=[M[i]*M[j+1]-M[i+1]*M[j] for i,j in ((0,1),(0,2),(0,3),(1,2))]
assert res_gcd(ff,(1,2,3),r,z)==S.Poly(z**12,z,domain=S.QQ)
ho=hankel_minors(moments(Y*(1-Y)*Rh.subs(z,1),6))
assert gcdpoly(ho[:2],r).is_one
print("minus common root at fifth/origin: exact gcds z^12 and 1",flush=True)

# Consecutive B with d_B=0 gives ell I²P = rho IP. The only
# live-constant coefficient solution yields opposite old signs.
Ps=Y*(Y**2-2*a*Y+5*a*a/6)
IPs=integral(Ps); I2s=integral(IPs)
rhoS=-Y*Y/5+a*Y/3
assert S.expand((a-Y)*I2s-rhoS*IPs)==0
assert S.expand(IPs.subs(Y,a))==0
assert S.expand(I2s.subs(Y,a)-a**5/45)==0
assert S.expand((rhoS*Ps).subs(Y,a)+a**5/45)==0
print("minus zero diagonal at consecutive fifth: exact opposite old primitive signs",flush=True)

# Consecutive B with D0_B=0: normalized (2r+4)(B/V)=3r+5.
# Keep the free literal root of ell, rather than setting it to V.
common=Y*(1-Y)*(Y-z)*((2*r+4)*Y-(3*r+5)*z)
A=moments(common*(Fh+Y*mh),4); B=moments(common*mh,4)
minors=[S.Poly(A[i]*B[j]-A[j]*B[i],r,z,domain=S.QQ)
           .clear_denoms()[1].primitive()[1].as_expr()
        for i,j in ((0,1),(0,2),(0,3),(1,2))]
assert res_gcd(minors,(1,2,3),r,z)==S.Poly(z**16,z,domain=S.QQ)
print("minus consecutive matched fifth: exact ordinary determinant gcd z^16",flush=True)

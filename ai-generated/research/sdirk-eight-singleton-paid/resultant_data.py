#!/usr/bin/env python3
"""Exact rational singleton slope polynomials and their bad-characteristic support."""
from sympy import QQ,CRootOf,Symbol,ring
from math import isqrt,prod

a=Symbol('a')
minpoly=70*a**4-140*a**3+90*a*a-20*a+1
K=QQ.algebraic_field(CRootOf(minpoly,0))
aa=K.unit
S,u=ring('u',K)
T,h=ring('h',K)
R,z=ring('z',T)
C,A=ring('a',QQ)
M=A**4-2*A**3+QQ(9,7)*A*A-QQ(2,7)*A+QQ(1,70)
G=(4+35*aa*(1-aa))/72
invG=(864-3456*G)/49
assert G*invG==K.one
LL=invG-2

def as_poly(b):
    return sum((C(q)*A**j for j,q in enumerate(b.to_list()[::-1])),start=C.zero)
def norm(b):
    return M.resultant(as_poly(b))

def data(a):
    c=G*(1+u)
    P=c**3+(a-2)*c*c+(a*a-2*a+QQ(9,7))*c+a**3-2*a*a+QQ(9,7)*a-QQ(2,7)
    p,d1,d2,d3=[P.get((i,),K.zero) for i in range(4)]
    e=lambda d:R(T(d))
    d,d1r,d2r,d3r=map(e,(p,d1,d2,d3))
    k=1+2*z-z*z
    Ky=d1r-2*d+(d2r+d)*z+d3r*z*z
    Q=2*(d2r+2*d3r+d)*z**3+(3*d1r-4*d2r+7*d3r-10*d)*z*z+(-8*d1r+5*d2r-6*d3r+15*d)*z+4*d1r-2*d2r-6*d
    return p,d2+2*d3+p,Q.resultant(Ky-d*k*R(h))
p,star,F=data(aa)
pr,starr,Fr=data(1-aa)
VF=sum((Fr.get((j,),K.zero)*(-h)**j*(1+LL*h)**(3-j) for j in range(4)),start=T.zero)
assert F.degree()==VF.degree()==3
resultant=F.resultant(VF)

def paid(d):
    for q in (2,3,5,7):
        while d%q==0:d//=q
    return d==1

for elem in [p,pr,G,invG,star,starr,resultant,*F.values(),*VF.values()]:
    assert all(paid(c.denominator) for c in elem.to_list())
assert norm(p)==norm(pr)
assert norm(star)==norm(starr)
small_guard=(29,101,1453,523357)
star_guard=(613,118709,5428349)
assert abs(int(norm(p).numerator))==29**2*101**2*1453**2*523357
assert abs(int(norm(star).numerator))==prod(star_guard)
small_result=(601,6277)
PRIMES=tuple(sorted(small_guard+star_guard+small_result))
assert all(q>7 and all(q%i for i in range(2,isqrt(q)+1)) for q in PRIMES)
rr=abs(int(norm(resultant).numerator))
s=isqrt(rr)
assert s*s==rr and s%prod(small_result)==0
N=s//prod(small_result)
assert len(str(N))==229

if __name__=='__main__':
    print('constant guard norm:',norm(p))
    print('star guard norm:',norm(star))
    print('exception prime fields:',PRIMES)
    print('remaining modulus digits:',len(str(N)))

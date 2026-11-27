#!/usr/bin/env python3
import sympy as S
from sympy.polys.matrices import DomainMatrix
a,q,r=S.symbols('a q r')
l0=[q**2*r**2*(q-r)*(4-3*q-3*r+2*q*r),-r*r*(1-r)**2,q*q*(1-q)**2]
l1=[2*q**4*(1-q)*(2-q),2*q*(1-2*q)*(1-q),0]
c=[S.Integer(1),q,r]
d=[S.prod(x-a for i,x in enumerate(c)if i!=j)for j in range(3)]
colJ=lambda l:[S.expand(sum(u*x**(k+1)*v/(k+1)for u,x,v in zip(l,c,d)))for k in range(1,5)]
colE=lambda l:[S.expand(sum(u*x**k for u,x in zip(l,c)))for k in range(1,5)]
rhs=[a**(k+1)/(k+1)for k in range(1,5)]
M=[colJ(l0),colJ(l1),colE(l0),colE(l1)]
def det(xs):
    D=DomainMatrix.from_Matrix(S.Matrix(xs).T).to_field()
    return S.factor(D.domain.to_sympy(D.det()))
for i in [2,3]:
    x=M if i==4 else M[:i]+[rhs]+M[i+1:]
    got=det(x)
    expected=0 if i==2 else a**2*q**7*r**3*(q-a)**2*(r-a)**3*(a-1)**2*(q-1)**6*(q-r)**2*(r-1)**2/5
    assert S.expand(got-expected)==0
    print(i,got,flush=True)

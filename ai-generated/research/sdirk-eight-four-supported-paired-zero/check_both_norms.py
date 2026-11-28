#!/usr/bin/env python3
"""Both third rows zero: Gaussian clock pairs in the paired all-live graph."""
import sympy as S
from sympy import QQ,CRootOf,ring
from math import gcd
x=S.Symbol('x')
Q=lambda x:4*x**3-12*x*x+3*x+2
a=CRootOf(Q(x),0);b=CRootOf(Q(x),1)
K=QQ.algebraic_field(a,b)
u=K.from_sympy(a);v=K.from_sympy(b);o=K.one
R,t=ring('T',QQ)
def poly(a):
 return sum((R(c)*t**i for i,c in enumerate(a.to_list()[::-1])),start=R.zero)
M=sum((R(c)*t**i for i,c in enumerate(K.mod.to_list()[::-1])),start=R.zero)
def norm(y):return abs(int(M.resultant(poly(y)).numerator))
def strip(n):
 for p in (2,3,5,7):
  while n and n%p==0:n//=p
 return n

x,y=S.symbols('x y')
Qv=S.div(Q(y)-Q(x),y-x,y)[0]
assert S.Poly((y-x)*Qv-(Q(y)-Q(x)),y,x).is_zero
gb=S.groebner([Q(x),Qv],y,x,domain=QQ)
def guard(e):
    for c in S.Poly(e,S.Symbol('T'),y,x,domain=QQ).coeffs(): assert strip(int(S.denom(c)))==1
for p in gb.polys:guard(p.as_expr())
for p,target in [(poly(u),x),(poly(v),y),(M,0)]:
    e=p.as_expr().subs(S.Symbol('T'),x+2*y)-target
    qs,rem=gb.reduce(e)
    assert rem==0
    for f in (e,*qs):guard(f)
def L(x,h):return 35*x**4-30*x*x*h*h+3*h**4
def test(a,b,d):
 h=d+2
 return strip(gcd(norm(L(4*a-d,h)),norm(L(4*b-d,h))))

assert M.degree()==6
for a,b,ps in (
 (u,v,[('midpoint',K.zero,267613**2),('forward other fixed',u,1),('reflected other fixed',v,1),
       ('both third graph site',u+v,4271*8150279*16397761)]),
 (u,u,[('midpoint',K.zero,267613**2),('both third graph site',2*u,3517**2)])
):
 for name,lam,wanted in ps:
    for h in (lam,a,b,L(4*a-lam,lam+2),L(4*b-lam,lam+2)):guard(poly(h).as_expr())
    n=test(a,b,lam)
    assert n==wanted
    print('equal' if a==b else 'unequal',name,n)

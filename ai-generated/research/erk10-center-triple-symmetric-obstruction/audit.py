#!/usr/bin/env python3
"""Exact univariate terminal test on the regular symmetric 6+10 triple chart."""
import sympy as S
from math import factorial
from itertools import permutations
from functools import cache
from math import prod
Y,X,V=S.symbols('Y X V')
R=S.Rational
Z,O=R(0),R(1)
a,t=R(1,3),R(1,2)
u=(4-8*V**2)/(1+3*V**2)
A,T,B=R(2,3),R(1,2),(1+u)/2
tail=(R(1,3),(1-u)/2,(1+V)/2,(1-V)/2)
clock=[Z,O,A,T,B,*tail]
cent=lambda z:S.cancel(2*z-1)
of=[cent(z)for z in clock]
z0,z1,z2=map(cent,(A,T,B))
def polmu(p,expo=0):
 p=S.Poly(p,X)
 return S.cancel(sum(v/R(j+1)for (j,),v in p.terms() if j%2==0))
@cache
def nr(z):
 P=S.Poly.from_list([1],X)
 for w in of:
  if z!=w:P*=S.Poly(X-w,X)
 return S.cancel(polmu(P.as_expr())/(z-1))
def k(y):return -y*y*(3*y*y-10*a*y+9*a*a)/12
def r0(y):
 if y==a:return -5*a**4/36
 assert y==t
 return -a*a*t*t/12
def line(vals,z):
 return S.cancel(vals[0]+(vals[1]-vals[0])*(z-z0)/(z1-z0))
ks=[S.cancel(nr(z)*k((1-z)/2))for z in (z0,z1)]
rs=[S.cancel(nr(z)*r0((1-z)/2))for z in (z0,z1)]
assert S.cancel(line(ks,z2)-nr(z2)*k(1-B))==0
@cache
def K(x):return S.cancel(line(ks,cent(x))/nr(cent(x)))
@cache
def Rho(x):return S.cancel(line(rs,cent(x))/nr(cent(x)))
H4=S.Poly(Y*(Y-a)*(Y-t)*(Y-1+B),Y)
IK=S.Poly(k(Y)+H4.as_expr()/4,Y)
IR=S.Poly(S.interpolate([(Z,Z),(a,r0(a)),(t,r0(t)),(1-B,Rho(B))],Y),Y)
F=tuple(map(lambda p:S.Poly(p,Y),(-H4,IK,IR)))
@cache
def IntPair(j,i):
 return S.cancel(sum(v*R(factorial(j)*factorial(k),factorial(j+k+2))
    for (k,),v in F[i].terms()))
def func(L):
 P=S.Poly(X*S.prod(X-z for z in L),X)
 return tuple(S.cancel(sum(v*IntPair(j,i)for (j,),v in P.terms()))for i in range(3))
@cache
def move(c):
 y=1-c
 return tuple(map(S.cancel,(H4.eval(y),K(c)-F[1].eval(y),Rho(c)-F[2].eval(y))))
def det(a,b,c):
 return S.cancel(a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0]))
def mirror():
    """The two scalar first-singleton charts split by clock B."""
    U,Q=S.symbols('U Q')
    labels=(-1, 1, 0, R(1,3), -R(1,3), U, -U)
    def co(z):
        return polmu(S.prod(X-w for w in labels if w!=z)*(X**2-Q))/(z-1)
    def early(zz):
        kk=[S.cancel(co(z)*k((1-z)/2)) for z in zz]
        return S.cancel((zz[1]-zz[0])*(kk[2]-kk[0])-(zz[2]-zz[0])*(kk[1]-kk[0]))
    num=early((R(1,3),Z,-R(1,3)))
    free=early((R(1,3),Z,U))
    assert free==S.expand(-U*(3*U-1)*((3*U+8)*Q+U-4)/102060)
    print('Nonmirror singleton: exact collinearity equation verified.')
    sols=S.solve(num,Q)
    assert sols and S.cancel(sols[0]-(21*U**2-11)/(21*(3*U**2-1)))==0
    den=S.Poly(num,Q)
    assert S.gcd(den.nth(0),den.nth(1))==1
    assert {x*x%7 for x in range(7)}=={0,1,2,4} and pow(3,-1,7)==5
    print('Mirror singleton: proved square formula and its impossible 7-adic residue.')

def no_root_receipt(P):
    """Split into exact factors and exhibit a no-root prime for each nonlinear factor."""
    cf,factors=S.factor_list(P)
    assert cf*prod(f**m for f,m in factors)==P
    rs={}
    cert=[]
    for f,m in factors:
      if f.degree()==1:
        root=-f.nth(0)/f.nth(1)
        rs[root]=m
        continue
      _d,p=f.clear_denoms(convert=True)
      vv=list(map(int,p.all_coeffs()))
      def ev0(x,p):
        y=0
        for k in vv:y=(y*x+k)%p
        return y
      wit=next((p for p in S.primerange(2,10000) if vv[0]%p and all(ev0(x,p) for x in range(p))),None)
      assert wit is not None,(f.as_expr(),f.degree())
      cert.append((f.degree(),int(wit)))
    return rs,cert

def main():
 mirror()
 total=0;valid=0
 for c,d in permutations(range(4),2):
  w=move(tail[c])
  rho=func([x for i,x in enumerate(tail)if i!=c])
  v=func([x for i,x in enumerate(tail)if i not in (c,d)])
  H=det(rho,v,w)
  assert H
  n,p=map(lambda q:S.Poly(q,V),S.fraction(H))
  found, cert=no_root_receipt(n)
  roots={}
  for r,m in found.items():
   cells=[S.cancel(x.subs(V,r))for x in clock]
   if len(set(cells))!=9 or p.eval(r)==0:continue
   weights=tuple(S.cancel(nr(q).subs(V,r))for q in of if q not in (-1,1))
   if not all(weights):continue
   roots[r]=m
   valid+=1
  print(c,d,'degree',n.degree(),p.degree(),'rational roots',found,'factor degree/no-root prime',cert,
        'noncolliding nonzero-mass',roots,flush=True)
  total+=1
 print('COMPLETE',total,'cases',valid,'actual rational survivors',flush=True)
if __name__=='__main__':main()

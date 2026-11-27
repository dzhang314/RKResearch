#!/usr/bin/env python3
"""Exact elimination of ghost-clock aliases on the u=0 reflection terminal cut."""
import sympy as S
from time import monotonic
from math import prod
z,x,c=S.symbols("z x c")
a,b,d=S.symbols("a b d")
R=x*(x-1)*(x-4)
L=x**3-a*x*x+b*x-d
def I(f):
 p=S.Poly(f,x)
 return sum(y*z**(j[0])/(j[0]+1) for j,y in p.terms())
def H(q):
 return (z**6+3*(2*q-z)**2*z**4+5*(6*q*q-6*q*z+z*z)**2*z*z+
         7*(20*q**3-30*q*q*z+12*q*z*z-z**3)**2)
K0,K1,K4=[S.factor(I(S.cancel(R/(x-j))*L)) for j in (0,1,4)]
F0=S.factor(I(R*L))
L3=c**3-9*c*c+18*c-6
K=I(R*(x*x+(c-a)*x+(c*c-a*c+b)))
starts=monotonic()
save=[]
def rootless(f):
 for p in S.primerange(3,2000):
  u=S.Poly(f,z,modulus=p)
  if u.degree()==S.degree(f,z) and all(u(k)%p!=0 for k in range(p)):
   return p
 raise AssertionError("no rootlessness certificate")
expected={0:((3,3,9),None),1:((2,3,6,18),S.Integer(2)),
          4:((2,3,6,18),S.Integer(8)), 'early':((3,15),None)}

for i in (0,1,4,'early'):
 f=[F0]
 if i==0:
  f += [2*K4+K1,H(0)*K0-z**6*4*L.subs(x,0)]
  kap=-K1/2
 elif i==1:
  f += [K4-K0,H(1)*K1+z**6*3*L.subs(x,1)]
  kap=K0
 elif i==4:
  f += [2*K0+K1,H(4)*K4-z**6*12*L.subs(x,4)]
  kap=K0
 else:
  f += [K4-K0,2*K0+K1]
 mat,wei=S.linear_eq_to_matrix(f,(a,b,d))
 det=S.factor(mat.det())
 print('case',i,'det',det,flush=True)
 dscale, ds=S.factor_list(det)
 assert S.expand(dscale*prod(g**n for g,n in ds)-det)==0
 detroots=set()
 for g,n in ds:
  dg=S.degree(g,z)
  if dg>1:
   rootless(g)
  else:
   detroots.add(-S.Poly(g,z).nth(0)/S.Poly(g,z).nth(1))
 spec=expected[i][1]
 assert detroots == ({0} if spec is None else {0,spec})
 if spec is not None:
  # These are the actual left-null contradictions, not a lost determinant branch.
  M0,b0=mat.subs(z,spec),wei.subs(z,spec)
  witness={1:S.Matrix([-288,-S.Rational(504,5),1]),
           4:S.Matrix([-S.Rational(2211840,13),-S.Rational(589824,13),1])}[i]
  assert witness.T*M0==S.zeros(1,3) and witness.dot(b0)!=0
 print("Cramer poles",detroots,"excluded exactly",flush=True)

 sol=[S.factor(x/det) for x in (mat.adjugate()*wei)]
 env=dict(zip((a,b,d),sol))
 l=S.factor(L.subs(x,c).subs(env))
 if i=='early':
  j=S.factor((K*H(c)-z**6*R.subs(x,c)*S.diff(L,x).subs(x,c)).subs(env))
 else:
  j=S.factor((L3*K+2*(c+3)*kap).subs(env))
 nl=S.fraction(l)[0]
 nj=S.fraction(j)[0]
 res=S.factor(S.resultant(nl,nj,c))
 sc,fr=S.factor_list(res)
 assert S.expand(sc*prod(g**n for g,n in fr)-res)==0
 degrees=[];certs=[];roots=set()
 for g,n in fr:
  dg=S.degree(g,z)
  if dg==1:
   roots.add(-S.Poly(g,z).nth(0)/S.Poly(g,z).nth(1))
  else:
   degrees.append(dg);certs.append(rootless(g))
 assert tuple(sorted(degrees))==expected[i][0]
 assert roots==({0} if spec is None else {0,spec})
 print("projection nonlinear degrees",degrees,"projective rootless primes",certs,flush=True)
 print("all rational projected roots excluded",roots,flush=True)

#!/usr/bin/env python3
"""Exact symbolic regular-family gate and separate rational exceptional prefix."""
from fractions import Fraction as F
from functools import cache
from math import prod,lcm
from pathlib import Path
import json
import sympy as S
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'erk10-sixteen-f17'))
from rooted import trees,tf,size
f,v,r,g,X=S.symbols('f v r g X')
a=S.Rational

def tableau():
 return [[],[a(2,3)],[a(1,4),a(3,4)],[1,-3,4],[1-2*f,9*f-3,4-8*f,f],
   [v*(4*v*v-13*v+12)/12,-3*v*v*(v-2)/4,v*v*(v-1)/3,-v*v*(v-1)*(-f+v-2)/(12*f),v*v*(v-2)*(v-1)/(12*f)],
   [(-6*g*r*v*v+18*g*r*v-12*g*r-8*g*v**3+36*g*v*v-52*g*v+24*g+4*r**4-21*r**3+38*r*r-24*r)/(12*(r-2)),
    -3*(-4*g*v**3+12*g*v*v-8*g*v+r**4-4*r**3+4*r*r)/(4*(r-2)),
    (3*g*r*v*v-6*g*r*v-8*g*v**3+18*g*v*v-4*g*v+r**4-3*r**3+2*r*r)/(3*(r-2)),
    -(6*f*g*r*v*v-6*f*g*r*v-4*f*g*v**3+4*f*g*v-f*r**4+3*f*r**3-2*f*r*r-3*g*r*v**3+7*g*r*v*v-4*g*r*v+6*g*v**3-14*g*v*v+8*g*v+r**5-5*r**4+8*r**3-4*r*r)/(12*f*(r-2)),
    (-3*g*v**3+7*g*v*v-4*g*v+r**4-3*r**3+2*r*r)/(12*f),g]]
def phi(A,scal=lambda x:x):
 @cache
 def val(t):
  p=[ast(z)for z in t]
  return [scal(prod(u[i]for u in p))for i in range(len(A))]
 @cache
 def ast(t):
  return [scal(sum(q*u for q,u in zip(r,val(t))))for r in A]
 return val

def symbolic():
 P=phi(tableau(),S.factor)
 clocks=(0,a(2,3),1,2,2,v,r)
 tall=lambda n: () if n==1 else (tall(n-1),)
 E=(tall(3),tall(4),((),tall(3)),((),(),tall(3)),(((),(),(),()),),(((),tall(3)),))
 cols=[tuple(S.factor(z-a(size(t),tf(t))*x**(size(t)-1))for z,x in zip(P(t)[1:],clocks[1:]))for t in E]
 D=S.Matrix(cols[:3])
 assert D[:,0:3].det()==a(2,81)
 L=((-D[:,0:3].inv()*D[:,3:6]).applyfunc(S.factor)).col_join(S.eye(3))
 guard=4*(r-2)
 assert all(S.Poly(S.cancel(x*guard),f,v,r,g).get_domain().is_ZZ for x in L)
 assert (D*L).applyfunc(S.cancel)==S.zeros(3,3)
 S0=(S.Matrix(cols[3:])*L).applyfunc(S.factor)
 dev=S.factor(S0.det(method='domain-ge'))
 assert S.cancel(dev-(-4*f*g*v**3*(r-v)*(v-2)**3*(v-1)**2/45))==0
 print('Small determinant 2/81, paid projection, and regular projected determinant verified.')
 REL=((((),()),a(-14,27)),(tall(3),a(-8,27)),(((),(),()),1),(tall(4),-2),(((),(),(),()),a(-1,3)),(((),tall(3)),1))
 for i in range(7):
  z=S.cancel(sum(c*P(t)[i]for t,c in REL).subs(g,0))
  assert z==0
 get=S.factor(sum(c*X**size(t)/tf(t)for t,c in REL))
 assert S.cancel(get+X**3*(3*X*X-15*X+20)/90)==0
 print('Six-term actual g=0 rooted relation and negative discriminant verified.')

def literal():
 d=json.loads((HERE/'rational-prefix.json').read_text())
 A,Pi,H6=([[F(z)for z in r]for r in d[k]] for k in ('A','Pi','H6'))
 t=F(d['theta']);assert t==F(5,2)
 assert F(d['v'])==t*(12*t*t-45*t+40)/(15*(t-2)**2)==F(5,3)
 sym=tableau()
 assert A[:7]==[[F(S.sympify(x).subs({f:1,g:1,v:F(5,3),r:F(5,3)}))for x in w]for w in sym]
 assert all(len(r)==i for i,r in enumerate(A))
 assert len({tuple(r+[0]*(len(A)-len(r)))for r in A})==8
 P=phi(A)
 Y=lambda t: [sum(x*a for x,a in zip(w,P(t)))for w in Pi]
 M=[]
 for h in range(1,6):
  for u in trees(h):
   M.append(P(u))
   assert Y(u)==[F(h,tf(u))*(j==h-1)for j in range(5)]
 assert S.Matrix(M).rank()==8
 assert [sum(t**(k+1)*Pi[k][i]/(k+1)for k in range(5))for i in range(8)]==A[-1]+[F(0)]
 RR=[]
 for u in trees(6):
  q=[-z for z in Y(u)]+[F(6,tf(u))]
  assert not q[0] and not sum(z*t**k for k,z in enumerate(q))
  RR.append(q)
 assert S.Matrix(RR).rank()==3
 def unit(n):
  a=abs(n)
  if not a:return False
  for p in (2,3,5,7):
   while a%p==0:a//=p
  return a==1
 for row in A+Pi+H6:assert all(unit(x.denominator)for x in row)
 B={}
 for row in H6:
  j=next(i for i,x in enumerate(row)if x)
  assert j not in B and unit(row[j].numerator)
  B[j]=[x/row[j]for x in row]
 for residual in RR:
  for j in sorted(B):residual=[a-residual[j]*b for a,b in zip(residual,B[j])]
  assert not any(residual)
 print('Distinct 8 physical rows, all 17 dense identities, literal endpoint, rank 3 through size six.')
 print('Paid common matrix/decoder denominators:',lcm(*(a.denominator for r in A for a in r)),
       lcm(*(a.denominator for r in Pi for a in r)))
 print('All 20 higher residuals expressed in 3 basis rows using paid pivots.')

if __name__=='__main__':symbolic();literal()

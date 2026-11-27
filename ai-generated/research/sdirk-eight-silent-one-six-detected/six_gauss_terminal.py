"""Single invisible stage, detected h on six active, Gauss terminal."""
import sympy as S
from itertools import product
from flint import nmod_poly
p,t=1129,203
def inv(x):return pow(int(x)%p,-1,p)
def L4(x):return (70*x**4-140*x**3+90*x*x-20*x+1)%p
def lead(g,c,r):
 P=nmod_poly([1],p)
 for x in c:P*=nmod_poly([-x,1],p)
 return (sum(int(P[j])*pow(int(r),j+1,p)*inv(j+1) for j in range(P.degree()+1))-g*int(P(r)))%p
def g3n(u):
 h=-2+u+4*u*u-u**3
 return ((1+4*u-4*u*u)*h+4*u*u*(3*u-2))%p

def main():
 assert S.isprime(p) and (2*t*t-1)%p==0
 G=[j for j in range(p) if not L4(j)]
 assert G==[100,214,916,1030]
 count=0
 for g,c in product(G,G):
  x=(1-g)%p
  if c==x:continue
  u=(x-c)*inv(g)%p;k=(1+2*u-u*u)%p
  # Both terminal clocks Gauss, or an active third reverse Gauss clock.
  assert k and (u-2)%p and (2*u+k*(u-2))%p
  assert g3n(u*inv(2)%p)
 for g,sg,st,bk in product(G,(1,-1),(True,False),(True,False)):
  x=(1-g)%p;u=(1+sg*2*t)%p
  d=(x-g*(2-u if bk else 2*u))%p
  assert L4(d)
 for g,u,sign,st,c in product(G,(2,1+2*t,1-2*t),(1,-1),(True,False),G):
  a=g*(2+sign*2*t)%p
  b=g*(2-sign*2*t if st else 3+sign*4*t)%p
  r=(1-g-g*u)%p
  assert r!=a and r!=b
  assert lead(g,[a,b],c)
  assert lead(g,[a,b,r],c)
  count+=1
 print('Gauss terminal detected-six: exact scalar gate orientations',count)
if __name__=='__main__':main()

"""Solve the exact reflected quadratic for each emitted rational triple.

A degenerately zero polynomial is reported separately, never counted as
an obstruction. This script does not claim a global search.
"""
from fractions import Fraction as Q
from math import isqrt, prod
from sys import stdin

def paid(n):
    n=abs(n)
    if not n:return False
    for p in (2,3,5):
        while n%p==0:n//=p
    return n==1

def pair_mul(x,y):return x[0]*y[0],x[0]*y[1]+x[1]*y[0],x[1]*y[1]
def H3(T):
 return Q(1,5)+sum(x*y for j,x in enumerate(T) for y in T[j+1:])/3,sum(T)/3+prod(T)
def solve_v(a,u,w):
 if len({a,u,w,-a})<4:return ()
 ku=(1+2*u+4*a*u-2*a*a-u*u)/(a+1)**2
 kw=(1-2*w-4*a*w-2*a*a-w*w)/(a+1)**2
 H0,H1,H3_,H4=[H3([x for j,x in enumerate((a,u,w,-a)) if i!=j]) for i in range(4)]
 L3=[(u-w)*x+ku*(w-a)*y for x,y in zip(H0,H1)]
 L4=[((u+a)*x-2*a*ku*y)*kw for x,y in zip(H0,H1)]
 c,b,d=[x-y for x,y in zip(pair_mul(L3,H4),pair_mul(L4,H3_))]
 if not d:
  if not b:
   if not c:
    print('identical back gate',a,u,w,flush=True)
   return ()
  return (-c/b,)
 D=b*b-4*d*c
 if D<0:return ()
 n,m=isqrt(D.numerator),isqrt(D.denominator)
 if n*n!=D.numerator or m*m!=D.denominator:return ()
 return tuple((-b+i*Q(n,m))/(2*d) for i in (-1,1))
if __name__=='__main__':
 n=nr=0
 for ln in stdin:
  g,d,w=[Q(*p) for p in [list(map(int,ln.split()[i:i+2])) for i in (0,2,4)]]
  a=2*g-1;u=a+2*d;n+=1
  for v in solve_v(a,u,w):
   nr+=1
   if len({a,u,v,w,-a})==5 and paid(v.denominator):
    print('rational paid candidate for separate full checking:',a,u,v,w)
 print('survivors, rational quadratic roots',n,nr)

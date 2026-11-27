"""Polynomials over Q(t), t²=1/2, in the row-four clock s."""
from dataclasses import dataclass
from flint import fmpq_poly as P, fmpq as Q

@dataclass
class E:                       # coefficients a(xi)+t b(xi), t²=1/2
 a:P
 b:P
 def __init__(self,a=0,b=0):
  self.a=P(a);self.b=P(b)
 @staticmethod
 def cast(a):return a if isinstance(a,E) else E(a)
 def __add__(self,o):
  o=self.cast(o);return E(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return E(-self.a,-self.b)
 def __sub__(self,o):return self+-self.cast(o)
 def __rsub__(self,o):return self.cast(o)+-self
 def __mul__(self,o):
  o=self.cast(o);return E(self.a*o.a+self.b*o.b/2,self.a*o.b+self.b*o.a)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=self.cast(o)
  return self*o.inv()
 def __rtruediv__(self,o):return self.cast(o)*self.inv()
 def __pow__(self,n):
  z=E(1)
  for _ in range(n):z*=self
  return z
 def __bool__(self):return bool(self.a) or bool(self.b)
 def __eq__(self,o):
  o=self.cast(o);return self.a==o.a and self.b==o.b
 def __repr__(self):return f"({self.a})+t({self.b})"
 def degree(self):return max(self.a.degree(),self.b.degree())
 def coeff(self,n):return E(self.a[n],self.b[n])
 def lc(self):return self.coeff(self.degree())
 def inv(self):
  assert self.degree()==0
  a,b=self.a[0],self.b[0]
  d=a*a-b*b/2
  return E(a/d,-b/d)
 def monic(self):return self*self.lc().inv()
 def der(self):return E(self.a.derivative(),self.b.derivative())
 def div(self,o):
  d=o.degree();k=o.lc().inv()
  r=self
  q=zero
  while r and r.degree()>=d:
   n=r.degree()-d
   c=r.lc()*k
   v=c*E(P([0]*n+[1]))
   q+=v;r-=v*o
  return q,r
 def __mod__(self,o):
  if not o.b:return E(self.a%o.a,self.b%o.a)
  return self.div(o)[1]
 def exact(self,o):
  q,r=self.div(o);assert not r;return q
 def gcd(self,o):
  a,b=self,o
  while b:a,b=b,a%b
  return a.monic() if a else a
 def invmod(self,o):
  a,b=o,self%o
  c,d=zero,one
  while b:
   q,r=a.div(b)
   a,b=b,r
   c,d=d,(c-q*d)%o
  if a.degree()!=0:return None,a
  z=c*a.inv()%o
  assert self*z%o==E(1)
  return z,a
zero,one=E(),E(1)

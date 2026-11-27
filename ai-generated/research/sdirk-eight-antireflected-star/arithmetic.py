from flint import fmpq_poly, fmpq

class E:
 P=None
 def __init__(self,v=0):
  if isinstance(v,E):self.a=v.a
  elif isinstance(v,fmpq_poly):self.a=v%E.P
  elif isinstance(v,(list,tuple)):self.a=fmpq_poly(list(v))%E.P
  else:self.a=fmpq_poly([fmpq(str(v))])
 def __bool__(self):return bool(self.a)
 def __add__(self,v):return E(self.a+E(v).a)
 __radd__=__add__
 def __neg__(self):return E(-self.a)
 def __sub__(self,v):return self+(-E(v))
 def __rsub__(self,v):return E(v)+(-self)
 def __mul__(self,v):
  if isinstance(v,Q):return NotImplemented
  return E(self.a*E(v).a)
 __rmul__=__mul__
 def __truediv__(self,v):return self*E(v)**(-1)
 def __rtruediv__(self,v):return E(v)*self**(-1)
 def __eq__(self,v):return self.a==E(v).a
 def __pow__(self,n):
  if n<0:
   g,t,_=self.a.xgcd(E.P)
   if g.degree()!=0:raise ZeroDivisionError('not a unit')
   return E(t/g[0])**(-n)
  u=E(1);v=self
  while n:
   if n%2:u=u*v
   n//=2
   if n:v=v*v
  return u
 def __repr__(self):return str(self.a)

class Q:
 v=None #  formal quadratic T² = v
 def __init__(self,a=0,b=0):
  if isinstance(a,Q):self.a,self.b=a.a,a.b
  else:self.a,self.b=E(a),E(b)
 def __add__(self,o):
  o=Q(o);return Q(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return Q(-self.a,-self.b)
 def __sub__(self,o):return self+(-Q(o))
 def __rsub__(self,o):return Q(o)+(-self)
 def __mul__(self,o):
  o=Q(o);return Q(self.a*o.a+Q.v*self.b*o.b,self.b*o.a+self.a*o.b)
 __rmul__=__mul__
 def norm(self):return self.a**2-Q.v*self.b**2
 def __truediv__(self,o):
  o=Q(o);D=o.norm()
  return self*Q(o.a/D,-o.b/D)
 def __rtruediv__(self,o):return Q(o)/self
 def __bool__(self):return bool(self.a) or bool(self.b)
 def __eq__(self,o):
  o=Q(o);return self.a==o.a and self.b==o.b
 def __pow__(self,n):
  if n<0:return (1/self)**(-n)
  out=Q(1)
  for i in range(n):out=out*self
  return out

def solve(es, rhs, R=E):
 m=len(es)
 a=[list(map(R,r))+[R(y)] for r,y in zip(es,rhs)]
 for i in range(m):
  for j in range(i,m):
   try:
    z=1/a[j][i]
    break
   except ZeroDivisionError:pass
  else:return
  a[i],a[j]=a[j],a[i]
  a[i]=[x*z for x in a[i]]
  for j in range(m):
   if j!=i and a[j][i]:
    z=a[j][i];a[j]=[x-z*y for x,y in zip(a[j],a[i])]
 return [r[-1] for r in a]

def poly_eval(p,x,cast):
 t=cast(0)
 for a in p[::-1]:t=t*x+a
 return t

def divmod_coeff(p,q,R=E):
 def trim(v):
  while v and not v[-1]:v.pop()
  return v
 assert q
 o=[R(0) for _ in range(max(0,len(p)-len(q)+1))];p=p[:]
 t=1/q[-1]
 while p and len(p)>=len(q):
  j=len(p)-len(q);s=t*p[-1]
  o[j]=s
  for i,v in enumerate(q):p[j+i]=p[j+i]-s*v
  p.pop();trim(p)
 return trim(o),p

def poly_gcd(a,b):
 while b:a,b=b,divmod_coeff(a,b)[1]
 return [u/a[-1] for u in a]

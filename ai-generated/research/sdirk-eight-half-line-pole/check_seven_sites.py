"""Exact rational line-pole determinant, with t²=1/2 and variable xi."""
from itertools import product,permutations
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
 def __mod__(self,o):return self.div(o)[1]
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
zero,one,t,z=E(),E(1),E(0,1),E(P([0,1]))
g=one/2;g1=g*g/2
def det(M):
 n=len(M)
 return sum(((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))*prod(M[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def prod(xs):
 r=one
 for x in xs:r*=x
 return r
def cramer(M,b):
 n=len(M)
 return [det([[b[i] if j==k else M[i][j] for j in range(n)] for i in range(n)]) for k in range(n)]
def clean(p):
 p=list(p)
 while p and not p[-1]:p.pop()
 return p
def add(p,q):
 v=list(p if len(p)>=len(q) else q)
 for i,c in enumerate(q if len(p)>=len(q) else p):v[i]+=c
 return clean(v)
def scale(p,c):return clean([d*c for d in p])
def mul(p,q):
 out=[zero]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]+=a*b
 return clean(out)
def xmul(p,d=1):return [zero]*d+p if p else []
def ev(p,a):
 s=zero
 for e in reversed(p):s=s*a+e
 return s
def qr_monic(p,q):
 assert q[-1]==one
 p=clean(p); b=[zero]*max(0,len(p)-len(q)+1)
 while len(p)>=len(q):
  j=len(p)-len(q);h=p[-1];b[j]=h
  for i,k in enumerate(q):p[i+j]-=h*k
  p=clean(p)
 return clean(b),p
def xp(xs):
 r=[one]
 for x in xs:r=mul(r,[-x,one])
 return r

def endpoint(sign,star):
 u=one+2*sign*t;w=2-u if star else 2*u;r=zero if star else 3*u/2-1
 return g*(1+u),g*(1+w),g*g1*u,g*g1*(w-r)
legs=[[E(c) for c in v] for v in ((-1,12,-30,20),(1,-20,90,-140,70),(-1,30,-210,560,-630,252))]
q=[-z,one];q2=mul(q,q)
def strip(p,g):
 while p.degree()>0:
  d=p.gcd(g)
  if d.degree()==0:break
  p=p.exact(d)
 return p.monic()
def finite_gcd(a,b,mod):
   # Certified Euclid in X over Q(t)[xi]/mod, split a coefficient fiber
   # if a nonunit occurs rather than silently dividing it.
   aa=list(a);bb=list(b)
   a,b=clean([k%mod for k in a]),clean([k%mod for k in b])
   while b:
    iv,d=b[-1].invmod(mod)
    if iv is None:
     if not (0<d.degree()<mod.degree()):
      raise ArithmeticError((d.degree(),mod.degree()))
     return finite_gcd(aa,bb,d) and finite_gcd(aa,bb,mod.exact(d))
    while len(a)>=len(b):
     i=len(a)-len(b);c=(a[-1]*iv)%mod
     for j,k in enumerate(b):a[i+j]=(a[i+j]-c*k)%mod
     a=clean(a)
    a,b=b,a
   return len(a)==1 and a[0].invmod(mod)[0] is not None

def data(front,rear,sig):
 a,b,ha,hb=endpoint(1,front);c,d,k,l=endpoint(sig,rear);c,d=1-c,1-d
 Va,Vb,Vc,Vd=[[ev(p,s) for p in legs] for s in (a,b,c,d)]
 M=[Va,Vb,[l*(d-z)*v-k*(c-z)*w for v,w in zip(Vc,Vd)]]
 delta=det(M)
 pscale=cramer(M,[ha*(a-z),hb*(b-z),zero])
 p=[]
 for j,k0 in zip(pscale,legs):p=add(p,scale(k0,j))
 assert len(p)==6
 v=p[-1];S4,r=qr_monic(p,q);r=r[0];S3,ss=qr_monic(S4,q)
 ss=ss[0] if ss else zero
 U4,tt=qr_monic(xmul(S4),q)
 tt=tt[0] if tt else zero
 assert tt==z*ss
 def I(f):return sum(k/(j+1) for j,k in enumerate(f[:8]))
 A8=-I(xmul(p,3))
 B1=-I(S4)
 S2=mul(S4,S4)
 B2=-(v*I(S2)+v*v*A8+2*r*v*I(S3)+2*v*ss*B1)
 XS2=xmul(S2)
 A9=-(v*I(XS2)+XS2[8]*A8+2*r*v*I(U4)+2*v*tt*B1+v*r*B1+z*B2)
 W=v**3*r*r
 def moment(f):
  Q0,rr=qr_monic(f,q2)
  out=I(Q0)*W
  if len(Q0)>8:out+=Q0[8]*A8*v*v*r*r
  if len(Q0)>9:out+=Q0[9]*A9*r*r
  assert len(Q0)<=10
  # rem=f(xi)+f'(xi)(X-xi)
  U=ev(rr,z);V=rr[1] if len(rr)>1 else zero
  return out+U*B2*v*v+V*B1*v**3*r
 P4=xp((a,b,c,d))
 T=[moment(xmul(P4,j)) for j in range(8)]
 tap=[[one,one,one],[g,a,b],[g*g-(2*one/3)*g1,a*a,b*b]]
 tapd=det(tap)
 h=[cramer(tap,o)[0]*(g1/tapd) for o in ([-g,zero,zero],[one,-g,zero],
                    [zero,one/2,-g],[zero,zero,one/3])]
 F=add(scale(mul(q,h),delta),scale(p,-one))
 guards=delta*v*r*prod(z-x for x in (a,b,c,d))
 return F,T,guards,c,d,(a,b,ha,hb,p,delta,tap,tapd)

def main():
 import sys
 for front,rear,sig in product((True,False),(True,False),(1,-1)):
  if rear and sig==-1:continue
  if len(sys.argv)>1 and int(sys.argv[1])!=int(front):continue
  print("phase",front,rear,sig,flush=True)
  F,T,G,c,d,_=data(front,rear,sig)
  H4=det([[T[i+j] for j in range(4)] for i in range(4)])
  if not H4:
   print("H4 identically zero",flush=True);continue
  H3=[[T[i+j] for j in range(3)] for i in range(3)];H3d=det(H3)
  S=strip(H4,G*H3d)
  S=S.exact(S.gcd(S.der())).monic()
  assert S.degree()==3
  print("raw H4",H4.degree(),"ungated squarefree",S.degree(),flush=True)
  for a in (c,d):
   g=S.gcd(ev(F,a))
   assert g.degree()==0
  Qc=cramer(H3,[-T[3+i] for i in range(3)])+[H3d]
  assert finite_gcd(F,Qc,S)
  print("  seven-site branch excluded",flush=True)
if __name__=='__main__':main()

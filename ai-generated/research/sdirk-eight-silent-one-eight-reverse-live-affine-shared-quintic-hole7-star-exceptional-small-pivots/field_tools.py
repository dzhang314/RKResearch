"""Small field and signed polynomial arithmetic for the complete local checks."""
from functools import reduce

def hor(a,x):
 z=x*0
 for b in reversed(a):z=z*x+b
 return z

def mul(a,b):
 if not a or not b:return []
 z=[a[0]*0]*(len(a)+len(b)-1)
 for i,c in enumerate(a):
  for j,d in enumerate(b):z[i+j]+=c*d
 return tr(z)

def add(a,b):
 if not a:return b[:]
 if not b:return a[:]
 z=[a[0]*0]*max(len(a),len(b))
 for i,c in enumerate(a):z[i]+=c
 for i,c in enumerate(b):z[i]+=c
 return tr(z)

def sc(a,b):return tr([t*b for t in a])
def tr(a):
 while a and a[-1]==0:a.pop()
 return a

def mod_monic(a,m):
 a=a[:]
 assert m[-1]==1
 while len(a)>=len(m):
  q=a[-1];i=len(a)-len(m)
  for j,b in enumerate(m):a[i+j]-=q*b
  tr(a)
 return a

def gcd(a,b):
 if not a:return mon(b)
 if not b:return mon(a)
 while b:
  b=mon(b)
  a,b=b,mod_monic(a,b)
 return a

def mon(a):return sc(a,a[-1].inverse()) if a else []

class Ext:
 def __init__(self,K,P,f):
  self.K,self.P,self.f=K,P,f
 def __call__(self,v):
  if isinstance(v,Elt):
   if v.E is self:return v
   raise TypeError("different extensions")
  return Elt(self,self.P(v))
 def gen(self):return Elt(self,self.P.gen())

class Elt:
 def __init__(self,E,p):self.E,self.p=E,p%E.f
 def __add__(self,x):return Elt(self.E,self.p+self.E(x).p)
 __radd__=__add__
 def __neg__(self):return Elt(self.E,-self.p)
 def __sub__(self,x):return self+-self.E(x)
 def __rsub__(self,x):return self.E(x)+-self
 def __mul__(self,x):return Elt(self.E,self.p*self.E(x).p)
 __rmul__=__mul__
 def __eq__(self,x):return self.p==self.E(x).p
 def inverse(self):
  d,p,q=self.p.xgcd(self.E.f)
  assert d.degree()==0
  return Elt(self.E,p/d[0])
 def __truediv__(self,x):return self*self.E(x).inverse()
 def __rtruediv__(self,x):return self.E(x)*self.inverse()
 def __pow__(self,n):
  z=self.E(1);a=self
  while n:
   if n%2:z*=a
   a*=a;n//=2
  return z
 def __repr__(self):return str(self.p)


def summ(xs):
 return reduce(add,xs,[])

def evp(H,p):
 out=[]
 for a in reversed(H):out=add(mul(out,p),[a])
 return out

def nested(a,b):
 if not a or not b:return []
 z=[[] for _ in range(len(a)+len(b)-1)]
 for i,p in enumerate(a):
  for j,q in enumerate(b):
   z[i+j]=add(z[i+j],mul(p,q))
 while z and not z[-1]:z.pop()
 return z

def nodal(x,A):
 return [sc(x,-1),[A(1)]]
def nread(Q,x):return summ(sc(t,x**j) for j,t in enumerate(Q))
def compose(Q,x):return summ(mul(t,power(x,j)) for j,t in enumerate(Q))
def power(x,k):
 q=[x[0].E(1)]
 for _ in range(k):q=mul(q,x)
 return q
def div(a,b):
 b=tr(b[:]); aa=tr(a[:]); s=b[-1].inverse()
 c=[b[-1]*0 for _ in range(len(aa)-len(b)+1)]
 while aa and len(aa)>=len(b):
  n=len(aa)-len(b);v=aa[-1]*s;c[n]=v
  for i,h in enumerate(b):aa[i+n]-=v*h
  tr(aa)
 assert not aa
 return c

def integ(P,i):return sum(v/(i+j+1) for j,v in enumerate(P))

def tail_cuts(A,g,r,s,y,w,H,mode):
 E2=[2*g*g,-4*g,A(1)]
 N=mul(mul(mul(E2,[-g*s,A(1)]),[-g*y,A(1)]),[-w,A(1)])
 Q=[[a] for a in N]
 x=1-g
 U=[A(0),A(1)]
 Hx=[hor(H,x)]
 if mode=='star':
  c,d=[x-g,-g],[x-g,g];k=[A(2),A(0),A(-1)];pad=[A(0),A(1),A(0),A(-1)]
  F=summ((mul([A(1),A(-1)],evp(H,c)),sc(mul([A(1),A(1)],evp(H,d)),-1),sc(mul(mul(U,k),Hx),2)))
  deg=2;lead=2*g**4
 elif mode=='arith':
  c,d=[x,-g],[x,-2*g];k=[A(1),A(2),A(-1)];pad=[A(0),A(0),A(1)]
  jr,hr=map(lambda q:list(map(A,q)),([2,3,-12,4],[-2,1,4,-1]))
  F=summ((mul(hr,evp(H,d)),sc(mul(jr,evp(H,c)),2),sc(mul(mul(jr,k),Hx),-1)))
  deg=5;lead=-8*g**4
 else:
  c=[x,-g];k=[A(1),A(2),A(-1)];pad=U
  w0=list(map(A,[-2,1]))
  d=add([x],sc(mul(k,w0),g/2))
  F=add(mul(w0,evp(H,c)),sc(mul(add(sc(U,2),mul(k,w0)),Hx),-1))
  deg=4;lead=g**4
 F=div(F,pad)
 assert len(F)==deg+1 and F[-1]==lead
 tem=nested(Q,nodal(d,A))
 D=nested(nested(Q,nodal(c,A)),nodal([x],A))
 if mode!='silent8':D=nested(D,nodal(d,A))
 hr,beta=hor(H,r),integ(H,0)
 def J(P,i):
  j0=summ(sc(a,hr/(i+j+1)) for j,a in enumerate(P))
  return add(j0,sc(nread(P,r),-beta*r**i))
 Hp=[[a] for a in H]
 h4,h5=J(Hp,4),J(Hp,5)
 d0,d1=J(D,0),J(D,1)
 if mode=='silent8':
  B=[d0,add(mul(D[-1],h4),sc(d1,-1)),
     summ((mul(D[-2],h4),mul(D[-1],h5),sc(d1,-H[-2]),sc(J(D,2),-1)))]
 else:
  B=[add(mul(D[-1],h4),sc(d0,-1)),
     summ((mul(D[-2],h4),mul(D[-1],h5),sc(d0,-H[-2]),sc(d1,-1)))]
 term=add(mul(k,compose(tem,c)),nread(tem,x))
 return F,B,term

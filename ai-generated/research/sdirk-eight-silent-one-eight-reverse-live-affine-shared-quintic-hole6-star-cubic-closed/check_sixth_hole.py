"""Complete degree-protected residue test for all actual silent placements."""
from early_projection import model,row
from flint import fmpz_mod_poly_ctx,fq_default_ctx,fq_default_poly_ctx,nmod_poly
from itertools import combinations
from collections import Counter

P=1009


def reduction(v):
    return int(v.p)*pow(int(v.q),-1,P)%P


def evalf(v,g,K):
    z=K(0)
    for j in range(v.degree(),-1,-1):
        z=z*g+reduction(v[j])
    return z


def convert(v,g,K,U):
    tab=v.to_dict()
    return U([evalf(row(tab,j),g,K) for j in range(v.degrees()[0]+1)])


def components(m):
    mm=nmod_poly([reduction(m[j]) for j in range(m.degree()+1)],P)
    assert mm.degree()==66 and mm.leading_coefficient()==1
    fac=mm.factor()[1]
    assert sorted((q.degree(),i) for q,i in fac)==[(2,1),(5,1),(15,1),(21,1),(23,1)]
    prod=nmod_poly([1],P)
    for q,i in fac:
        prod*=q**i
    assert prod==mm
    for q,i in fac:
        K=fq_default_ctx(modulus=fmpz_mod_poly_ctx(P)([int(b) for b in q.coeffs()]),var="g")
        yield K,K.gen(),q


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

class Quad:
 def __init__(self,E,ee,pp):self.E,self.e,self.p=E,ee,pp
 def __call__(self,x):
  if isinstance(x,Pair):
   assert x.Q is self
   return x
  return Pair(self,self.E(x),self.E(0))
 def gen(self):return Pair(self,self.E(0),self.E(1))

class Pair:
 def __init__(self,Q,a,b):self.Q,self.a,self.b=Q,a,b
 def __add__(self,x):
  x=self.Q(x);return Pair(self.Q,self.a+x.a,self.b+x.b)
 __radd__=__add__
 def __neg__(self):return Pair(self.Q,-self.a,-self.b)
 def __sub__(self,x):return self+-self.Q(x)
 def __rsub__(self,x):return self.Q(x)+-self
 def __mul__(self,x):
  x=self.Q(x);k=self.b*x.b
  return Pair(self.Q,self.a*x.a-self.Q.p*k,self.a*x.b+self.b*x.a+self.Q.e*k)
 __rmul__=__mul__
 def __eq__(self,x):
  x=self.Q(x);return self.a==x.a and self.b==x.b
 def __pow__(self,n):
  z=self.Q(1);a=self
  while n:
   if n%2:z*=a
   a*=a;n//=2
  return z

def gate(y,Q=None):
 if Q is None:return any(x!=0 for x in y)
 j=[Q.p,-Q.e,Q.E(1)]
 for x in y:
  z=Q(x)
  j=gcd(j,tr([z.a,z.b]))
  if len(j)==1:return True
 return False

def remainders(H,r,D,A):
 R=mod_monic(mul([-r,A(1)],list(map(A,[1,-20,90,-140,70]))),H)
 T=mod_monic(D,H)
 R+=[A(0)]*(4-len(R));T+=[A(0)]*(4-len(T))
 return [R[i]*T[j]-R[j]*T[i] for i,j in combinations(range(4),2)]

def missing(E0,H,r,c,x,A):
 E=E0[:]
 for k in (c,x):E=mul(E,[-k,A(1)])
 ac=hor(H,c)*(c-x)*hor(E0,c);ax=hor(H,x)*(x-c)*hor(E0,x)
 dn=mul(E,[ax*x-ac*c,ac-ax])
 return remainders(H,r,dn,A)

def test():
 # The two roots of 2t²=1. Both early-clock orientations are represented.
 ts=[t for t in range(P) if (2*t*t-1)%P==0]
 assert len(ts)==2
 F,E,B,M,guard,raw_h4,raw_e4=model()
 done=Counter()
 for K,g,fac in components(M):
  W=fq_default_poly_ctx(K)
  cv0=lambda v:convert(v,g,K,W)
  bs=list(map(cv0,B))
  assert all(q.degree()==6 for q in bs)
  br=bs[0].gcd(bs[1]).gcd(bs[2]);assert br.degree()==1
  r=-br[0]/br[1]
  read=lambda v:cv0(v)(r)
  d0,d1,d2v,R4,LR=map(read,guard)
  assert g!=0 and d2v!=0 and R4!=0 and LR!=0
  e=(-d1/d2v)*g; pp=(d0+9*g**4*LR/R4)*g*g/d2v
  HH=[read(z) for z in raw_h4]+[K(0)]
  EE=[read(z) for z in raw_e4]
  ef,ff=read(E[0]),read(F[0]);assert ef!=0 and ff!=0
  Hh=[ef*a-ff*b for a,b in zip(HH,EE)];assert Hh[-1]!=0
  Hh=[a/Hh[-1] for a in Hh]
  assert hor(Hh,r)!=0
  a,b=sorted([(2+2*t)%P for t in ts]);ad,bd=g*a,g*b
  X0=1-g;U=W.gen()
  for rear in ("star","arith","silent8"):
   if rear=="star":
    k=2-U**2;c=X0-g*(1+U);d=X0-g*(1-U)
    FN=(1-U)*hor(Hh,c)-(1+U)*hor(Hh,d)+2*U*k*hor(Hh,X0)
    gappad=U*(1-U**2);degree=2;top=2*g**4
   elif rear=="arith":
    k=1+2*U-U**2;c=X0-g*U;d=X0-2*g*U
    j=2+3*U-12*U**2+4*U**3
    q=-2+U+4*U**2-U**3
    FN=q*hor(Hh,d)+2*j*hor(Hh,c)-k*j*hor(Hh,X0)
    gappad=U**2;degree=5;top=-8*g**4
   else:
    k=1+2*U-U**2;c=X0-g*U;d=X0+g*k*(U-2)/2
    FN=(U-2)*hor(Hh,c)-(2*U+k*(U-2))*hor(Hh,X0)
    gappad=U;degree=4;top=g**4
   eq,rem=divmod(FN,gappad)
   assert rem.is_zero() and eq.degree()==degree and eq.leading_coefficient()==top,(rear,rem,eq.degree(),eq.leading_coefficient()/top)
   phis=eq.factor()[1]
   assert sum(q.degree()*v for q,v in phis)==degree
   for qr,em in phis:
    A=Ext(K,W,qr)
    # All entries are ambient polynomial values, so the canonical u is valid
    # even when its irreducible factor has degree > 1.
    c1,d1,k1=[A(v) for v in (c,d,k)]
    rr,xx,AA,BB,e1,pp1=map(A,(r,X0,ad,bd,e,pp))
    H=list(map(A,Hh))
    early2=mul([-AA,A(1)],[-BB,A(1)]);early4=mul(early2,[pp1,-e1,A(1)])
    def pen(z,J):
     return (J(xx)-z)*hor(list(map(J,H)),J(c1))-J(k1)*(J(c1)-z)*hor(list(map(J,H)),J(xx))
    if rear=="silent8":
     gates=missing(early4,H,rr,c1,xx,A)
     assert gate(gates),(fac.degree(),rear,8,qr.degree())
     done[rear,8]+=1
     continue
    for slot,z,other in ((2,AA,BB),(3,BB,AA)):
     early3=mul([-other,A(1)],[pp1,-e1,A(1)])
     gates=[pen(z,A)]+missing(mul(early3,[-d1,A(1)]),H,rr,c1,xx,A)
     assert gate(gates),(fac.degree(),rear,slot,qr.degree())
     done[rear,slot]+=1
    Q=Quad(A,e1,pp1);z=Q.gen()
    early3=mul(list(map(Q,early2)),[z-Q(e1),Q(1)])
    gates=[pen(z,Q)]+missing(mul(early3,[-Q(d1),Q(1)]),list(map(Q,H)),Q(rr),Q(c1),Q(xx),Q)
    assert gate(gates,Q),(fac.degree(),rear,45,qr.degree())
    done[rear,45]+=1
    E0=mul(early4,[-d1,A(1)])
    D7=mul(E0,mul([-c1,A(1)],[-xx,A(1)]))
    ac=hor(H,c1)*(c1-xx)*hor(E0,c1);ax=hor(H,xx)*(xx-c1)*hor(E0,xx)
    gates=[ac-ax]+remainders(H,rr,D7,A)
    assert gate(gates),(fac.degree(),rear,7,qr.degree())
    done[rear,7]+=1
 assert done==Counter({("silent8",8):14, **{("star",j):7 for j in (2,3,45,7)},
                       **{("arith",j):10 for j in (2,3,45,7)}})
 print("p=1009; full gamma r fibers and all actual silent placements:",dict(done),flush=True)


if __name__=="__main__":
 test()

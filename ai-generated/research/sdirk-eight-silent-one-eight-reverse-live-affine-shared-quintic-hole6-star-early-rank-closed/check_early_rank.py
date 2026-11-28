"""Complete early-anchor rank loss, regular exceptional star actual hole six."""
from flint import (fmpq, fmpq_mpoly_ctx, fmpz_mod_poly_ctx, fq_default_ctx,
                   fq_default_poly_ctx, nmod_poly)
from sympy import symbols, Poly, QQ, sqrt
from itertools import combinations
from functools import reduce

C=fmpq_mpoly_ctx.get(("r","s","gamma"),ordering="lex")
r,s,g=C.gens()


def mul(a,b):
    z=[C.constant(0)]*(len(a)+len(b)-1)
    for i,a0 in enumerate(a):
        for j,b0 in enumerate(b):
            z[i+j]+=a0*b0
    return z


def model():
    d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
    d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
    d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
    D=d2*s*s+d1*s+d0
    y=(3*s-1)/2
    U=(1-2*d0)*fmpq(4,3)+8*(d2-70*g**4)*y+fmpq(4,3)*D*(5-s)
    V=d2*(y+s)+d1
    E3=mul([2*g*g,-4*g,C.constant(1)],[-s*g,C.constant(1)])
    F=[U*a+8*V*b for a,b in zip([6*g**3,-18*g*g,9*g,C.constant(-1)],E3)]
    E=mul(E3,[-y*g,C.constant(1)])

    def moment(q,j):
        return sum(c/(i+j+1) for i,c in enumerate(q))

    def row(q):
        return [moment(q,j+1)-r*moment(q,j) for j in range(3)]

    f,e=row(F),row(E)
    B=[f[i]*e[j]-f[j]*e[i] for i,j in combinations(range(3),2)]
    L=70*r**4-140*r**3+90*r*r-20*r+1
    G=r**4-16*g*r**3+72*g*g*r*r-96*g**3*r+24*g**4
    M=(r**4/4-g*r**3-(s+4)*(g*r**3/3-g*g*r*r)
       +(4*s+2)*(g*g*r*r/2-g**3*r)-2*s*(g**3*r-g**4))
    T=(9*U-8*V)*g**4*L+D*(U*G-32*V*M)
    return B,T


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

X,R,G=symbols('X r gamma')
t=sqrt(2)
L=[1,2*X-1,6*X**2-6*X+1,20*X**3-30*X**2+12*X-1,
   70*X**4-140*X**3+90*X**2-20*X+1]
a,b=2+t,2-t
ha,hb=(a-1)/2,(b-1)/2
J=QQ.algebraic_field(t)
def ell1(P):
    a0=P.subs(X,G*a)/ha
    b0=P.subs(X,G*b)/hb
    # both sign orientations give this rational slope.
    q=Poly((b0-a0)/(b-a),R,G,domain=J)
    assert all(len(v.to_list())==1 for v in q.rep.to_dict().values())
    return Poly(q.as_expr(),R,G,domain=QQ)
def rank():
    K=sum((2*j+1)*L[j]*Poly(L[j],X).eval(R) for j in range(4))
    S=ell1(L[4])
    Q=ell1(K)
    assert S==Poly(2*(1400*G**4-840*G**3+180*G**2-20*G+1),R,G,domain=QQ)
    return S,Q

def hor(P,g,K,p):
    z=K(0)
    for c in P.all_coeffs():
        n,d=c.as_numer_denom()
        z=z*g+(int(n)*pow(int(d),-1,p)%p)
    return z

def modrank():
    p=1009
    l,q=rank()
    root=Poly(l.as_expr(),G,domain=QQ).monic()
    u=nmod_poly([int(c.p)*pow(int(c.q),-1,p)%p for c in reversed(root.all_coeffs())],p)
    assert u.degree()==4 and u.leading_coefficient()==1
    ff=u.factor()[1]
    assert len(ff)==1 and ff[0]==(u,1)
    for f,e in ff:
        K=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)([int(a) for a in f.coeffs()]),var='g')
        W=fq_default_poly_ctx(K);g=K.gen()
        pol=W([hor(Poly(Poly(q.as_expr(),R).nth(j),G,domain=QQ),g,K,p) for j in range(4)])
        assert q.degree(R)==pol.degree()==3
        fac=pol.factor()[1]
        assert len(fac)==1 and fac[0][0].degree()==3 and fac[0][1]==1
        v,_=fac[0]
        assert v*pol.leading_coefficient()==pol
        yield g,K,W,v,p

def coefficient(q,K,g,A,r,p):
    z=[A(0)]*(q.degrees()[1]+1)
    for (i,j,k),h in q.to_dict().items():
        z[j]+=A((int(h.p)*pow(int(h.q),-1,p)%p)*g**k)*r**i
    return tr(z)

def test():
    B,T=model()
    for g,K,W,H,pp in modrank():
        p=pp
        A=Ext(K,W,H);r=A.gen()
        vals=[coefficient(q,K,g,A,r,p) for q in [*B,T]]
        assert [len(z)-1 for z in vals]==[5,5,5,5]
        assert reduce(gcd,vals)==[A(1)]
    print("1009: complete gamma degree 4 and r degree 3; four full s degree-five gates have gcd 1")


if __name__=="__main__":
    test()

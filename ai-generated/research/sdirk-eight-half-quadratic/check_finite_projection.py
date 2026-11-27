"""Try a good-reduction certificate for the six-literal-site squared Hankel cut."""
from literal_front import *
from flint import nmod_poly
from itertools import product
from math import isqrt

p=1009
t0=285
assert all(p%m for m in range(2,isqrt(p)+1)) and (2*t0*t0-1)%p==0

def rat(x):
    a,b=x.numerator,x.denominator
    return int(a)%p*pow(int(b),-1,p)%p
def kmod(x):
    x=K.convert(x)
    s=0
    for u in x.to_list():s=(s*t0+rat(u))%p
    return s
class MField:
    def __init__(self,Q):
        self.Q=Q*pow(int(Q.leading_coefficient()),-1,p)
        assert self.Q.degree()==2
    def __call__(self,x):
        if isinstance(x,ME):
            assert x.f is self
            return x
        return ME((x if isinstance(x,nmod_poly) else nmod_poly([x],p))%self.Q,self)
class ME:
    def __init__(self,x,f):self.x,self.f=x,f
    def __bool__(self):return bool(self.x)
    def __eq__(self,x):return self.x==self.f(x).x
    def __add__(self,x):return self.f(self.x+self.f(x).x)
    __radd__=__add__
    def __neg__(self):return self.f(-self.x)
    def __sub__(self,x):return self+-self.f(x)
    def __rsub__(self,x):return self.f(x)+-self
    def __mul__(self,x):return self.f(self.x*self.f(x).x)
    __rmul__=__mul__
    def __truediv__(self,x):return self*pow(x%p,-1,p)
    def __repr__(self):return str(self.x)

def clean(P):
    while P and not P[-1]:P.pop()
    return P
def mul(P,Q):
    if not P or not Q:return []
    S=[0]*(len(P)+len(Q)-1)
    for i,a in enumerate(P):
        for j,b in enumerate(Q):S[i+j]+=a*b
    return clean(S)
def monicqr(f,q):
    assert q[-1]==1
    f=clean(list(f));b=[0]*max(0,len(f)-len(q)+1)
    while f and len(f)>=len(q):
        d=len(f)-len(q);v=f[-1];b[d]=v
        for j,c in enumerate(q):f[d+j]-=v*c
        f=clean(f)
    return clean(b),f
def eval_(L,x):
    a=0
    for u in L[::-1]:a=a*x+u
    return a
legs=[[-1,12,-30,20],[1,-20,90,-140,70],[-1,30,-210,560,-630,252]]
def V(x):return [eval_(v,x)%p for v in legs]

def eval_R(poly,S0,Y0):
    return sum(kmod(c)*pow(S0,i,p)*pow(Y0,j,p) for (i,j,k),c in poly.items() if k==0)%p
def sgcd(P,Q):return P.gcd(Q).degree()

def pencil(front, rear, sign, data, s0, y0):
    a,b,ha,hb,hs,d,W,A,B,C,D,M=data
    rm=end(sign,rear)
    c,d,k,l=map(kmod,[1-rm[0],1-rm[1],rm[2],rm[3]])
    a,b,ha,hb=map(kmod,(a,b,ha,hb))
    W0=eval_R(B,s0,y0)
    if not W0:return None
    hy=-eval_R(A,s0,y0)*pow(W0,-1,p)%p
    if (eval_R(C,s0,y0)+eval_R(D,s0,y0)*hy)%p:return None
    xs=[a,b,s0,y0,c,d]
    if len(set(xs))<6:return None
    M=[V(x) for x in (a,b,s0)]
    dm=det(M)%p
    if not dm:return None
    hs=eval_R(hs,s0,0)
    P=[cramer(M,[h*pow(x,i,p)%p for h,x in zip((ha,hb,hs),(a,b,s0))]) for i in range(3)]
    PS=[[sum(co[j]*(legs[j][i] if i<len(legs[j]) else 0)
          for j in range(3))*pow(dm,-1,p)%p for i in range(6)] for co in P]
    tc=[(eval_(u,y0)-hy*pow(y0,i,p))%p for i,u in enumerate(PS)]
    if not tc[1]:return None
    alpha=nmod_poly([-tc[2]*pow(tc[1],-1,p)%p,-tc[0]*pow(tc[1],-1,p)%p],p)
    beta=nmod_poly([0,1],p)
    qq=[beta,alpha,nmod_poly([1],p)]
    pp=[beta*PS[0][i]+alpha*PS[1][i]+PS[2][i] for i in range(6)]
    Qr=l*eval_(qq,d)*eval_(pp,c)-k*eval_(qq,c)*eval_(pp,d)
    if Qr.degree()!=2:return None
    F=MField(Qr)
    q=[F(x) for x in qq];u=[F(x) for x in pp]
    Q2=mul(q,q)
    fxs=[mul(q,u),[0]+mul(q,u),mul(u,u),[0]+mul(u,u)]
    QR=[monicqr(r,Q2) for r in fxs]
    N=[[rest[j] if j<len(rest) else F(0) for j in range(4)] for quo,rest in QR]
    def I(U):
        assert len(U)<=8
        return sum(F(x)/(j+1) for j,x in enumerate(U))
    rho=F(det(N));omega=cramer(N,[-I(quo) for quo,rem in QR])
    def T(U):
        quo,rem=monicqr(U,Q2)
        return F(rho*I(quo)+sum(rem[j]*omega[j] for j in range(len(rem))))
    P6=[F(1)]
    for x in xs:P6=mul(P6,[F(-x),F(1)])
    T0=[T([F(0)]*j+P6) for j in range(6)]
    J=[[T0[i+j] for j in range(3)] for i in range(3)]
    G=F(det(J))
    Dall=F(1)
    for x in xs:Dall*=eval_(q,x)
    dq=F(Dall*rho)
    return F.Q,G.x,dq.x,rho.x

def replay():
    for front,rear,sig in product((True,False),(True,False),(1,-1)):
        if rear and sig==-1:
            continue
        data=front_data(front)
        a,b,ha,hb,hs,d,W,A,B,C,D,M=data
        U=W.exquo(d.exquo((s-a)*(s-b)))
        s0=1 if front else 3
        sample=nmod_poly([sum(kmod(v)*pow(s0,i,p)
                             for (i,j,k),v in U.items() if j==j0 and not k)%p
                          for j0 in range(3)],p)
        assert U.degree(Y)==sample.degree()==2
        roots=sample.roots()
        assert len(roots)==2 and all(m==1 for _,m in roots)
        assert sorted(int(y) for y,_ in roots)==([575,758] if front else [89,343])
        for y,m in roots:
            receipt=pencil(front,rear,sig,data,s0,int(y))
            assert receipt is not None
            R,G,D,rho=receipt
            assert R.degree()==2 and int(R.leading_coefficient())==1
            assert sgcd(R,G)==sgcd(R,D)==sgcd(R,rho)==0
        print(front,rear,sig,"s = ",s0,"two rank-two fibers with Hankel unit")

if __name__=='__main__':
    replay()

"""Pair equations for disjoint D labels, using exact FLINT polynomial fractions."""
from math import lcm
from flint import fmpq_mpoly_ctx,fmpz_mpoly_ctx
from collections import defaultdict
from itertools import combinations
Cq=fmpq_mpoly_ctx.get(('H','d'),'lex')
CZ=fmpz_mpoly_ctx.get(('H','d'),'lex')
one=Cq.constant(1)
zero=Cq.constant(0)
class F:
    def __init__(self,n=0,d=1):
        if isinstance(n,F):
            assert d==1
            self.n,self.d=n.n,n.d;return
        try:n=Cq.constant(n)
        except TypeError:pass
        try:d=Cq.constant(d)
        except TypeError:pass
        assert d
        if not n:self.n,self.d=zero,one;return
        if not d.is_constant():
            g=n.gcd(d)
            if not g.is_constant():n=n/g;d=d/g
        a=d.leading_coefficient()
        self.n,self.d=n/a,d/a
    @staticmethod
    def make(n,d):
        """Use only when numerator and denominator are known coprime."""
        out=F.__new__(F)
        if not n:
            out.n,out.d=zero,one
            return out
        a=d.leading_coefficient()
        out.n,out.d=n/a,d/a
        return out
    def __add__(self,b):
        b=F(b)
        if not self:return b
        if not b:return self
        if self.d==b.d:
            n=self.n+b.n
            if not n:return F()
            g=n.gcd(self.d)
            return F.make(n/g,self.d/g)
        g=self.d.gcd(b.d)
        u,v=self.d/g,b.d/g
        n=self.n*v+b.n*u
        if not n:return F()
        if g.is_constant():return F.make(n,u*v)
        q=n.gcd(g)
        return F.make(n/q,(g/q)*u*v)
    __radd__=__add__
    def __neg__(self):return F(-self.n,self.d)
    def __sub__(self,b):return self+-F(b)
    def __rsub__(self,b):return F(b)+-self
    def __mul__(self,b):
        b=F(b)
        if not self or not b:return F()
        a,c=self.n,self.d
        w,x=b.n,b.d
        if not (a.is_constant() or x.is_constant()):
            g=a.gcd(x);a=a/g;x=x/g
        if not (w.is_constant() or c.is_constant()):
            g=w.gcd(c);w=w/g;c=c/g
        return F.make(a*w,c*x)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=F(b);assert b.n;return self*F.make(b.d,b.n)
    def __rtruediv__(self,b):return F(b)/self
    def __pow__(self,k):
        assert int(k)==k and k>=0
        return F.make(self.n**k,self.d**k)
    def __bool__(self):return bool(self.n)
H,a=map(F,Cq.gens())

def ip(p):
    vals=p.to_dict()
    M=lcm(*(int(c.denominator) for c in vals.values()))
    return CZ.from_dict({ix:int(M*c) for ix,c in vals.items()})
def strip(p,guards):
    for g in guards:
        while p and (q:=p.gcd(g)).total_degree()>0:
            p,r=divmod(p,q);assert not r
    return p
def ev(a,v):
    out=F()
    for g in reversed(a):out=out*v+g
    return out
def div_linear(a,r):
    b=a[1:]
    for i in range(len(b)-2,-1,-1):b[i]=b[i]+r*b[i+1]
    assert not (a[0]+r*b[0])
    return b

CASES=('SS','A3S','A3A3')
def D(x):return -2+x+4*x*x-x**3
def k(x):return 1+2*x-x*x
def N(x):return (1+4*x-4*x*x)*D(x)+4*x*x*(3*x-2)
def paid(ph,z):
    if ph=='S':return 2-z,k(z)/2,[z,z-1,z-2,k(z)]
    return 2*z,N(z)/(2*D(z)),[z,z-2,k(z),D(z),N(z),3*z-2]
def mob(H,a):
    P=2*H**4-4*H**3-72*H*H+104*H-128
    Q=-5*H**4+20*H**3+60*H*H+120*H-40
    return ((2-a)*Q-P)/(P*a+Q),P*a+Q,Q*Q-P*(P-2*Q)
def frame(mode,hidden=False):
    fwd='S' if mode.startswith('S') else 'A3';rev=mode[len(fwd):]
    b,Mob,P8=mob(H,a)
    h=H/2;m=1+h;Z=F();one=F(1)
    masks={'mobius':[H,H-2,m,Mob,P8]}
    initial=sum(masks.values(),[])
    names=[ip(x.n) for x in initial]
    assert all(initial) and all(x.d.is_constant() for x in initial)
    def add(name,gs):
        assert all(gs)
        assert all(strip(ip(x.d),names).total_degree()==0 for x in gs)
        masks[name]=gs
        names.extend([ip(x.n) for x in gs])
    p,fp,d0=paid(fwd,a)
    v,rq,d1=paid(rev,b)
    s=a;t=H-b;q=H-v
    fs,rt=k(a)/2,k(b)/2
    add('front',d0);add('rear',d1)
    add('clocks',[a-b]+[x-y for x,y in combinations((Z,H,p,q,s,t),2)])
    n=(a-2)*H*(H-b)-2*H+a+b
    M=(b-2)*H*(H-a)-2*H+a+b
    add('scale',[n,M])
    lam=n/M
    r2=((a-2)*(b-2)*H-a-b+4)/(2*M)
    r1=(lam-1)/(2*H)-H*r2
    R=lambda y:one/2+r1*y+r2*y*y
    assert not (R(s)-fs) and not (R(t)-lam*rt)
    add('curvature',[r2])
    L3=lambda y:(y-h)**3-3*m*m*(y-h)/5
    L4=lambda y:(y-h)**4-6*m*m*(y-h)**2/7+3*m**4/35
    L=[L4(Z),-4*h**3+12*m*m*h/7,6*h*h-6*m*m/7,-4*h,one]
    V=[L3(Z),3*h*h-3*m*m/5,-3*h,one,Z]
    Lp,Lq=L4(p),L4(q)
    add('anchors',[Lp,Lq])
    S=Lp*L3(q)-Lq*L3(p)
    off=(q-p)*Lq*L3(p)-S*p
    scale=(q-p)*Lp*Lq
    Q=[scale*V[i]-off*L[i]-(S*L[i-1] if i else Z) for i in range(5)]+[-S]
    m0,m1,m2,m3=div_linear(div_linear(Q,p),q)
    l1=2*m1-4*m0*r1
    add('graph',[m0,m3,l1])
    E=m2-2*m0*r2-l1*r1
    G=m3-l1*r2
    L0=L4(Z)
    lin=lambda y:(H-y)*2*lam*L0/H+y*2*L0/H
    K2=(lam*L4(s)/fs-lin(s))/(s*(s-H))
    K=lambda y:lin(y)+K2*y*(y-H)
    assert not (K(t)-L4(t)/rt)
    u0=fp*(fp-R(p));u1=rq*(lam*rq-R(q))
    add('off_graph',[u0,u1])
    Y=(lam*Lp-fp*K(p))*u1-(Lq-rq*K(q))*u0
    if hidden:
        zz=-2*m0/l1
        add('hidden',[zz,zz-H,zz-p,zz-q,zz-s,zz-t,L4(zz)])
    assert all(strip(ip(z.d),names).total_degree()==0 for z in [E,G,Y])
    bits=[strip(ip(x.n),names) for x in (E,G,Y)]
    guards={k:[ip(x.n) for x in v] for k,v in masks.items()}
    return bits,guards
def project(mode,elim='d',method=None):
    eq,gs=frame(mode)
    E,G,Y=eq
    print(mode,'rows',[r.degrees() for r in eq],flush=True)
    assert all(eq)
    Hguards=[a for a in sum(gs.values(),[]) if not a.degrees()[0 if elim=='H' else 1]]
    if method is None:method=lambda a,b:a.resultant(b,elim)
    PP=[strip(method(E,x),Hguards) for x in [G,Y]]
    assert all(PP)
    G=PP[0].gcd(PP[1]);assert G
    fs=G.factor()[1]
    print(mode,'projections',[x.total_degree() for x in PP],
      'factors',[(x.total_degree(),n) for x,n in fs],flush=True)
    return fs,eq,gs,[x.total_degree() for x in PP]

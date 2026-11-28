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
u,v=map(F,Cq.gens())

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

CASES=('A2A2','A2A3','A2S','A3A3','A3S','SS')
def paid(phase,z):
    k=lambda x:1+2*x-x*x
    if phase=='S':return 2-z,k(z)/2,k(z)/2,[z,z-1,z-2,k(z)]
    a=z if phase=='A2' else z/2
    D=-2+a+4*a*a-a**3
    N=(1+4*a-4*a*a)*D+4*a*a*(3*a-2)
    g=[a,a-2,k(a),D,N,3*a-2]
    if phase=='A2':return 2*z,k(a)/2,N/(2*D),g
    return z/2,N/(2*D),k(a)/2,g
def frame(mode):
    front=mode[:1] if mode[0]=='S' else mode[:2]
    rear=mode[len(front):]
    s,fp,fs,gf=paid(front,u)
    t0,rp,rt,gr=paid(rear,v)
    H=u+v;t=H-t0;p=u;h=H/2;m=h+1
    Z=F()
    L3=lambda y:(y-h)**3-3*m*m*(y-h)/5
    L4=lambda y:(y-h)**4-6*m*m*(y-h)**2/7+3*m**4/35
    masks={'front_taps':gf,'rear_taps':gr,
           'clocks':[m]+[a-b for a,b in combinations((Z,H,p,s,t),2)],
           'legendre':[L4(p)]}
    gg=sum(masks.values(),[])
    assert all(gg) and all(a.d.is_constant() for a in gg)
    support=[ip(a.n) for a in gg]
    beta=-L4(p)/(fp*rp)
    T0=[-beta/2,2*L4(Z)]
    TH=[2*L4(H),-beta/2]
    Tp=[-beta*fp,-beta*rp]
    Ts=[-beta*fs,L4(s)/fs]
    Tt=[L4(t)/rt,-beta*rt]
    R0=[F(1)/2,Z]
    RH=[Z,F(1)/2]
    Rs=[fs,Z]
    Rt=[Z,rt]
    def gate(y,Y,anchor,V,L0,LH):
        J=lambda x,i:(H-x)*L0[i]+x*LH[i]
        return [anchor*(anchor-H)*(H*Y[i]-J(y,i))-y*(y-H)*(H*V[i]-J(anchor,i)) for i in (0,1)]
    Q=gate(s,Ts,p,Tp,T0,TH)
    W=gate(t,Tt,p,Tp,T0,TH)
    R=gate(t,Rt,s,Rs,R0,RH)
    lines=[Q,W,R]
    R2=[(H*Rs[i]-(H-s)*R0[i]-s*RH[i])/(H*s*(s-H)) for i in (0,1)]
    R1=[(RH[i]-R0[i])/H-H*R2[i] for i in (0,1)]
    Rcoefs=[R0,R1,R2]
    expect=sum(lines,[])+sum(Rcoefs,[])
    assert all(strip(ip(a.d),support).total_degree()==0 for a in expect)
    guards={k:[ip(a.n) for a in t0] for k,t0 in masks.items()}
    eq=lambda a:strip(ip(a.n),support)
    return lines,Rcoefs,eq,guards,(H,p,s,t,m,L3,L4,fp,fs,rp,rt,beta)
def rows_for(mode,kind):
    lines,_,eq,gg,_=frame(mode)
    if kind=='rank':P=sum(lines,[])
    else:P=[a*d-c*b for (a,b),(c,d) in combinations(lines,2)]
    return [eq(a) for a in P if a],gg
def project(mode,kind,method=None):
    rows,groups=rows_for(mode,kind)
    print(kind,mode,'degrees',[p.degrees() for p in rows],flush=True)
    assert all(r.total_degree()>0 for r in rows)
    common=rows[0]
    for r in rows[1:]:common=common.gcd(r)
    assert common.total_degree()==0
    if method is None:method=lambda a,b:a.resultant(b,'d')
    gs=[g for g in sum(groups.values(),[]) if not g.degrees()[1]]
    select=min(rows,key=lambda a:sum(a.degrees()))
    P=[strip(method(select,r),gs) for r in rows if r!=select]
    P=[p for p in P if p]
    assert P
    f=P[0]
    for p in P[1:]:f=f.gcd(p)
    assert f
    print(kind,mode,'projected degrees',[p.total_degree() for p in P],
          'u factors',[(p.total_degree(),k) for p,k in f.factor()[1]],flush=True)
    return f.factor()[1],rows,groups,[p.total_degree() for p in P]

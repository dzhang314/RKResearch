"""Pair equations for disjoint D labels, using exact FLINT polynomial fractions."""
from math import lcm
from flint import fmpq_mpoly_ctx,fmpz_mpoly_ctx
from collections import defaultdict
from itertools import combinations,product
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

CASES=[a+b for a,b in product(('A1','A2','S'),('A2','A3','S'))]
def taps(ph,w):
    k=1+2*w-w*w
    if ph=='S':return (w,2-w),(k/2,k/2),[w,w-1,w-2,k]
    D=-2+w+4*w*w-w**3
    N=(1+4*w-4*w*w)*D+4*w*w*(3*w-2)
    return (w,2*w),(k/2,N/(2*D)),[w,w-2,k,D,N,3*w-2]
def frame(mode):
    if mode[0]=='S':front='S';i=0
    else:front='A';i=int(mode[1])-1
    rear=mode[1:] if front=='S' else mode[2:]
    if rear=='A3':
        (r,rr,gt)=taps('A',v/2);j=1
    elif rear=='A2':
        (r,rr,gt)=taps('A',v);j=0
    else:
        (r,rr,gt)=taps('S',v);j=0
    assert r[j].n==v.n and r[j].d==v.d
    (f,ff,gf)=taps(front,u)
    p,q=f[i],f[1-i]
    fp,fq=ff[i],ff[1-i]
    rp,rt=rr[j],rr[1-j]
    H=p+v;t=H-r[1-j]
    h=H/2;m=h+1
    Z=F()
    L3=lambda y:(y-h)**3-3*m*m*(y-h)/5
    L4=lambda y:(y-h)**4-6*m*m*(y-h)**2/7+3*m**4/35
    masks={'front_taps':gf,'rear_taps':gt,
           'clocks':[m]+[a-b for a,b in combinations((Z,H,p,q,t),2)],
           'legendre':[L4(p),L4(q)]}
    guards=sum(masks.values(),[])
    assert all(guards) and all(a.d.is_constant() for a in guards)
    initial=[ip(a.n) for a in guards]
    b=(L3(q)/L4(q)-L3(p)/L4(p))/(q-p)
    a=L3(p)/L4(p)-b*p
    L=[L4(Z),-4*h**3+12*m*m*h/7,6*h*h-6*m*m/7,-4*h,F(1)]
    V=[L3(Z),3*h*h-3*m*m/5,-3*h,F(1),F()]
    Q=[V[i]-a*L[i]-(b*L[i-1] if i else F()) for i in range(5)]+[-b]
    M=div_linear(div_linear(Q,p),q)
    m0,m1,m2,m3=M
    assert b and m0 and m3
    masks['graph']=[b,m0]
    assert all(strip(ip(a.d),initial).total_degree()==0 for a in masks['graph'])
    base=initial+[ip(a.n) for a in masks['graph']]
    z0=m0*(H-t)/(m3*H*t*(t-H))
    z1=m0*(t-2*H*rt)/(m3*H*t*(t-H))
    beta=-L4(p)/(fp*rp)
    T0=[-beta/2,2*L4(Z)]
    TH=[2*L4(H),-beta/2]
    Tp=[-beta*fp,-beta*rp]
    Tq=[-beta*fq,L4(q)/fq]
    Tt=[L4(t)/rt,-beta*rt]
    lin=lambda y,i:(H-y)*T0[i]+y*TH[i]
    def read(y,val):
        return [p*(p-H)*(H*val[i]-lin(y,i))-y*(y-H)*(H*Tp[i]-lin(p,i)) for i in (0,1)]
    A,B=read(q,Tq);C,D=read(t,Tt)
    seen=sum(masks.values(),[])
    assert all(strip(ip(a.d),base).total_degree()==0 for a in seen+[A,B,C,D,z0,z1])
    groups={k:[ip(x.n) for x in g] for k,g in masks.items()}
    groups['denominators']=[ip(a.d) for a in seen]
    gg=sum(groups.values(),[])
    eq=lambda a:strip(ip(a.n),gg)
    data=(H,p,q,t,fp,fq,rp,rt,L3,L4,M,z0,z1,beta)
    lines=[A,B,C,D]
    return lines,eq,groups,data

def rank_project(mode):
    lines,eq,gg,_=frame(mode)
    rr=list(map(eq,lines))
    print(mode,'rank rows',[r.degrees() for r in rr],flush=True)
    g=rr[0]
    hs=[z for z in sum(gg.values(),[]) if not z.degrees()[1]]
    PP=[strip(g.resultant(z,'d'),hs) for z in rr[1:]]
    PP=[a for a in PP if a]
    assert [p.total_degree() for p in PP]==PROFILES[mode] and PP
    q=PP[0]
    for a in PP[1:]:q=q.gcd(a)
    assert q
    print(mode,'rank projection',[p.total_degree() for p in PP],
          'u factors',[(f.total_degree(),n) for f,n in q.factor()[1]],flush=True)
    return q.factor()[1],rr,gg


PROFILES={'A1A2':[61,57,59],'A1A3':[112,72,76],'A1S':[61,31,18],
          'A2A2':[49,60,64],'A2A3':[100,75,88],'A2S':[49,34,28],
          'SA2':[16,26,23],'SA3':[55,48,47],'SS':[16,8]}

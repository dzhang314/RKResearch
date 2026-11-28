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
H,u=map(F,Cq.gens())

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
def phases(mode):
    left='S' if mode[0]=='S' else mode[:2]
    return left,mode[len(left):]
def paid(ph,z):
    k=lambda x:1+2*x-x*x
    if ph=='S':return 2-z,k(z)/2,k(z)/2,[z,z-1,z-2,k(z)]
    a=z if ph=='A2' else z/2
    D=-2+a+4*a*a-a**3
    N=(1+4*a-4*a*a)*D+4*a*a*(3*a-2)
    g=[a,a-2,k(a),D,N,3*a-2]
    if ph=='A2':return 2*z,k(a)/2,N/(2*D),g
    return z/2,N/(2*D),k(a)/2,g
def frame(mo):
    l,r=phases(mo)
    s,fp,fs,fg=paid(l,u)
    h=H/2;m=h+1;Z=F()
    L=lambda x:(x-h)**4-6*m*m*(x-h)**2/7+3*m**4/35
    groups={'front_taps':fg,'initial':[H,m,s,H-s,L(u)]}
    gs=sum(groups.values(),[])
    assert all(gs) and all(x.d.is_constant() for x in gs)
    masks=[ip(a.n) for a in gs]
    w0=H-s-2*H*fs
    assert w0 and strip(ip(w0.d),masks).total_degree()==0
    groups['pivot']=[w0]
    masks+=[ip(w0.n)]
    t=s*(H-s)/w0
    z=H-t
    v=z/2 if r=='A2' else (2*z if r=='A3' else 2-z)
    q=H-v
    S,rp,rt,gt=paid(r,v)
    assert not (S-z)
    groups['rear_taps']=gt
    groups['clock_pairs']=[a-b for a,b in combinations((Z,H,u,q,s,t),2)]
    groups['legendre']=[L(q)]
    assert all(sum(groups.values(),[]))
    assert all(strip(ip(x.d),masks).total_degree()==0 for x in gt+groups['clock_pairs']+groups['legendre'])
    masks+=[ip(x.n) for x in gt+groups['clock_pairs']+groups['legendre']]
    R=fs*t*t/(H-s)**2
    eq=[L(s)-4*fs*fs*L(Z),L(t)-4*R*R*L(Z),rt-R]
    assert all(eq)
    assert all(strip(ip(x.d),masks).total_degree()==0 for x in eq)
    rows=[strip(ip(x.n),masks) for x in eq]
    groups={k:[ip(x.n) for x in t0] for k,t0 in groups.items()}
    return rows,groups
def project(mode):
    rr,G=frame(mode)
    print(mode,'rank-zero rows',[a.degrees() for a in rr],flush=True)
    assert all(z.total_degree()>0 for z in rr)
    ms=[g for g in sum(G.values(),[]) if not g.degrees()[0]]
    B=rr[0]
    P=[strip(B.resultant(a,'H'),ms) for a in rr[1:]]
    assert all(P)
    p=P[0].gcd(P[1]);assert p
    ff=p.factor()[1]
    print(mode,'projected degrees',[x.total_degree() for x in P],
          'u factors',[(q.total_degree(),n) for q,n in ff],flush=True)
    return ff,rr,G,[x.total_degree() for x in P]

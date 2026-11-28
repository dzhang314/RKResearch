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

def tap(ph,w):
    k=1+2*w-w*w
    if ph=='S':return (w,2-w),(k/2,k/2),[w,w-1,w-2,k]
    D=-2+w+4*w*w-w**3
    N=(1+4*w-4*w*w)*D+4*w*w*(3*w-2)
    return (w,2*w),(k/2,N/(2*D)),[w,w-2,k,D,N,3*w-2]
def divrem(a,r):
    b=a[1:]
    for i in range(len(b)-2,-1,-1):b[i]+=r*b[i+1]
    return b,a[0]+r*b[0]
def frame(left,right,i,j):
    (uf,ff,at),(vr,rr,ar)=tap(left,u),tap(right,v)
    H=uf[i]+vr[j]
    h=H/2;m=h+1
    p=uf[i];q=uf[1-i];r=H-vr[1-j]
    fp,fq=ff[i],ff[1-i];rp,rq=rr[j],rr[1-j]
    S=F()
    g={'front_taps':at,'rear_taps':ar,
       'clocks':[m]+[a-b for a,b in combinations((S,H,p,q,r),2)]}
    L3=lambda y:(y-h)**3-3*m*m*(y-h)/5
    L4=lambda y:(y-h)**4-6*m*m*(y-h)**2/7+3*m**4/35
    g['legendre']=[L4(z) for z in (p,q,r)]
    assert all(sum(g.values(),[]))
    known=sum(g.values(),[])
    prelim=[ip(a.n) for a in known]
    assert all(a.d.is_constant() for a in known)
    L=[L4(S),-4*h**3+12*m*m*h/7,6*h*h-6*m*m/7,-4*h,F(1)]
    M=[L3(S),3*h*h-3*m*m/5,-3*h,F(1),F()]
    a1=(L3(q)/L4(q)-L3(p)/L4(p))/(q-p)
    a0=L3(p)/L4(p)-p*a1
    W=[M[i]-a0*L[i]-(a1*L[i-1] if i else F()) for i in range(5)]+[-a1]
    R0,E=divrem(div_linear(div_linear(W,p),q),r)
    t0=R0[0];tH=ev(R0,H)
    assert a1 and t0 and tH
    g['graph_pivots']=[a1,t0,tH]
    assert all(strip(ip(a.d),prelim).total_degree()==0 for a in g['graph_pivots'])
    allowed=prelim+[ip(a.n) for a in [t0,tH]]
    lam=tH/t0
    R=lambda y:ev(R0,y)/(2*t0)
    beta=-L4(p)/(fp*rp)
    T0=2*lam*L4(S)-beta/2
    TH=2*L4(H)-beta*lam/2
    Tp=-beta*(fp+lam*rp)
    Tq=lam*L4(q)/fq-beta*fq
    Tr=L4(r)/rq-beta*lam*rq
    li=lambda y:(H-y)*T0+y*TH
    read=lambda y,b:p*(p-H)*(H*b-li(y))-y*(y-H)*(H*Tp-li(p))
    X=read(q,Tq);Y=read(r,Tr)
    g['shared_pair']=[fp-lam*rp]
    g['graph_off']=[fp-R(p),lam*rp-R(p),fq-R(q),lam*rq-R(r)]
    gs=sum(g.values(),[])
    assert all(gs)
    assert all(strip(ip(a.d),allowed).total_degree()==0 for a in gs)
    groups={k:[ip(a.n) for a in z] for k,z in g.items()}
    groups['denominators']=[ip(a.d) for a in gs]
    gg=sum(groups.values(),[])
    assert all(strip(ip(a.d),gg).total_degree()==0 for a in [E,X,Y])
    rows=[strip(ip(a.n),gg) for a in [E,X,Y]]
    assert all(rows)
    return rows,groups
CASES={'AS11':('A','S',0,0),'AS21':('A','S',1,0),'AA11':('A','A',0,0),
       'AA12':('A','A',0,1),'AA22':('A','A',1,1),'SS11':('S','S',0,0)}
def project(mode,method=None):
    rows,groups=frame(*CASES[mode])
    E,X,Y=rows
    print(mode,'rows',[x.degrees() for x in rows],flush=True)
    if any(x.total_degree()==0 for x in rows):return [],rows,groups
    assert [x.degrees() for x in rows]==DEGREES[mode][0]
    gg=[a for a in sum(groups.values(),[]) if not a.degrees()[1]]
    if method is None:method=lambda a,b:a.resultant(b,'d')
    aa=[method(E,p) for p in (X,Y)]
    pp=[strip(a,gg) for a in aa]
    print(mode,'projection degrees raw',[p.total_degree() for p in aa],
          'guarded',[p.total_degree() for p in pp],flush=True)
    assert ([a.total_degree() for a in aa],[p.total_degree() for p in pp])==DEGREES[mode][1:]
    assert all(pp)
    cc=pp[0].gcd(pp[1]);assert cc
    ff=cc.factor()[1]
    print(mode,'u factors',[(q.total_degree(),n) for q,n in ff],flush=True)
    return ff,rows,groups

DEGREES = {
 'AS11': ([(9,9),(19,14),(14,13)],[180,126],[180,126]),
 'AS21': ([(9,9),(16,14),(17,13)],[153,153],[153,153]),
 'AA11': ([(8,8),(19,14),(14,19)],[160,160],[160,160]),
 'AA12': ([(9,9),(19,17),(14,16)],[207,153],[203,152]),
 'AA22': ([(8,8),(16,17),(17,16)],[160,160],[157,160]),
 'SS11': ([(8,8),(13,14),(14,13)],[112,112],[112,112])}

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

CASES=('SS','A3A3','A2A2')
def DD(z):return -2+z+4*z*z-z**3
def kk(z):return 1+2*z-z*z
def NN(z):return (1+4*z-4*z*z)*DD(z)+4*z*z*(3*z-2)
def frame(mo):
    h=H/2;m=1+h;Z=F();one=F(1)
    if mo=='SS':
        p=2-a;g=fs=kk(a)/2;kap=kk(a)
        tg=[a,a-1,a-2,kap]
    else:
        p=2*a if mo=='A3A3' else a/2
        u=a if mo=='A3A3' else a/2
        kap=kk(u)
        gg=NN(u)/(2*DD(u));f0=kap/2
        g,fs=(gg,f0) if mo=='A3A3' else (f0,gg)
        tg=[u,u-2,kap,DD(u),NN(u),3*u-2]
    q=H-p;t=H-a
    d=p-h;x=a-h
    raw={'known':[H,m]+[r-s for r,s in combinations((Z,H,p,q,a,t,h),2)],
         'taps':tg}
    m0=sum(raw.values(),[])
    assert all(m0) and all(z.d.is_constant() for z in m0)
    masks=[ip(z.n) for z in m0]
    def add(key,g):
        assert all(g) and all(strip(ip(a.d),masks).total_degree()==0 for a in g)
        raw[key]=g;masks.extend(ip(z.n) for z in g)
    L=lambda w:w**4-6*m*m*w*w/7+3*m**4/35
    lh=L(h);ld=L(d);lx=L(x);lz=L(Z)
    invA=a*(a-H)
    r=(fs-one/2)/invA
    slope=(d*d-3*m*m/5)/ld
    add('graph_anchors',[ld,lz])
    add('graph_pivots',[r,slope])
    eta=h*h-1/(2*r)
    E=eta-(1/slope+6*m*m/7-d*d)
    C2=(lx/fs-2*lh)/invA
    C=lambda w:2*lh+C2*(w*w-h*h)
    R=lambda w:one/2+r*(w*w-h*h)
    lead=1-r*C2
    prod=g*(g-R(d))
    add('paid_graph',[lead,prod])
    B=(ld-g*C(d))/prod
    add('B',[B])
    A=lambda w:C(w)-B*R(w)
    mate=-ld/(B*g)
    assert mate
    # Trace weight formula on p3(w)=w(w^2-d^2), H_s(w)=lead*(w^2-h^2)*(w^2-x^2).
    H3=4*m**6/175
    p3=lambda w:w*(w*w-d*d)
    p3p=lambda w:3*w*w-d*d
    Hs=lambda w:lead*(w*w-h*h)*(w*w-x*x)
    Hsp=lambda w:2*w*lead*(2*w*w-h*h-x*x)
    gr=-r*H3/slope
    DDw=lambda w:gr*(A(w)**2+B*L(w)+A(w)*B*R(w))/(p3p(w)*Hs(w)*L(w)**2)
    SSw=lambda w:gr/(p3(w)*Hsp(w)*R(w)**2)
    for w in [h,x]:
        add('single' + ('H' if w is h else 'S'),[p3(w),Hsp(w),R(w)])
    for w in [Z,d]:
        add('double'+('0' if w is Z else 'D'),[p3p(w),Hs(w)])
    weighted=DDw(Z)+2*DDw(d)+2*SSw(h)+2*SSw(x)
    unweighted=4+2/fs+A(Z)/lz+2*A(d)/ld
    Zt=unweighted-m*weighted
    # Degree-two actual normalized x=1+y interpolant.
    # x values 1,1+p,1+a; denom each literal distinct.
    W=[Z,Z,Z]
    for v,dv in [(one,one/2),(one+p,g),(one+a,fs)]:
        other=[w for w in [one,one+p,one+a] if (w-v)]
        i,j=other
        fac=dv/((v-i)*(v-j))
        W[0]+=fac*i*j;W[1]-=fac*(i+j);W[2]+=fac
    c0,c1,c2=W
    def affine(w):
        X=1+h+w
        T=c0+c1*X+c2*X*X
        J=c0*X+c1*X*X/2+c2*X**3/3
        La=1+(X-1)/kap
        De=4*one/3+2*(kap+1)*(X-1)/(3*kap)
        return 1-La+c1+c2*De,T-J
    v0,w0=affine(Z)
    vp,wp=affine(d)
    vq,wq=affine(-d)
    qy=[E,Zt,mate*vp-wp,mate*vq-wq,v0,w0]
    assert all(strip(ip(z.d),masks).total_degree()==0 for z in qy)
    eq=[strip(ip(x.n),masks) for x in qy]
    gs={k:[ip(x.n) for x in ls] for k,ls in raw.items()}
    return eq,gs
def project(mo):
    eq,gs=frame(mo)
    E,T,P,Q,C,N=eq
    gg=[a for a in sum(gs.values(),[]) if not a.degrees()[1]]
    print(mo,'rows',[r.degrees() for r in eq],flush=True)
    rr0=lambda a,b:strip(a.resultant(b,'d'),gg)
    rr=[rr0(E,r) for r in eq[1:]]
    print(mo,'outer degrees',[p.total_degree() for p in rr],flush=True)
    assert all(rr)
    h0,q0,q1,c0,n0=rr
    gg=[h0.gcd(q0),h0.gcd(q1),h0.gcd(c0).gcd(n0)]
    ff=[g.factor()[1] for g in gg]
    for z,f in zip(['plus','minus','centre'],ff):
        print(mo,z,'factors',[(q.total_degree(),n) for q,n in f],flush=True)
    return ff,eq,gs,[p.total_degree() for p in rr]

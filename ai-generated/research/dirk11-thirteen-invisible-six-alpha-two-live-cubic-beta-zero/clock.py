#!/usr/bin/env python3
"""Corrected beta-zero ordinary/profile eliminants and guarded residue ranks.

The first projection is over Q[V]. Residue fields are used only to exhibit
nonzero minors of matrices already defined over an exact clock field.
"""
from fractions import Fraction
from math import lcm,gcd,comb
from time import monotonic
import argparse
from flint import fmpq,fmpq_poly,nmod_poly,nmod_mat
parser=argparse.ArgumentParser()
parser.add_argument('tower',choices=('regular','F1','F2','Fn'))
args=parser.parse_args()
baseMod=None
p=0
start_time=monotonic()
def log(*x): print(f'{monotonic()-start_time:8.2f}',*x,flush=True)
class Base:
    def to(self,x):
        if isinstance(x,PE):return x
        if isinstance(x,E):raise TypeError('upper algebra')
        if isinstance(x,(tuple,list)):
            return PE(POL([co(a) for a in x]))
        return PE(POL([co(x)]))
    def gen(self): return self.to([0,1])
base=Base()
def co(x):
    q=Fraction(x)
    if p:return q.numerator*pow(q.denominator,-1,p)%p
    return q.numerator if q.denominator==1 else fmpq(q.numerator,q.denominator)
POL=lambda c: nmod_poly(c,p) if p else fmpq_poly(c)
class PE:
    __slots__=('f',)
    def __init__(self,f):self.f=f%baseMod if baseMod is not None and f.degree()>=baseMod.degree() else f
    r=base
    def __eq__(self,x):
        if isinstance(x,E):return NotImplemented
        return self.f==base.to(x).f
    def __add__(self,x):
        if isinstance(x,E):return NotImplemented
        return PE(self.f+base.to(x).f)
    __radd__=__add__
    def __neg__(self):return PE(-self.f)
    def __sub__(self,x):
        if isinstance(x,E):return NotImplemented
        return PE(self.f-base.to(x).f)
    def __rsub__(self,x):
        if isinstance(x,E):return NotImplemented
        return base.to(x)-self
    def __mul__(self,x):
        if isinstance(x,E):return NotImplemented
        return PE(self.f*base.to(x).f)
    __rmul__=__mul__
    def __pow__(self,n):return PE(self.f**n)
    def __repr__(self):return str(self.f)
    def scale(self,z):return PE(self.f*co(z))
    def div_exact(self,f):
        q,r=divmod(self.f,f)
        assert r==0
        return PE(q)
class R:
    def __init__(self,low,mod,name):
        self.low=low; self.mod=tuple(low.to(c)for c in mod); self.n=len(mod)
        self.name=name
        self.z=low.to(0); self.o=low.to(1)
    def to(self,x):
        if isinstance(x,E) and x.r is self:return x
        return E(self,(self.low.to(x),)+(self.z,)*(self.n-1))
    def gen(self):return E(self,(self.z,self.o)+(self.z,)*(self.n-2))
class E:
    __slots__=('r','cs')
    def __init__(self,r,cs):self.r=r;self.cs=tuple(cs)
    def __eq__(self,x):
        try:return self.cs==self.r.to(x).cs
        except TypeError:return NotImplemented
    def __add__(self,x):
        try:z=self.r.to(x)
        except TypeError:return NotImplemented
        return E(self.r,[a+b for a,b in zip(self.cs,z.cs)])
    __radd__=__add__
    def __neg__(self):return E(self.r,[-x for x in self.cs])
    def __sub__(self,x):
        try:z=self.r.to(x)
        except TypeError:return NotImplemented
        return E(self.r,[a-b for a,b in zip(self.cs,z.cs)])
    def __rsub__(self,x):
        try:z=self.r.to(x)
        except TypeError:return NotImplemented
        return z-self
    def __mul__(self,x):
        if not isinstance(x,E) or x.r is not self.r:
            try:s=self.r.low.to(x)
            except TypeError:return NotImplemented
            return E(self.r,[a*s for a in self.cs])
        RR=self.r
        z=mul(self.cs,x.cs)
        return E(RR,rem(z,(*RR.mod,RR.o)))
    __rmul__=__mul__
    def __pow__(self,n):
        if n==0:return self.r.to(1)
        if n==1:return self
        z=self**(n//2)
        return z*z*self if n&1 else z*z
    def scale(self,q):return E(self.r,[a.scale(q) for a in self.cs])
    def div_exact(self,d):return E(self.r,[a.div_exact(d)for a in self.cs])
    def __repr__(self):return repr(self.cs)
def mul(f,g):
    r=f[0].r
    z=[r.to(0)]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a!=0:
            for j,b in enumerate(g):
                if b!=0:z[i+j]+=a*b
    return z
def rem(f,g):
    z=list(f)
    d=len(g)-1
    for i in range(len(z)-1,d-1,-1):
        k=z[i]
        if k!=0:
            for j,c in enumerate(g[:-1]):
                if c!=0:z[i-d+j]-=k*c
    return z[:d]+[f[0].r.to(0)]*max(0,d-len(z))
def cofact(f,x):
    a=x.r.to(f[-1])
    out=[a]
    for c in reversed(f[1:-1]):
        a=a*x+x.r.to(c);out.append(a)
    assert a*x+x.r.to(f[0])==0
    return list(reversed(out))
def ev(f,x):
    a=x.r.to(0)
    for c in reversed(f):a=a*x+x.r.to(c)
    return a
def prim(f):
    return [f[0].r.to(0),*(a.scale(Fraction(1,i+1)) for i,a in enumerate(f))]
def pplus(f,g):
    if len(f)<len(g):return pplus(g,f)
    return [*(a+b for a,b in zip(f,g)),*f[len(g):]]
def pscale(f,z): return [a*z for a in f]
def det(M):
    if len(M)==1:return M[0][0]
    if len(M)==2:return M[0][0]*M[1][1]-M[0][1]*M[1][0]
    return sum((-1)**i*c*det([[x for j,x in enumerate(row) if j!=i] for row in M[1:]])for i,c in enumerate(M[0]) if c!=0)
def cols(*C):return list(zip(*C))
def adjcol(M):
    return [(-1)**i*det([[M[j][k]for k in range(len(M))if k!=i]for j in range(1,len(M))])for i in range(len(M))]
def norm(x):
    y=x.r.gen()
    zs=[x]
    for _ in range(x.r.n-1):zs.append(zs[-1]*y)
    return det(cols(*(a.cs for a in zs)))
def flatten(x):
    if isinstance(x,PE):return [x.f]
    return sum([flatten(c)for c in x.cs],[])
def monic_f(f):
    if p:return f*f.leading_coefficient().__pow__(-1)
    return f/f.leading_coefficient()
def content(*xs):
    aa=sum([flatten(x)for x in xs],[])
    d=POL([])
    for a in aa:
        if a!=0:d=d.gcd(a)
        if d.degree()==0:break
    return monic_f(d)
def lose(name,*xs):
    d=content(*xs)
    if d.degree()>0:
        u=POL([1,-14,56,-84,42])*POL([0,-1,1])*POL([1,-16,72,-120,66])*POL([3,-32,108,-144,66])*POL([3,-64,604,-3096,9360,-17136,18648,-11088,2772])
        f=d
        while (q:=f.gcd(u)).degree()>0: f=f//q
        assert f.degree()==0,(name,'unexpected scalar removal',f)
        xs=tuple(x.div_exact(d)for x in xs)
    fs=sum([flatten(x)for x in xs],[])
    l=lcm(*(int(f.denom())for f in fs))
    g=gcd(*(int(f.numer().content())*(l//int(f.denom()))for f in fs))
    if g: xs=tuple(x.scale(Fraction(l,g))for x in xs)
    log(name,'normalized coefficient degree',
        max(a.degree() for x in xs for a in flatten(x)),
        'guarded content degree',d.degree())
    return xs

v=base.gen()
J4=lambda y:42*y**4-84*y**3+56*y*y-14*y+1
J5=lambda y:(2*y-1)*(66*y**4-132*y**3+84*y*y-18*y+1)
L=132*J4(v)
Traw=pplus(pscale([base.to(c)for c in (-1,20,-120,300,-330,132)],J4(v)),pscale([base.to(c)for c in (1,-14,56,-84,42)],-J5(v)))
T4raw=cofact(Traw,v)
T4=[T4raw[i]*L**(3-i)for i in range(4)]+[base.to(1)]
K=R(base,T4[:-1],'fifth ordinary')
B=K.gen()
R3=cofact(T4,B)
c0,c1,c2,_=R3
Fn=[-c0*c1*c1,-12*c0*c1+12*c0*c2*c2-c1*c1*c2,-36*c0-4*c1*c2,12*c2]
if args.tower=='F1':
    Fn=[-75*c0*c0,75*c0*c2,-80*c1,K.to(96)]
elif args.tower=='F2':
    Fn=[-c0*c0,c0*c2,-c1,K.to(1)]
L3=Fn[-1]
S=R(K,[Fn[i]*L3**(2-i)for i in range(3)],'Fn quadratic profile')
ss=S.gen()
B,L3,c0,c1,c2,L=(S.to(x)for x in (B,L3,c0,c1,c2,L))
V=S.to(v)*L
a,b=L-V,L-B
zero,one=S.to(0),S.to(1)
R3=[c0,c1,c2,one]
if args.tower=='F1':
    t1=16*c0*ss*L3*L3
    t0=16*ss*ss*(2*ss+c1*L3)-15*c0*(c2*ss-c0*L3)*L3*L3
elif args.tower=='F2':
    t1=c0*ss*L3*L3
    t0=ss*ss*(2*ss+c1*L3)-c0*(c2*ss-c0*L3)*L3*L3
elif args.tower=='Fn':
    t1=c0*(c1*L3+6*ss)*L3*L3
    t0=ss*(2*ss+c1*L3)*(c1*L3+6*ss)-6*c0*c2*ss*L3*L3
else:
    t1=c1*L3+6*ss
    t0=6*c2*ss
A1_TERMS=[((5, 0, 1, 0), -30), ((4, 1, 0, 1), 46), ((4, 0, 2, 1), 60), ((4, 0, 0, 2), 276), ((3, 1, 1, 2), -92), ((3, 0, 3, 2), -30), ((3, 0, 1, 3), -834), ((2, 2, 0, 3), 47), ((2, 1, 2, 3), 46), ((2, 1, 0, 4), 424), ((2, 0, 2, 4), 558), ((2, 0, 0, 5), 852), ((1, 2, 1, 4), -47), ((1, 1, 1, 5), -520), ((1, 0, 1, 6), -1044), ((0, 3, 0, 5), 16), ((0, 2, 0, 6), 160), ((0, 1, 0, 7), 448), ((0, 0, 0, 8), 384)]
A1gate=sum(n*c0**i*c1**j*c2**k*ss**h*L3**(8-h)for (i,j,k,h),n in A1_TERMS)
m=lose('common m scale',ss*t1,t0*L3,t1*L3)
M=cols(*(rem([zero]*i+list(m),R3)for i in range(3)))
adj=lose('common old inverse scale',*adjcol(M))
den,eq1,eq2=rem(mul(m,adj),R3)
assert eq1==eq2==0
J4p=[L**4,-14*L**3,56*L**2,-84*L,42*one]
A0=prim([zero,*R3])[1:]; A1=prim([zero,zero,*R3])[1:]
def old(f):return rem(mul(adj,f),R3)
U=old(J4p); W=old(A0); Q=old(A1)
all9=lose('common quotient fit scale',*U,*W,*Q)
U,W,Q=(list(all9[i:i+3])for i in (0,3,6))
def monic_div(A,B):
    x=list(A); n=len(B)-1
    if len(x)<len(B):return [],x
    assert B[-1]==1
    q=[x[0].r.to(0)]*(len(A)-n)
    for j in range(len(x)-1,n-1,-1):
        c=x[j];q[j-n]=c
        if c!=0:
            for i,g in enumerate(B[:-1]):x[j-n+i]-=c*g
    return q,x[:n]
d4,chk=monic_div(pplus(mul(A0,U),pscale(mul(W,J4p),-one)),R3)
assert all(x==0 for x in chk)
d5,chk=monic_div(pplus(mul(A1,U),pscale(mul(Q,J4p),-one)),R3)
assert all(x==0 for x in chk)
def refl(f):
    n=len(f)-1
    from math import comb
    return [(-1)**i*sum(comb(j,i)*f[j]*L**(j-i)for j in range(i,n+1)) for i in range(n+1)]
def wedge(u,v):return u[0]*v[1]-u[1]*v[0]
def psrem(f,g):
    cs=list(f)
    d=len(g)-1
    ell=g[-1]
    for i in range(len(cs)-1,d-1,-1):
        c=cs[i]
        for j in range(i):
            cs[j]*=ell
        if c!=0:
            for j in range(d):
                cs[i-d+j]-=c*g[j]
    return cs[:d]+[zero]*max(0,d-len(cs))
qV=ev(d4,V)
lV=ev(A0,V)
pV=ev(d5,V)
mV=ev(A1,V)
JV,JB=ev(J4p,V),ev(J4p,B)
W2=W[-1]
u,q=(psrem(f,W)for f in (U,Q))
rr=psrem(R3,W)
J0=JV*W2*wedge(q,u)+pV*wedge(rr,u)
J1=JV*wedge(q,rr)+mV*wedge(rr,u)
E1=lV*J0-qV*J1
C=[lV*U[i]-qV*R3[i]for i in range(3)]+[-qV]
# Genuine adjacent B commutator. All polynomials in D4 are reverse.
CV=ev(C,B); D4=pplus(pscale(d4,lV),pscale(A0,-qV))
# J(b)/b is a forward evaluation, computed with the reflected C.
Jb=ev(prim([zero,*refl(C)])[1:],b)
Adj=((B-V)*CV-Jb)*ev(D4,B)-(B-V)*Jb*CV
eqs=[('reverse',E1),('adjacent',Adj)]
if args.tower!='regular':eqs.append(('singular-pivot',A1gate))
def descend(e):
    while isinstance(e,E):e=norm(e)
    return e.f
def project(name,e):
    e,=lose(name+' input',e)
    while isinstance(e,E):
        e=norm(e)
        if isinstance(e,E):e,=lose(name+' relative',e)
    f=e.f/e.f.leading_coefficient()
    log(name,'projection',f.degree())
    return f
g=None
for n,u in eqs:
    h=project(n,u)
    g=h if g is None else g.gcd(h)
log('exact joint degree',g.degree())
z=fmpq_poly([0,1])
j4=fmpq_poly([1,-14,56,-84,42]);j5=fmpq_poly([-1,20,-120,300,-330,132])
j_minus=fmpq_poly([1,-16,72,-120,66])
j_plus=fmpq_poly([3,-32,108,-144,66])
j_rep=fmpq_poly([3,-64,604,-3096,9360,-17136,18648,-11088,2772])
assert j5-j4==2*(z-1)*j_minus and j5+j4==2*z*j_plus
assert j5.derivative()*j4-j5*j4.derivative()==2*j_rep
forbidden=[j4,j_minus,j_plus,j_rep]
plan={
 'regular':{(60,-1461941766456):('old-norm',11,1),(12,16227):('profile-ratio',11,12),(12,54123):('c2',9,4)},
 'F1':{(36,137146315515648):('old-norm',11,1)},
 'F2':{(36,-4682817):('old-norm',11,36)},
 'Fn':{(48,162325396752128559):('old-norm',11,2),(12,54123):('c2',9,4)}
}[args.tower]
seen=set()
gs={'old-norm':den,'profile-ratio':t1,'c2':c2}
us={}
todo=[]
qmonic=lambda f:f/f.leading_coefficient()
for f,mul0 in g.numer().factor()[1]:
    f0=fmpq_poly(f)
    if any(qmonic(f0)==qmonic(h)for h in forbidden):
        log('forbidden exact factor',f.degree(),int(f[0]),mul0)
        continue
    ID=(f.degree(),int(f[0]))
    assert ID not in seen
    seen.add(ID)
    k,cap,d=plan[ID]
    if k not in us:us[k]=descend(gs[k])
    assert us[k]!=0 and us[k]%f0==0
    todo.append((f,k,cap,d))
    log('allowed clock factor',ID,mul0,k,cap,d)
assert seen==set(plan)

def rank_receipt(f,k,cap,d):
    global p,baseMod
    p=103
    ff=nmod_poly(list(map(int,f.coeffs())),p)
    assert ff.degree()==f.degree()
    ff=sorted((e for e,_ in ff.factor()[1]),key=lambda q:(q.degree(),list(map(int,q.coeffs()))))[0]
    assert ff.degree()==d
    baseMod=ff
    cache={}
    def cv(e):
        if isinstance(e,PE):
            return PE(nmod_poly([int(x.numerator)*pow(int(x.denominator),-1,p)%p for x in e.f.coeffs()],p))
        rr=e.r
        if id(rr) not in cache:
            mm=[cv(x)for x in rr.mod]
            lo=base if rr.low is base else cache[id(rr.low)]
            cache[id(rr)]=R(lo,mm,rr.name)
        return E(cache[id(rr)],tuple(cv(x)for x in e.cs))
    es=[cv(g)for _,g in eqs]
    gg=cv(gs[k])
    top=gg.r
    def vect(e):
        if isinstance(e,PE):
            a=list(map(int,e.f.coeffs()))
            return a+[0]*(d-len(a))
        return sum([vect(t)for t in e.cs],[])
    def basis(r):
        if r is base:return [base.gen()**j for j in range(d)]
        lo=basis(r.low)
        return [r.to(x)*r.gen()**i for i in range(r.n)for x in lo]
    bs=basis(top)
    assert len(bs)==12*d
    col=[vect(gg*e*x)for e in es for x in bs]
    rank=nmod_mat(list(map(list,zip(*col))),p).rank()
    assert rank==cap*d
    log('exact-field certificate',f.degree(),int(f[0]),k,'residue',d,'rank',rank)
    p=0;baseMod=None
for f,k,cap,d in todo:
    rank_receipt(f,k,cap,d)
log('corrected beta=0 closure',args.tower)

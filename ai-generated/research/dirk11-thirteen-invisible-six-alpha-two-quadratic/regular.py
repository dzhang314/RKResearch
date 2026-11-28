#!/usr/bin/env python3
"""Exact or residue finite clock arithmetic for the alpha-two d_V=0 chart."""
from fractions import Fraction
from itertools import permutations,combinations
from math import lcm,gcd
from pathlib import Path
import sys
from time import monotonic
import argparse
from flint import fmpq,fmpq_poly,fmpz_poly,nmod_poly,nmod_mat
parser=argparse.ArgumentParser()
parser.add_argument('--p',type=int,default=101)
parser.add_argument('--chart',choices=('reverse','forward','quintic','all'),default='all')
parser.add_argument('--write',type=Path)
parser.add_argument('--no-extra',action='store_true')
parser.add_argument('--first-only',action='store_true')
parser.add_argument('--raw',action='store_true')
parser.add_argument('--trace-guards',action='store_true')
parser.add_argument('--verify-over',type=Path)
parser.add_argument('--verify-prime',type=int,default=101)
parser.add_argument('--rank-guard',choices=('J4','c0','c2','old-norm','carrier-leading','carrier-at-a','carrier-at-b','carrier-at-origin','profile-constant','profile-ratio','w0-leader','RV','clock-derivative','forward-a','forward-b','ordinary-pair'))
parser.add_argument('--rank-file',type=Path)
parser.add_argument('--rank-factor',type=int,default=0)
parser.add_argument('--rank-residue-factor',type=int,default=0)
parser.add_argument('--keep',action='store_true')
args=parser.parse_args()
baseMod=None
p=args.p
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
def lose(name,*xs,strip=True):
    global ledger
    if args.keep or args.verify_over and p:return xs
    d=content(*xs)
    if d.degree() and strip:
        ledger.append((name,d));xs=tuple(x.div_exact(d)for x in xs)
    if not p:
        fs=sum([flatten(x)for x in xs],[])
        l=lcm(*(int(f.denom())for f in fs))
        g=gcd(*(int(f.numer().content())*(l//int(f.denom()))for f in fs))
        if g:xs=tuple(x.scale(Fraction(l,g))for x in xs)
    log(name,'deg',max(a.degree()for x in xs for a in flatten(x)),'content',d.degree() if strip else 'uncleared')
    return xs
def homog(f,x,d):
    return sum(x.r.to(c)*x**i*d**(len(f)-1-i)for i,c in enumerate(f))

ledger=[]
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
L3=Fn[-1]
S=R(K,[Fn[i]*L3**(2-i)for i in range(3)],'Fn quadratic profile')
ss=S.gen()
B,L3,c0,c1,c2,L=(S.to(x)for x in (B,L3,c0,c1,c2,L))
V=S.to(v)*L
a,b=L-V,L-B
zero,one=S.to(0),S.to(1)
R3=[c0,c1,c2,one]
t1=c1*L3+6*ss
t0=6*c2*ss
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
Rg=ev(d4,V)
d5V=ev(d5,V)
UF=[U[0]+U[1]*L+U[2]*L**2,-U[1]-2*U[2]*L,U[2]]
pure=prim(mul([zero,-b,one],UF))[1:]
clear=pplus(pscale(pure,ev(J4p,b)),pscale(J4p,-ev(pure,b)))
Fg=ev(cofact(clear,b),a)
log('reverse and forward zero-diagonal gates prepared')
def prepare_quintic():
    # W_2 is live. Reduce two quadratics by it without dividing any
    # coefficient, and reduce R in the same basis with an extra W_2.
    w0,w1,w2=W
    def red(f):return [w2*f[i]-f[2]*W[i]for i in range(2)]
    u0,u1=red(U); q0,q1=red(Q)
    rr0=c0*w2*w2-c2*w0*w2+w0*w1
    rr1=c1*w2*w2-c2*w1*w2-w0*w2+w1*w1
    Qg=w2*ev(J4p,V)*(q0*u1-q1*u0)+d5V*(rr0*u1-rr1*u0)
    return Qg
def live_guards():
    return {'J4':L,'c0':c0,'c2':c2,'old-norm':den,'carrier-leading':U[-1],
       'carrier-at-a':ev(U,V),'carrier-at-b':ev(U,B),'carrier-at-origin':ev(U,L),
       'profile-constant':ss,'profile-ratio':t1,'w0-leader':W[-1],
       'RV':ev(R3,V),'clock-derivative':ev([T4[i]*i for i in range(1,5)],B),
       'forward-a':a,'forward-b':b,'ordinary-pair':a-b}
if args.verify_over:
    assert not p
    vals0=live_guards() if args.rank_guard else None
    qexact=prepare_quintic() if args.chart in ('quintic','all') else None
    p=args.verify_prime
    vals=[int(x)for x in args.verify_over.read_text().split()]
    if args.rank_guard:
        f0,k=fmpz_poly(vals).factor()[1][args.rank_factor]
        assert args.rank_file
        cert=fmpq_poly([fmpq(x)for x in args.rank_file.read_text().split()]).numer()
        assert f0.gcd(cert).degree()==f0.degree()
        vals=list(map(int,f0.coeffs()))
    F=nmod_poly(vals,p)
    assert F.degree()==len(vals)-1
    baseMod=monic_f(F)
    if args.rank_guard:
        sub=sorted([a for a,k in F.factor()[1]],key=lambda z:(z.degree(),list(map(int,z.coeffs()))))
        baseMod=sub[args.rank_residue_factor]
        log('chosen residue factor',baseMod)
    cache={}
    def conv(e):
        if isinstance(e,PE):
            return PE(nmod_poly([int(x.numerator)*pow(int(x.denominator),-1,p)%p for x in e.f.coeffs()],p))
        R0=e.r
        if id(R0) not in cache:
            mod=[conv(x)for x in R0.mod]
            low=base if R0.low is base else cache[id(R0.low)]
            cache[id(R0)]=R(low,mod,R0.name)
        return E(cache[id(R0)],tuple(conv(x)for x in e.cs))
    if args.rank_guard:
        guard=conv(vals0[args.rank_guard])
    # Convert the actual gates including exact upstream quotient.
    if qexact is not None:Qg=conv(qexact)
    Rg,Fg=conv(Rg),conv(Fg)
    S=Rg.r
    log('exact upstream coefficients reduced',p,baseMod.degree())
else:
    if args.chart in ('quintic','all'):Qg=prepare_quintic()
def save(n,f):
    if args.write:
        (args.write/(n+'.txt')).write_text(' '.join(map(str,f.coeffs()))+'\n')
def monic_kernel(n,e):
    if args.verify_over:
        while isinstance(e,E):e=norm(e)
        g,a,b=baseMod.xgcd(e.f)
        assert g==a*baseMod+b*e.f
        log(n,'gcd degree',g.degree())
        return g
    e,=lose(n+'-input',e)
    while isinstance(e,E):
        e=norm(e)
        log(n,'norm',max(f.degree()for f in flatten(e)))
        if isinstance(e,E):e,=lose(n+'-relative-content',e)
    f=monic_f(e.f)
    log(n,'base degree',f.degree())
    save(n,f)
    return f
def guard_rank(g,es):
    assert args.rank_guard and g.r is S
    def vector(e):
        if isinstance(e,PE):
            ca=list(map(int,e.f.coeffs()))
            return ca+[0]*(baseMod.degree()-len(ca))
        return sum([vector(c)for c in e.cs],[])
    def basis(r):
        if r is base:return [base.gen()**j for j in range(baseMod.degree())]
        lo=basis(r.low)
        out=[r.to(c)*r.gen()**j for j in range(r.n)for c in lo]
        return out
    basis0=basis(S)
    def dims(e):
        cols0=[vector(c*u)for u in basis0 for c in e]
        return nmod_mat(list(map(list,zip(*cols0))),p).rank()
    gg=dims([g]); ee=dims([g*c for c in es])
    cap=9 if args.rank_guard in ('c0','c2','clock-derivative','RV','forward-a','forward-b','ordinary-pair') else 11
    # Those named guards all lie in the lower quartic clock layer.
    n=cap*baseMod.degree()
    log('rank guard',args.rank_guard,len(basis0),gg,ee,'needed',n)
    assert ee>=n
if args.trace_guards:
    assert not args.verify_over
    for name,e in live_guards().items():
        while isinstance(e,E):e=norm(e)
        s=monic_f(e.f)
        s=s//s.gcd(s.derivative())
        log('guard',name,s.degree())
        save('G-'+name,s)
else:
    vals={'reverse':Rg,'forward':Fg}
    if args.chart in ('quintic','all'):vals['quintic']=Qg
    if args.rank_guard:
        guard_rank(guard,list(vals.values()))
    else:
        gb=[]
        for name,h in vals.items():
            if args.chart not in (name,'all'):continue
            gb.append(monic_kernel(name,h))
        if len(gb)>1:
            g=gb[0]
            for f in gb[1:]:g=g.gcd(f)
            log('joint degree',g.degree())
            if p:log('factor degrees',[(f.degree(),k)for f,k in g.factor()[1]])
    if args.write and not args.verify_over:
        (args.write/'ledger.txt').write_text('\n'.join(n+' '+ ' '.join(map(str,d.coeffs()))for n,d in ledger)+'\n')

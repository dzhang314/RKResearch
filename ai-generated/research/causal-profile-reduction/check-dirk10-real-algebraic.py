#!/usr/bin/env python3
"""Exact algebraic construction and complete rooted replay of an 11-stage DIRK10.
Uses only Python's standard library. No other tableau is imported.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import cache
from math import prod


@dataclass(frozen=True)
class E:
    alg: object
    c: tuple

    def __bool__(s):
        return bool(s.c)

    def __add__(s, a):
        a = s.alg.cast(a)
        if not s:
            return a
        if not a:
            return s
        return E(s.alg, tuple(add(s.c, a.c)))

    __radd__ = __add__

    def __neg__(s):
        return E(s.alg, tuple(-x for x in s.c))

    def __sub__(s, a):
        return s + (-s.alg.cast(a))

    def __rsub__(s, a):
        return s.alg.cast(a) + (-s)

    def __mul__(s, a):
        a = s.alg.cast(a)
        if not s or not a:
            return s.alg.zero
        if len(s.c) == 1:
            return E(s.alg, tuple(scale(a.c, s.c[0])))
        if len(a.c) == 1:
            return E(s.alg, tuple(scale(s.c, a.c[0])))
        return E(s.alg, tuple(red(mul(s.c, a.c), s.alg.mod)))

    __rmul__ = __mul__

    def __truediv__(s, a):
        return s * s.alg.inverse(s.alg.cast(a))

    def __rtruediv__(s, a):
        return s.alg.cast(a) / s

    def __pow__(s, k):
        if k < 0:
            return s.alg.inverse(s)**(-k)
        a = s.alg.one
        while k:
            if k & 1:
                a *= s
            k //= 2
            if k:
                s *= s
        return a


def trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a


def add(a, b):
    if len(a) < len(b):
        a, b = b, a
    return trim([x+y for x,y in zip(a, b)]+list(a[len(b):]))


def sub(a, b):
    return add(a, [-x for x in b])


def scale(a, b):
    return trim([x*b for x in a]) if b else []


def mul(a, b):
    if not a or not b:
        return []
    v = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    v[i+j] = v[i+j] + x*y
    return trim(v)


def red(a, monic):
    b = trim(a)
    n = len(monic)-1
    while len(b)>n:
        c = b.pop()
        j = len(b)-n
        if c:
            for k, d in enumerate(monic[:-1]):
                if d:
                    b[j+k] = b[j+k] - c*d
        b=trim(b)
    return b


def divrem(a, b):
    a = trim(a)
    assert b
    q = [0]*max(0,len(a)-len(b)+1)
    iv = 1/b[-1] if isinstance(b[-1], E) else 1/Q(b[-1])
    while len(a)>=len(b):
        j=len(a)-len(b)
        t=a[-1]*iv
        q[j]=t
        for k,c in enumerate(b):
            if c:
                a[k+j]=a[k+j]-c*t
        a=trim(a)
    return trim(q),a


def ev(a, x):
    v=0
    for c in reversed(a):
        v=c+x*v
    return v


def integral(a):
    return [0]+[v/Q(i+1) for i,v in enumerate(a)]


class Alg:
    def __init__(self, base, mod, name):
        self.base=base
        self.name=name
        self.mod=tuple(self.down(v) for v in mod)
        assert self.mod[-1] == self.down(1)
        self.zero=E(self,())
        self.one=E(self,(self.down(1),))
        self.gen=E(self,(self.down(0),self.down(1)))

    def down(self, x):
        return self.base.cast(x) if self.base else Q(x)

    def cast(self, x):
        if isinstance(x,E) and self is x.alg:
            return x
        v=self.down(x)
        return E(self,(v,)) if v else self.zero

    @cache
    def inverse(self, a):
        assert a, ("zero inverse",self.name)
        if len(a.c)==1:
            return E(self,(1/a.c[0],))
        x,y=list(self.mod),list(a.c)
        u,v=[],[self.down(1)]
        while y:
            q,z=divrem(x,y)
            x,y=y,z
            u,v=v,sub(u,mul(q,v))
        assert len(x)==1, ("not a unit",self.name,a)
        b=E(self,tuple(red(scale(u,1/x[0]),self.mod)))
        assert a*b==self.one
        return b


# A second independent coefficient audit: multiply the two full polynomials
# and test the stated decomposition at rational inputs, including origin.
a,b,u,xi=Q(1,10),Q(3,10),Q(3,5),Q(2)
s,t=Q(2,5),Q(2,3)
p=a*b
Phi=[Q(x)for x in [1,-14,56,-84,42]]
H=[0]+Phi
PP=mul([0,Q(1)],mul([-a,Q(1)],[-b,Q(1)]))
J=integral(PP)
D=mul([-u,Q(1)],PP)
r,c,e,f=Q(-500,9),Q(2044,15),Q(17264,75),Q(-5656,15)
assert H==add(mul([r,c],D),mul([e,f],J))
assert a+b==s and s/u==t and p==s*s/(6-t)
from random import Random
rng=Random(419)
for _ in range(32):
    x=Q(rng.randint(-97,97),rng.randint(1,37))
    assert ev(H,x)==(r+c*x)*(x-u)*x*(x-a)*(x-b)+(e+f*x)*(x**4/4-s*x**3/3+p*x*x/2)

B,N,EE=t/(10*(3-2*t)),s/(5*(3-2*t)),(3-4*t)/(5*(3-2*t))
assert integral(J)==add(add(scale([0]+D,B),scale(J,N)),scale([0]+J,EE))
K=Alg(None,[Q(1314,125),Q(-87,125),Q(-4,5),Q(1)],'k')
k=K.gen
S=1+(k-1)*EE
LL=k*(k-1)*B-S
yn,yd=e-r*k,c*k-f
wn,wd=r*LL,c*S-(k-1)*B*f
assert not (yd*(-u+(k-1)*N)+(r*k-e)*LL)
y,w=yn/yd,wn/wd
assert y and w and y!=w
Q4inv=[[300,-2100,4200,-2520],[-2100,16800,-36120,22680],
       [4200,-36120,81480,-52920],[-2520,22680,-52920,35280]]
mom=[(6-3*t)*(6-t)*(3-t),2*s*(6-t)*(3-t),3*s*s*(6-t),12*s**3]
Q4=mul([Q(1),Q(-1)],[sum(x*z for x,z in zip(q,mom))for q in Q4inv])
M=[e,f]
MyQ=mul(M,Q4)
Ly,Lw=-ev(MyQ,y)/ev(Phi,y),-ev(MyQ,w)/ev(Phi,w)
l1=(Ly-Lw)/(y-w)
l0=Ly-l1*y
nod5=add(MyQ,mul(Phi,[l0,l1]))
SUF,remainder=divrem(nod5,mul([-y,K.one],[-w,K.one]))
assert len(SUF)==4 and not remainder
SUF=[q/SUF[-1]for q in SUF]
T=Alg(K,SUF,'suffix low root')
lo=T.gen
QR,rem=divrem([T.cast(q) for q in SUF],[-lo,T.one])
assert len(QR)==3 and not rem
V=Alg(T,QR,'suffix middle root')
mi=V.gen
lo=V.cast(lo)
hi=-V.cast(SUF[2])-lo-mi
assert not ev([V.cast(q)for q in SUF],hi)


@dataclass(frozen=True)
class It:
    a: Q
    b: Q

    def __add__(s,t):
        t=t if isinstance(t,It) else It(Q(t),Q(t))
        return It(s.a+t.a,s.b+t.b)
    __radd__=__add__

    def __neg__(s):
        return It(-s.b,-s.a)

    def __sub__(s,t):
        t=t if isinstance(t,It) else It(Q(t),Q(t))
        return s+-t

    def __mul__(s,t):
        t=t if isinstance(t,It) else It(Q(t),Q(t))
        q=(s.a*t.a,s.a*t.b,s.b*t.a,s.b*t.b)
        return It(min(q),max(q))
    __rmul__=__mul__

    def sign(s):
        return 1 if s.a>0 else -1 if s.b<0 else 0


def it_eval(expr):
    if isinstance(expr,E):
        x=ki if expr.alg is K else (ilo if expr.alg is T else imi)
        return ev([it_eval(v)for v in expr.c],x)
    return It(Q(expr),Q(expr))


# Exact and separate real specialization. Refine the k bracket before
# checking signs of the suffix cubic with interval rational arithmetic.
kl,kr=Q(-204748,10**5),Q(-204747,10**5)
pol=[1314,-87,-100,125]
assert ev(pol,kl)<0<ev(pol,kr)
for _ in range(145):
    mid=(kl+kr)/2
    if ev(pol,mid)>0:
        kr=mid
    else:
        kl=mid
ki=It(kl,kr)
assert it_eval(y).a>Q(1187,1000) and it_eval(y).b<Q(1188,1000)
assert it_eval(w).a>Q(473,1000) and it_eval(w).b<Q(475,1000)
ilo=It(Q(6377,10**4),Q(6380,10**4))
imi=It(Q(8664,10**4),Q(8668,10**4))
ihi=It(Q(10154,10**4),Q(10159,10**4))
for box in [ilo,imi,ihi]:
    coeff=[it_eval(q) for q in SUF]
    assert ev(coeff,box.a).sign()*ev(coeff,box.b).sign()==-1
# Three disjoint sign-change intervals exhaust the monic cubic, so the
# high root is its trace minus the first two. Distinct from the other
# physical clocks (and from each of their own denominator factors).
assert ilo.b<imi.a and imi.b<ihi.a
print('exact real isolating intervals and degree<=18 quotient construction PASS',flush=True)


def polynomials_on_layout():
    cv=[0,xi,a,b,u,y,w,lo,mi,hi,1]
    cv=[V.cast(v) for v in cv]
    digits=[0,2,3,4,5,6,7,8,9]
    derivative={i:prod(cv[i]-cv[j] for j in digits if j!=i) for i in digits}
    bs={i:ev(M,cv[i])**2/(ev(Phi,cv[i])*derivative[i]) for i in digits}
    rho=Q(14,15)/sum(bs.values())
    beta=[V.zero]*11
    for i in digits:
        beta[i]=rho*bs[i]
    beta[0]+=Q(1,30)
    beta[-1]=V.cast(Q(1,30))
    for j in range(10):
        assert sum(beta[i]*cv[i]**j for i in range(11))==V.cast(Q(1,j+1))
    gamma=xi**3/6
    kap=xi**2/(3*(a-xi)*(2*b-a))
    g=[V.zero]*11
    h=[V.zero]*11
    g[1]=V.cast(gamma)
    for i in range(2,10):
        h[i]=kap*ev(H,cv[i])/ev(M,cv[i])
    gnorm=beta[9]*(1-cv[9])**3*derivative[9]/(6*ev(M,cv[9]))
    G=[V.zero]*11
    for i in digits:
        G[i]=gnorm*ev(M,cv[i])/derivative[i]
    return cv,beta,g,h,G


def solve_tableau(cv, beta, g, h, G):
    ch=[a*b for a,b in zip(cv,h)]
    cch=[a*b for a,b in zip(cv,ch)]
    Tc=[ev(integral(H),a) for a in cv]
    f6=[g,h,ch,cch,Tc]
    lin={(i,j):k for k,(i,j) in enumerate((i,j) for i in range(11) for j in range(i+1)
         if not(i==j and i in (0,4,6,10)))}
    n=len(lin)
    piv={}
    rank={}
    def feed(row,rhs,name):
        row={i:V.cast(v) for i,v in row.items() if v}
        rhs=V.cast(rhs)
        while row:
            j=min(row)
            v=row[j]
            if j not in piv:
                iv=1/v
                piv[j]=({i:q*iv for i,q in row.items() if i!=j},rhs*iv)
                rank[name]=rank.get(name,0)+1
                return
            rr,tr=piv[j]
            del row[j]
            rhs-=v*tr
            for i,q in rr.items():
                u=row.get(i,V.zero)-v*q
                if u: row[i]=u
                elif i in row:del row[i]
        assert not rhs, ("inconsistent actual order block",name)
    def fwd(f,rhs,z,name):
        nonlocal n
        m=n; n+=len(z)
        for i in range(11):
            row={ind:f[j] for (a,j),ind in lin.items() if a==i}
            row.update({m+k:-v[i] for k,v in enumerate(z)})
            feed(row,rhs[i],name)
        print('linear block',name,'rank contribution',rank.get(name,0),flush=True)
    def back(f,rhs,name):
        for j in range(11):
            feed({ind:f[i] for (i,a),ind in lin.items()if a==j},rhs[j],name)
        print('linear block',name,'rank contribution',rank.get(name,0),flush=True)
    for j in (0,1,2):
        fwd([x**j for x in cv],[x**(j+1)/(j+1)+(g[i] if j==2 else 0)
             for i,x in enumerate(cv)],[],['A1','Ac','Ac2'][j])
    fwd(g,[x*xi/2+y for x,y in zip(g,h)],[],'Ag')
    fwd([x**3 for x in cv],[x**4/4 for x in cv],[g,h],'Ac3')
    fwd([x**4 for x in cv],[x**5/5 for x in cv],[g,h,ch],'Ac4')
    fwd(h,[0]*11,[h,ch],'Ah')
    fwd(ch,[0]*11,f6,'ACh')
    fwd([x**5 for x in cv],[x**6/6 for x in cv],f6,'Ac5')
    Y=[1-x for x in cv]
    for j in range(3):
        back([b*y**j for b,y in zip(beta,Y)],[b*y**(j+1)/(j+1)+(v if j==2 else 0)
             for b,y,v in zip(beta,Y,G)],['D1','D2','G'][j])
    assert n==len(piv)
    rhs=[V.zero]*n
    for j in reversed(sorted(piv)):
        row,val=piv[j]
        rhs[j]=val-sum(u*rhs[i] for i,u in row.items())
    return [[rhs[lin[i,j]]if (i,j) in lin else V.zero for j in range(i+1)]for i in range(11)]


def all_rooted(A,beta,through=10):
    # Generate unordered forests only; every branch list is sorted.
    @cache
    def size(t):
        return 1+sum(size(x)for x in t)
    @cache
    def dens(t):
        return size(t)*prod(dens(x)for x in t)
    T=[[],[()]]
    for n in range(2,through+1):
        childhood=[q for j in range(1,n) for q in T[j]]
        def allForests(m,lo):
            if not m:
                yield ()
            else:
                for i in range(lo,len(childhood)):
                    c=childhood[i];j=size(c)
                    if j>m: break
                    for d in allForests(m-j,i):
                        yield (c,)+d
        T.append(list(allForests(n-1,0)))
    @cache
    def prim(t):
        g=phi(t)
        return tuple(sum(u*v for u,v in zip(r,g)) for r in A)
    @cache
    def phi(t):
        a=[V.one]*11
        for q in t:
            a=[u*v for u,v in zip(a,prim(q))]
        return tuple(a)
    counts=[]
    for n in range(1,through+1):
        for t in T[n]:
            val=sum(z*v for z,v in zip(beta,phi(t)))
            assert dens(t)*val==V.one,("rooted order failure", n,t)
        counts.append(len(T[n]))
        print('verified all rooted trees of size',n,':',len(T[n]),flush=True)
    return counts


def main():
    cv,beta,g,h,G=polynomials_on_layout()
    print('exact ordinary quadrature PASS',flush=True)
    A=solve_tableau(cv,beta,g,h,G)
    assert all(sum(r)==v for r,v in zip(A,cv))
    print('exact actual tableau solved',flush=True)
    m11=11*sum(z*x**10 for z,x in zip(beta,cv))-1
    # A verified inverse is stronger than nonzero tensor coordinates:
    # it survives every real specialization, even if a quotient factors.
    assert m11*(1/m11)==V.one
    print('eleven-vertex star failure: exact unit witness',flush=True)
    assert all_rooted(A,beta)==[1,1,2,4,9,20,48,115,286,719]
    print('all 1205 literal rooted equations PASS over the exact real algebraic tableau',flush=True)


if __name__=='__main__':
    main()

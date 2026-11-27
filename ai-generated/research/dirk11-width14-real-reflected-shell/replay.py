#!/usr/bin/env python3
"""Exact real algebraic DIRK11 shell and all-rooted replay (stdlib only)."""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import cache
from math import prod
from itertools import chain


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

# Scalar geometry. All divisions below have checked inverses in the
# monic quotient tower, before any choice of real embedding.
def dot(x,y):
    z=next((a.alg.zero for a in chain(x,y) if isinstance(a,E)),0)
    return sum((a*b for a,b in zip(x,y) if a and b),z)

def smul(a,v):return [a*x for x in v]
def vsum(u,v):return [a+b for a,b in zip(u,v)]
def powers(x,n):return [x**j for j in range(n)]
def primitive(x,n,k=0):return [x**(j+1+k)/Q(j+1+k)for j in range(n)]
def evalrow(nodes,n):return list(zip(*[powers(x,n)for x in nodes]))
def basis(j,n):return [int(i==j)for i in range(n)]

def solve(M,rhs):
    n=len(rhs);assert n==len(M)==len(M[0])
    A=[list(r)+[x]for r,x in zip(M,rhs)]
    for j in range(n):
        k=next(k for k in range(j,n)if A[k][j])
        A[j],A[k]=A[k],A[j]
        v=1/A[j][j]
        A[j][j:]=[a*v for a in A[j][j:]]
        for k in range(n):
            if k==j or not A[k][j]:continue
            w=A[k][j];A[k][j:]=[x-w*y for x,y in zip(A[k][j:],A[j][j:])]
    out=[r[-1]for r in A]
    assert [dot(row,out)for row in M]==list(rhs)
    return out

@dataclass(frozen=True)
class Box:
    lo: Q
    hi: Q
    def __add__(self,other):
        if not isinstance(other,Box):other=Box(Q(other),Q(other))
        return Box(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return Box(-self.hi,-self.lo)
    def __sub__(self,other):return self+-other
    def __rsub__(self,other):return -self+other
    def __mul__(self,other):
        if not isinstance(other,Box):other=Box(Q(other),Q(other))
        c=(self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi)
        return Box(min(c),max(c))
    __rmul__=__mul__
    def sign(self):return 1 if self.lo>0 else -1 if self.hi<0 else 0

def rootbounds(x,steps=128):
    assert x>0
    l,r=Q(0),max(Q(1),x)
    for _ in range(steps):
        m=(l+r)/2
        if m*m<x:l=m
        else:r=m
    assert l*l<x<=r*r
    return l,r

def iso(t):
    l,_=rootbounds(t.lo);_,r=rootbounds(t.hi)
    return Box(l,r)

R=Alg(None,[Q(-15),Q(0),Q(1)],'positive sqrt(15)')
r=R.gen
U=Alg(R,[-(15+2*r)/33,0,1],'positive larger centered root')
V=Alg(U,[-(15-2*U.cast(r))/33,0,1],'positive smaller centered root')
Z,O=V.zero,V.one
a=O/2
b=(O+V.cast(U.gen))/2
d=(O+V.gen)/2
e,f=O-d,O-b
grid=[Z,a,b,d,e,f,O]
w=solve(evalrow(grid,7),primitive(O,7))
assert all(w)
assert [dot(w,[x**k for x in grid])for k in range(12)]==[O/Q(k+1)for k in range(12)]
ga=a**3/6

# Pure size-six prefix residuals are in span(e0,e1). The basis is computed
# from the polynomial lift of exact monomial values and its second moment
# coordinate, not fitted to any approximate tree residual.
P=[powers(Z,5),powers(b,5),primitive(b,5),primitive(b,5,1),powers(e,5)]
Q0=solve(P,[Z,b**5,b**6/6,b**7/7,e**5])
Q1=solve(P,[Z,Z,Z,O,Z])
evalerr=lambda x:[x**5-ev(Q0,x),ev(Q1,x)]
aa,bb=solve(list(zip(evalerr(1-a),evalerr(1-b))),evalerr(1-e))
lam=2*w[4]*aa/w[1];mu=2*w[4]*bb/w[2]

D5=evalrow(grid[:5],5)
Wa=solve(D5,vsum(primitive(a,5),[Z,Z,-ga,-3*a*ga/2,Z]))
We=solve(D5,primitive(e,5))
N=[1/prod(x-y for y in grid[:5]if y!=x)for x in grid[:5]]
assert [dot(N,z)for z in D5]==[Z,Z,Z,Z,O]
Ma=3*a**5/10
Ka=a*a*ga/2
R5=[wa-Ma*n+lam*we for wa,n,we in zip(Wa,N,We)]
tau=-(b-a)*R5[2]/((d-a)*R5[3])
assert tau

# The third dirty row d fits the four primitive moments with one
# affine cubic compensator. After gd=tau*gb, both its row and g-vector
# are affine in gb; their product yields the following exact quadratic.
Vb=evalrow(grid[:3],3)
Wb=solve(Vb,primitive(b,3))
Db=solve(Vb,[Z,Z,O])
hd0=dot(Wb,[y**3 for y in grid[:3]])-b**4/4
hd1=dot(Db,[y**3 for y in grid[:3]])
kc0=dot(Wb,[Z,ga,Z]);kc1=dot(Db,[Z,ga,Z])+Wb[2];kc2=Db[2]
s=(d-a)/(b-a)
Vd=evalrow(grid[:4],4)
Wd=solve(Vd,primitive(d,4))
S1=solve(Vd,[Z,Z,O,Z]);S2=solve(Vd,[Z,Z,Z,O])
F0=vsum(Wd,smul(tau*s*hd0,S2))
F1=vsum(smul(tau,S1),smul(tau*(3*a/2*(1-s)+s*hd1),S2))
A0=[Z,ga,Z,Z];A1=[Z,Z,O,tau]
qc=[dot(F0,A0)-tau*s*kc0,dot(F0,A1)+dot(F1,A0)-tau*((1-s)*a/2+s*kc1),
    dot(F1,A1)-tau*s*kc2]
assert qc[-1]
W=Alg(V,[qc[0]/qc[2],qc[1]/qc[2],O],'positive smaller gb')
g_b=W.gen

# This real place is established independently by exact rational interval
# arithmetic. Every monic algebra relation is respected at the selected roots.
rho=iso(Box(Q(15),Q(15)))
big=iso((15+2*rho)*Q(1,33))
small=iso((15-2*rho)*Q(1,33))
boxes={R:rho,U:big,V:small}

def enclosure(v):
    if not isinstance(v,E):return Box(Q(v),Q(v))
    return ev([enclosure(x)for x in v.c],boxes[v.alg]) if v else Box(Q(0),Q(0))

l,r=Q(160057,10**6),Q(160058,10**6)
assert enclosure(ev(qc,l)).sign()*enclosure(ev(qc,r)).sign()==-1
boxes[W]=Box(l,r)
assert enclosure(tau).lo>0
print('exact real place: gb in (0.160057,0.160058), quadratic signs opposite',flush=True)

def tableau():
    cw=W.cast
    Z,O=W.zero,W.one
    a,b,d,e,f=map(cw,(globals()['a'],globals()['b'],globals()['d'],globals()['e'],globals()['f']))
    ga,gb,gd=cw(globals()['ga']),g_b,cw(tau)*g_b
    ys=[Z,a,b,d,e,a,b,d,f,O]
    xx=[1-y for y in ys]
    G=[Z,ga,gb,gd,Z,-ga,-gb,-gd,Z,Z]
    ws=[cw(w[j])/Q(2 if j in (1,2,3)else 1)for j in (0,1,2,3,4,1,2,3,5,6)]
    assert all(ws)
    lb=vsum(list(map(cw,Wb)),smul(gb,list(map(cw,Db))))
    hb=dot(lb,[Z,a**3,b**3])-b**4/4
    kb=dot(lb,G[:3])
    h=lambda y:3*a/2+(y-a)/(b-a)*(hb/gb-3*a/2)
    k=lambda y:a/2+(y-a)/(b-a)*(kb/gb-a/2)
    L=[[Z]*10,[a/2,a/2]+[Z]*8,lb+[Z]*7]
    ld=vsum(list(map(cw,F0)),smul(gb,list(map(cw,F1))))
    L.append(ld+[Z]*6)
    GY=[g*y for g,y in zip(G,ys)]
    we=list(map(cw,We));nn=list(map(cw,N))
    me=-dot(we,G[:5])/dot(nn,G[:5])
    le=vsum(we,smul(me,nn))
    L.append(le+[Z]*5)
    qe=dot(le,GY[:5])
    qa=cw(Ka)
    ma=cw(Ma)
    mb=dot(lb,[z**4 for z in ys[:3]])-b**5/5
    qb=dot(lb,GY[:3])
    lm,mm=cw(lam),cw(mu)
    ma2=-ma-lm*me;qa2=-qa-lm*qe
    mb2=-mb-mm*me;qb2=-qb-mm*qe
    C5=evalrow(ys[:6],5)+[G[:6]]
    T5=primitive(ys[5],5);T5[2]+=G[5];T5[3]+=h(ys[5])*G[5];T5[4]+=ma2
    la2=solve(C5,T5+[k(ys[5])*G[5]])
    assert dot(la2,GY[:6])==qa2
    L.append(la2+[Z]*4)
    C6=evalrow(ys[:7],5)+[G[:7],GY[:7]]
    for i in range(6,10):
        y=ys[i]
        target=primitive(y,5)
        target[2]+=G[i];target[3]+=h(y)*G[i]
        if i==6:target[4]+=mb2
        row=solve(C6,target+[k(y)*G[i],qb2 if i==6 else Z])
        L.append(row+[Z]*3)
    assert all(not L[i][j]for i in range(10)for j in range(i+1,10))
    for i,y in enumerate(ys):
        assert [dot(L[i],[z**j for z in ys])for j in range(4)]+[dot(L[i],G)]==[
            y,y*y/2,y**3/3+G[i],y**4/4+h(y)*G[i],k(y)*G[i]]
    for P0 in [Q0,Q1]:
        P0=list(map(cw,P0))
        E0=[x**5-ev(P0,x) if P0==list(map(cw,Q0)) else ev(P0,x)for x in xx]
        assert not dot([a*u for a,u in zip(E0,ws)],
                       [dot(row,[y**4 for y in ys])-y**5/5 for row,y in zip(L,ys)])
        assert not dot([a*u for a,u in zip(E0,ws)],[dot(row,GY)for row in L])
    # Forward order-six donor jet and polynomial lift.
    w0=[Q(11,120),Q(27,40),Q(27,40),Q(-8,15),Q(11,120)]
    A0=[[],[b/6,b/6],[b/6,b/3,b/6],[b/4,Z,Z,b/4],[Z,27*b/22,27*b/22,-16*b/11]]
    A0=[row+[Z]*(7-len(row))for row in A0]
    c0=[sum(row)for row in A0]
    wa=[b*u for u in w0]
    A0.append(wa+[Z,Z])
    P=[powers(Z,5),powers(b,5),primitive(b,5),primitive(b,5,1),powers(e,5)]
    M=list(zip(*P))
    U=[basis(0,7),basis(5,7),wa+[Z,Z],[u*v for u,v in zip(wa,c0)]+[Z,Z],basis(6,7)]
    # Evaluate all rows by one coefficient solve, not one per coordinate.
    def lift(F):
        c=solve(M,F)
        return [dot(c,u)for u in zip(*U)]
    ip=lambda x:lift(primitive(x,5))
    ep=lambda x:lift(powers(x,5))
    A0.append(ip(e))
    T=[[ws[j]*L[j][i]/ws[i]for j in reversed(range(10))]for i in reversed(range(10))]
    Ep=[ep(x)for x in xx[::-1]]
    F=[row+[Z]*10 for row in A0]
    for x,row in zip(xx[::-1],T):
        v=[dot(row,u)for u in zip(*Ep)]
        F.append([a-b for a,b in zip(ip(x),v)]+row)
    B=[Z]*7+ws[::-1]
    for i,j in [(7,0),(8,5),(9,6)]:
        assert F[i]==F[j],(i,j)
        for row in F:row[j]+=row[i]
        B[j]+=B[i]
    keep=[i for i in range(17)if i not in (7,8,9)]
    A=[[F[i][j]for j in keep]for i in keep]
    b=[B[i]for i in keep]
    assert not any(A[i][j]for i in range(14)for j in range(i+1,14))
    assert any(A[i][i]for i in range(14))
    return A,b

def root_replay(A,b):
    def act(v):return tuple(dot(row,v)for row in A)
    one=(W.one,)*14
    # Normalize by the forest factorial. A constructor attaches a
    # weighted child through |child| A; then coordinate multiplication.
    states=[one];actions=[act(one)];degree=[1];indices={():0}
    assert dot(b,one)==W.one
    c=actions[0]
    totals=[1]
    for m in range(2,12):
        cut=len(degree)
        def children(k,i):
            if not k:yield ();return
            for j in range(i,cut):
                if degree[j]>k:break
                for u in children(k-degree[j],j):yield (j,)+u
        for kids in children(m-1,0):
            x,y=states[indices[kids[:-1]]],actions[kids[-1]]
            z=tuple(a*b for a,b in zip(x,y))
            assert m*dot(b,z)==W.one,(m,kids)
            indices[kids]=len(degree);states.append(z);degree.append(m)
            if m<11:actions.append(tuple(m*a for a in act(z)))
        totals.append(len(degree)-cut)
        print('order',m,'shapes',totals[-1],'PASS',flush=True)
    assert totals==[1,1,2,4,9,20,48,115,286,719,1842]
    v=tuple(t**6 for t in c)
    defect=12*7*dot(b,[x**4*y for x,y in zip(c,act(v))])-1
    assert defect
    unit=W.inverse(defect);assert defect*unit==W.one
    print(sum(totals),'rooted conditions;', 'order-12 four leaves plus size-7 bush has verified unit defect',flush=True)
    return defect,unit

if __name__=="__main__":
    import argparse,json
    from pathlib import Path
    cli=argparse.ArgumentParser()
    cli.add_argument("--export",type=Path)
    cli.add_argument("--quick",action="store_true")
    args=cli.parse_args()
    A,b=tableau()
    print("exact tower tableau constructed",flush=True)
    if args.quick:raise SystemExit(0)
    D,I=root_replay(A,b)
    if args.export:
        def serial(v,root):
            if root is None:return str(Q(v))
            x=root.cast(v)
            return [serial(x.c[i]if i<len(x.c)else root.down(0),root.base)
                    for i in range(len(root.mod)-1)]
        order=[R,U,V,W]
        record={"width":14,"order":11,"basis":"ascending nested monic quotients",
                "relations":[[serial(v,root.base)for v in root.mod]for root in order],
                "A":[[serial(x,W)for x in row[:i+1]]for i,row in enumerate(A)],
                "b":[serial(x,W)for x in b],"failure_tree":"root with four leaf children and one size-7 bush",
                "scaled_failure":serial(D,W),"scaled_failure_inverse":serial(I,W)}
        args.export.write_text(json.dumps(record,indent=2)+chr(10))

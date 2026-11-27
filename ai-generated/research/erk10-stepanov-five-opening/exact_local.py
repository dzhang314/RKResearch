#!/usr/bin/env python3
"""Exact radical high-block scopes, top-word ranks, and size-ten classification."""
from functools import cache
from itertools import combinations, product
from pathlib import Path
from hashlib import md5
from math import prod
import sys
import sympy as sp
xS,yS,zS=sp.sqrt(3),sp.sqrt(7),sp.sqrt(147+42*sp.sqrt(7))
K=sp.QQ.algebraic_field(xS,yS,zS)
x,y,z=map(K.from_sympy,[xS,yS,zS])
Z=K.zero;I=K.one
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Z)
def mat(M,z):return [dot(row,z) for row in M]
def tr(M):return list(map(list,zip(*M)))
def mulrow(u,A):return mat(tr(A),u)
def sub(u,v):return [a-b for a,b in zip(u,v)]
def scale(k,v):return [k*a for a in v]
def solve(A,b):
    n=len(A); R=[x+[y]for x,y in zip(A,b)]
    for j in range(n):
        k=next(i for i in range(j,n)if R[i][j])
        R[j],R[k]=R[k],R[j]
        v=R[j][j];R[j]=[u/v for u in R[j]]
        for i in range(n):
            if i==j:continue
            u=R[i][j];R[i]=sub(R[i],scale(u,R[j]))
    return [q[-1]for q in R]
def source(path):
    f=Path(path).read_bytes()
    assert md5(f).hexdigest()=='be9e5e3ba1ff8ed21124ad285d7d2fd5'
    lines=[list(map(int,s.split()))for s in f.splitlines()]
    def decode(r):
        a,b,c,d,e,f,g,h,q=r
        return (63*a*I+63*b*x+63*c*y+63*d*x*y+3*e*z+
                (-2*f+7*h)*x*z+3*g*y*z+(f-2*h)*x*y*z)/(63*q)
    vals=list(map(decode,lines));c,b=vals[:15],vals[15:30]
    A=[vals[30+i*(i-1)//2:30+i*(i+1)//2]+[Z]*(15-i)for i in range(15)]
    assert mat(A,[I]*15)==c
    return c,b,A
def powers(s,n):return [s**j for j in range(n)]
def high(path):
    c,b,A=source(path)
    B=[a[6:]for a in A[6:]]
    c,b=c[6:],b[6:]
    E=[[a**n for a in c]for n in range(7)]
    W=[[u*v for u,v in zip(b,e)]for e in E]
    D=[sub(mulrow(W[j],B),[u*(I-v)/(j+1)for u,v in zip(b,E[j+1])]) for j in range(5)]
    pairs=((0,6),(1,7),(2,3),(4,5),(8,))
    summ=lambda w:[sum((w[j]for j in J),Z)for J in pairs]
    assert not any(D[0]) and not any(summ(D[1]))
    d1=D[1];d1c=[u*v for u,v in zip(d1,c)];d1cc=[u*v for u,v in zip(d1,E[2])]
    for target,base in [
        (D[2],[d1,d1c]),(mulrow(d1,B),[d1,d1c]),
        (D[3],[d1,d1c,d1cc]),(mulrow(d1c,B),[d1,d1c,d1cc])]:
        k=len(base)
        assert all(d1[j] for j in (0,1,2,4))
        idx=(0,1,2,4)[:k]
        cs=solve([tr(base)[j]for j in idx],[target[j]for j in idx])
        assert mat(tr(base),cs)==target
    lam=mulrow(d1cc,B); q=summ(lam)
    k=next(i for i,v in enumerate(q)if v)
    eta=summ(D[4])[k]/q[k]
    assert summ(D[4])==scale(eta,q)
    H=W[:4]+[d1,d1c,sub(W[4],scale(eta,d1cc))]
    u=[Z,I]+solve([s[2:]for s in H],[-s[1]for s in H])
    assert not any(mat(H,u))
    M=tr([sub(scale(I/(k+1),E[k+1]),mat(B,E[k]))for k in range(1,4)])
    coef=solve([r[:2]for r in M[:2]],[-r[2]for r in M[:2]])+[I]
    assert not any(mat(M,coef))
    d=solve([M[0][:2],M[1][:2]],u[:2])
    assert mat([r[:2]for r in M],d)==u
    print('Exact high-block cubic kernel at published a87; same rank-at-most-two affine pencil certified (U in image).')
    return B,c,b,d1,lam,M,coef,eta

def twocoeff(B,c,b,L):
    pairs=((0,6),(1,7),(2,3),(4,5),(8,))
    S=lambda w:[sum((w[j]for j in J),Z)for J in pairs]
    LL=S(L);i=next(j for j,l in enumerate(LL)if l)
    coeff={}
    for W in product('bc',repeat=4):
        v=b[:];p=[I]
        for e in W+('b',):
            if e=='c':
                v=[a*x for a,x in zip(v,c)]
                p=[Z]+p
            else:
                v=mulrow(v,B)
                V=[a/(j+1)for j,a in enumerate(p)]
                p=[sum(V,Z)]+[-a for a in V]
        F=mat([powers(x,len(p))for x in c],p)
        ERR=S(sub(v,[a*x for a,x in zip(b,F)]))
        k=ERR[i]/LL[i];assert ERR==scale(k,LL),(W,ERR,LL)
        coeff[''.join(W)]=k
    print('Top word support: ',[w for w,v in coeff.items()if v])
    return coeff

@cache
def trees(n):
    if n==1:return ((),)
    pool=tuple((j,t)for j in range(1,n)for t in trees(j))
    def rec(left,k):
        if left==0:yield ();return
        for i in range(k,len(pool)):
            j,t=pool[i]
            if j>left:break
            for s in rec(left-j,i):yield (t,)+s
    return tuple(rec(n-1,0))
@cache
def size(t):return 1+sum(size(x)for x in t)
def top(t,W=''):
    large=[z for z in t if size(z)>=5]
    if not large:return
    assert len(large)==1
    big=large[0]
    context='c'*(size(t)-1-size(big))
    if size(big)==5:
        assert len(W+context)==4
        return W+context,big
    return top(big,W+context+'b')
def show(t):return '('+''.join(map(show,t))+')'

class Q:
    """A checked quadratic extension by the exact donor-clock discriminant."""
    D=None
    def __init__(self,a=0,b=0):
        self.a=a*I if isinstance(a,int) else a
        self.b=b*I if isinstance(b,int) else b
    def __add__(self,x):
        if not isinstance(x,Q):x=Q(x)
        return Q(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self):return Q(-self.a,-self.b)
    def __sub__(self,x):return self+-x
    def __rsub__(self,x):return -self+x
    def __mul__(self,x):
        if not isinstance(x,Q):x=Q(x)
        return Q(self.a*x.a+self.b*x.b*Q.D,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def norm(self):return self.a*self.a-self.b*self.b*Q.D
    def __truediv__(self,x):
        if not isinstance(x,Q):x=Q(x)
        d=x.norm()
        assert bool(d)
        return self*Q(x.a/d,-x.b/d)
    def __pow__(self,n):
        if n==0:return Q(1)
        if n==1:return self
        r=self**(n//2)
        return r*r*(self if n%2 else 1)

def positive_dyadic(box):
    from fractions import Fraction as Fr
    from math import isqrt
    unit=1<<240
    def sq(lo,hi):
        q=lambda w:isqrt((unit*unit*w.numerator)//w.denominator)
        return Fr(q(lo),unit),Fr(q(hi)+1,unit)
    def plus(a,b):return a[0]+b[0],a[1]+b[1]
    def prod(a,b):
        x=[u*v for u in a for v in b]
        return min(x),max(x)
    x=sq(Fr(3),Fr(3));y=sq(Fr(7),Fr(7))
    z=sq(147+42*y[0],147+42*y[1]); t=plus(plus(x,y),z)
    assert str(K.ext)=='sqrt(3) + sqrt(7) + sqrt(42*sqrt(7) + 147)'
    def ev(f):
        r=(Fr(0),Fr(0))
        for c in f.to_list():
            c=Fr(int(c.numerator),int(c.denominator))
            r=plus(prod(r,t),(c,c))
        return r
    a,b=box
    up,down=ev(-b),ev(Q.D)
    assert down[0]>0 and ev(a)[0]>0 and up[0]>0
    rr=sq(*down)
    l=(up[0]-rr[1])/2,(up[1]-rr[0])/2
    h=(up[0]+rr[0])/2,(up[1]+rr[1])/2
    assert Fr(22,100)<l[0]<l[1]<Fr(23,100)
    assert Fr(53,100)<h[0]<h[1]<Fr(54,100)
    print('Two positive separated exact donor clocks in (22/100,23/100),(53/100,54/100).')

def sources(c,L,co):
    Q.D=co[1]**2-4*co[0]
    positive_dyadic(co[:2])
    p=Q(-co[1]/2,-I/2);q=Q(-co[1]/2,I/2)
    c2=Q(I*2/15);a=2*p/3
    A=[[Q(0) for _ in range(5)]for _ in range(5)]
    A[1][0]=c2
    A[2][1]=a**2/(2*c2);A[2][0]=a-A[2][1]
    A[3][2]=3*p/4;A[3][0]=p-A[3][2]
    A[4][2]=3*q**2*(3*p-2*q)/(4*p*p)
    A[4][3]=(q*q/2-A[4][2]*a)/p
    A[4][0]=q-A[4][2]-A[4][3]
    @cache
    def phi(t):
        if not t: return [Q(1)]*5
        return [prod((branch[i]for branch in map(primitive,t)),start=Q(1))for i in range(5)]
    @cache
    def primitive(t):
        f=phi(t)
        return [sum(a*b for a,b in zip(x,f))for x in A]
    @cache
    def fac(t):
        return size(t)*prod(fac(q)for q in t)
    v=[Q(dot(L,[u**j for u in c])) for j in range(5)]
    ap=(v[2]-q*v[1])/(p*(p-q))
    aq=(v[2]-p*v[1])/(q*(q-p))
    assert bool((v[3]+v[2]*co[1]+v[1]*co[0]).norm()) is False
    nonzero=[]
    for t in trees(5):
        F=phi(t)
        e=5*v[4]/fac(t)-ap*F[3]-aq*F[4]
        assert e.norm()
        nonzero.append(show(t))
    print('All nine size-five generator values nonzero in both real donor orientations (exact quadratic norms).')
    return p,q,A
def emit(path,B,c,b,p,q,A):
    import json
    v=[sub(scale(I/(j+1),[x**(j+1)for x in c]),mat(B,[x**j for x in c]))
       for j in range(4)]
    def encode(x):
        def as_list(y):
            return [[int(q.numerator),int(q.denominator)]for q in y.to_list()]
        return [as_list(x.a),as_list(x.b)]
    answer=[z+[Q(0)]*9 for z in A]
    for i in range(9):
        w0,w1,w2,w3=(Q(v[j][i])for j in range(4))
        P=(w2-q*w1)/(p*(p-q));R=(w2-p*w1)/(q*(q-p))
        eq=P*p**3+R*q**3-w3
        assert not eq.a and not eq.b
        answer.append([w0-P-R,Q(0),Q(0),P,R]+list(map(Q,B[i])))
    weight=[Q(I/30),Q(0),Q(0),Q(0),Q(0)]+list(map(Q,b))
    out=dict(
        field='a(T)+sqrt(discriminant(T))*b(T); T=sqrt(3)+sqrt(7)+sqrt(147+42*sqrt(7))',
        encoding='descending rational coefficients, entries are [a,b]',
        discriminant=encode(Q(Q.D))[0],
        A=[[encode(x)for x in r[:i]]for i,r in enumerate(answer)],
        b=[encode(x)for x in weight])
    with open(path,'w') as f:json.dump(out,f,indent=None,separators=(',',':'));f.write(chr(10))


def main():
    B,c,b,d1,L,M,co,eta=high(sys.argv[1])
    import collections
    W=twocoeff(B,c,b,L)
    p,q,A=sources(c,L,co)
    if len(sys.argv)>2:emit(sys.argv[2],B,c,b,p,q,A)
    need=collections.Counter()
    for t in trees(10):
        z=top(t)
        if z and W[z[0]]:
            need[show(z[1])]+=1
    print('Exact counts by size-five source before the three generator checks:',sorted(need.items()))
    print('Potential nonzero:',sum(need.values()))
    print('cubic kernel',*[K.to_sympy(a).evalf(20)for a in co])
if __name__=='__main__':main()

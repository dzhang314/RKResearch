#!/usr/bin/env python3
"""Exact rational checks for the derivative root and scalar sharpness proofs."""
from fractions import Fraction as Q
from math import ceil, comb, factorial


def trim(v):
    v=list(map(Q,v))
    while v and not v[-1]:
        v.pop()
    return tuple(v)


def plus(a,b):
    return trim((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                for i in range(max(len(a),len(b))))


def scale(a,c):
    return trim(x*c for x in a)


def mult(a,b):
    if not a or not b:
        return ()
    v=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            v[i+j]+=x*y
    return trim(v)


def deriv(a):
    return trim(i*a[i] for i in range(1,len(a)))


def ev(a,x):
    y=Q(0)
    for v in reversed(a):
        y=y*x+v
    return y


def quo_rem(a,b):
    assert b
    q=[Q(0)]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b):
        j=len(a)-len(b)
        c=a[-1]/b[-1]
        q[j]=c
        a=plus(a,(Q(0),)*j+scale(b,-c))
    return trim(q),a


def gcd(a,b):
    while b:
        a,b=b,quo_rem(a,b)[1]
    return scale(a,1/a[-1]) if a else ()


def sgn(a):
    return (a>0)-(a<0)


def variations(stream):
    seq=[x for x in stream if x]
    return sum(a*b<0 for a,b in zip(seq,seq[1:]))


def sturm_open_zero_counts(a):
    """Squarefree polynomial, open half-lines using one-sided zero signs."""
    seq=[a,deriv(a)]
    assert seq[-1]
    while True:
        nxt=scale(quo_rem(seq[-2],seq[-1])[1],-1)
        if not nxt:
            break
        seq.append(nxt)
    assert len(seq[-1])==1
    def endpoint(sign_at):
        return variations(sign_at(f) for f in seq)
    def low(f,side):
        i=next(i for i,c in enumerate(f) if c)
        return sgn(f[i])*side**i
    ni=endpoint(lambda f:sgn(f[-1])*(-1)**(len(f)-1))
    nz=endpoint(lambda f:low(f,-1))
    pz=endpoint(lambda f:low(f,+1))
    pi=endpoint(lambda f:sgn(f[-1]))
    return ni-nz, pz-pi


def real_multiplicities(a):
    neg=zero=pos=0
    while len(a)>1:
        g=gcd(a,deriv(a))
        sf,rem=quo_rem(a,g)
        assert not rem
        n,p=sturm_open_zero_counts(sf)
        neg+=n
        pos+=p
        zero+=int(sf[0]==0)
        a=g
    return neg,zero,pos


def invstep(n,a):
    assert n>=1
    out=()
    for j in range(len(a)):
        out=plus(out,scale(a,(-1)**j*comb(n+j-1,j)))
        a=deriv(a)
    return out


def ecoef(q,n):
    return sum(q[i]/factorial(n-i) for i in range(min(n+1,len(q))))


def score(es):
    return sum(x==0 for x in es)+sum(a*b<0 for a,b in zip(es,es[1:]))


def inverse_family(m,h,k):
    n,r=m+1,h+k
    w=(Q(0),)*k+(Q(1),)
    for i in range(1,h+1):
        w=mult(w,(i,1))
    assert len(w)==r+1
    derivs=[w]
    for _ in range(r):
        derivs.append(deriv(derivs[-1]))
    bound=Q(1)
    for i in range(1,h+1):
        for x in (-i-Q(1,4),-i+Q(1,4)):
            err=sum(comb(n+j-1,j)*abs(ev(derivs[j],x)) for j in range(1,r+1))
            bound=max(bound,2*err/abs(ev(w,x)))
    for a in (1,n):
        g=trim(w[r-i]*(-1)**(r-i)*comb(a+r-i-1,r-i)*factorial(r-i)
               for i in range(r+1))
        assert len(g)==h+1
        bound=max(bound,1+sum(abs(v/g[-1]) for v in g[:-1]))
    M=ceil(bound)+1
    wM=trim(w[j]*M**(r-j) for j in range(r+1))
    U=invstep(n,wM)
    assert U[0]!=0
    pco=trim(ecoef(scale(U,1/U[0]),i) for i in range(m+1))
    q=scale(U,1/U[0])
    for i in range(1,h+1):
        lo,hi=M*(-i-Q(1,4)),M*(-i+Q(1,4))
        assert ev(q,lo)*ev(q,hi)<0
    f=q
    for _ in range(n):
        f=plus(f,deriv(f))
    assert f==scale(wM,1/U[0])
    assert len(pco)==m+1 and len(q)==r+1 and len(gcd(pco,q))==1
    assert real_multiplicities(q)==(h,0,k%2)
    es=[ecoef(q,i) for i in range(m+k+2)]
    assert es[:m+1]==list(pco)
    assert not any(es[m+1:m+k+1]) and es[-1]!=0
    assert score(es[:-1])==k and all(x>0 for x in es[:m+1])
    return q


def local_checks(q,N):
    h,z,p=real_multiplicities(q)
    assert not z and q[0]==1
    u=len(q)-1-h-p
    prev=q
    for j in range(N+1):
        nex=plus(prev,deriv(prev))
        hn,zn,pn=real_multiplicities(prev)
        hn2,zn2,pn2=real_multiplicities(nex)
        assert hn2>=hn and hn2+zn2+pn2>=hn+zn+pn
        if not prev[0]:
            assert hn2>hn and zn2==zn-1
        elif nex[0]*prev[0]<0:
            assert hn2>hn
        assert zn<=u+int(p>0)
        assert prev[0]==factorial(j)*ecoef(q,j)
        prev=nex
    assert score([ecoef(q,j) for j in range(N+1)])<=u+p


cases=0
for m in range(4):
    for h in range(4):
        for k in range(1,6):
            inverse_family(m,h,k)
            cases+=1
print(f'{cases} rational inverse-transform families: exact pole counts, tail lengths, reduction, and tight score')

qs=[]
for a,b,c,d in [(2,0,0,0),(0,2,0,0),(2,2,2,0),(0,0,1,1),(1,1,0,1),(3,1,1,1)]:
    q=(Q(1),)
    for f,n in [((1,1),a),((1,-2),b),((1,0,2),c),((1,-1,1),d)]:
        for _ in range(n):
            q=mult(q,f)
    qs.append(q)
for q in qs:
    local_checks(q,12)
print(f'{len(qs)*13} independent exact Sturm iterations: monotonic root counts, zero-drop, sign charges')

lag=0
for r in range(1,10):
    for n in range(1,10):
        t,alpha=min(r,n),abs(r-n)
        L=trim(Q((-1)**j*comb(t+alpha,t-j),factorial(j)) for j in range(t+1))
        assert real_multiplicities(L)==(0,0,t) and len(gcd(L,deriv(L)))==1
        for k in range(t):
            assert sum(v*factorial(alpha+k+j) for j,v in enumerate(L))==0
        c=Q((-1)**t) if n<=r else Q((-1)**t*factorial(r),factorial(n))
        en=trim(Q((-1)**i*comb(r,i),factorial(n-i)) for i in range(t+1))
        assert en==scale(tuple(reversed(L)),c)
        lag+=1
print(f'{lag} finite one-pole degree pairs: coefficient reversal, exact orthogonality, and positive simple roots')

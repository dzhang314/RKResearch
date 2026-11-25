#!/usr/bin/env python3
"""Standalone exact arithmetic. No packages, compiler, network, or tree imports."""
from fractions import Fraction as F
from math import comb, factorial
from itertools import product


def ceildiv(a,b): return -(-a//b)
def M(p,l): return l*(p+1)//2-l*l//2
def B0(p): return (((p+1)**2//4)+1)//2
def B(p,z): return z+B0(p-2*z) if 2*z<p else (p+1)//2
def S(p): return max(ceildiv(M(p,l)+(l-1)*p,2*l-1) for l in range(1,(p+1)//2+1))

def separated(p):
    k=[1+min(j,p-1-j) for j in range(p)]; totals={}
    def visit(j,l,t):
        totals[l]=max(totals.get(l,0),t)
        for i in range(j,p): visit(i+2,l+1,t+k[i])
    visit(0,0,0)
    return totals

def strip(x):
    x=list(x)
    while x and not x[-1]: x.pop()
    return x

def conv(f,g,q=None):
    if not f or not g: return []
    h=[0]*(len(f)+len(g)-1)
    for i,x in enumerate(f):
        for j,y in enumerate(g): h[i+j]+=x*y
    return strip(h if q is None else [x%q for x in h])

def gcd(f,g,q=None):
    f,g=strip(f),strip(g)
    while g:
        r=f[:]; inv=F(1,g[-1]) if q is None else pow(g[-1],-1,q)
        while len(r)>=len(g):
            i=len(r)-len(g); a=r[-1]*inv
            for j,b in enumerate(g):
                r[i+j]-=a*b
                if q is not None: r[i+j]%=q
            r=strip(r)
        f,g=g,r
    return f

def pade(m,r):
    n=m+r
    return ([F(comb(m,j)*factorial(n-j),factorial(n)) for j in range(m+1)],
            [F((-1)**j*comb(r,j)*factorial(n-j),factorial(n)) for j in range(r+1)])

def scalar_pairs(p):
    for ordered in [False,True]:
        s=max(1,p-1) if ordered else S(p)
        r=p-s; z=s-r
        assert 0<=r<=s and B(p,z)<=s
        P,Q=pade(s,r); h=[F(1,factorial(i)) for i in range(p+2)]
        a=conv(Q,h)
        assert all(a[i]==(P[i] if i<len(P) else 0) for i in range(p+1))
        assert a[p+1]!=0 and len(P)==s+1 and len(Q)==r+1
        assert len(gcd(P,Q))==1
        assert len(gcd(Q,[j*Q[j] for j in range(1,len(Q))]))==1

reviewed=[1,1,2,3,4,5,7,8,10,11,13,15,17,19,21,22,24,25,27,29]
print('p | S_all | ordered | scalar-opt (s,r,z) | char0 reviewed floor s | z_min_at_s | r_max_at_s')
for p in range(1,21):
    totals=separated(p); assert totals[0]==0
    assert all(v==M(p,l) for l,v in totals.items())
    for z in range(p+2):
        assert B(p,z)==max(v-(l-1)*z for l,v in totals.items() if l)
    # Independent joint minimization of degree and physical z across r,z.
    for ordered in [False,True]:
        floor=next(s for s in range(1,p+1) if any(
            p<=r+z+(min(1,r) if ordered else r) and s>=B(p,z)
            for r in range(s+1) for z in range(s-r+1)))
        assert floor==(max(1,p-1) if ordered else S(p))
    scalar_pairs(p)
    s=S(p); t=reviewed[p-1]; z=next(z for z in range(t+1) if B(p,z)<=t)
    assert s<=t and max(1,p-1)<=t
    print(f'{p:2} | {s:2} | {max(1,p-1):2} | ({s},{p-s},{2*s-p}) | {t:2} | {z:2} | {t-z:2}')


def modcheck(Q,q):
    Q=strip(Q); Vdeg=len(Q)-len(gcd(Q,[(i*x)%q for i,x in enumerate(Q) if i],q))
    for p in range(q):
        H=[pow(factorial(i)%q,-1,q) for i in range(p+1)]
        v=strip(conv(Q,H,q)[:p+1]); assert p<=len(v)-1+Vdeg
    return Vdeg

modcases=splitcases=0
for q in [2,3,5,7]:
    for x in product(range(q),repeat=3):
        modcheck([1,*x],q); modcases+=q
    # Separate proof frontier: characteristic-divisible multiplicities yield zero credit.
    for aa in range(1,q):
        for bb in range(1,q):
            for e,f in [(0,q),(1,q),(q,1),(q,q+1),(q+1,2*q),(q+1,q-1)]:
                Q=[1]
                for a,n in [(aa,e),(bb,f)]:
                    for _ in range(n): Q=conv(Q,[1,-a],q)
                mult={aa:e,bb:f} if aa!=bb else {aa:e+f}
                assert modcheck(Q,q)==sum(v%q!=0 for v in mult.values())
                splitcases+=q
print('Finite-field paid-prefix checks (unrestricted normalized degree<=3, designed split multiplicities):',modcases,splitcases)

q=7;s=7
# A=I+L with unit strict subdiagonal. Recovery from seven scalar coefficients.
mom=[1,4,0,0,0,0,1]; Bk=[sum((-1)**(k-n)*comb(k,n)*mom[n] for n in range(k+1))%q for k in range(s)]
b=[(Bk[i]-(Bk[i+1] if i+1<s else 0))%q for i in range(s)]
v=[1]*s; series=[1]
for i in range(4*q):
    series.append(sum(x*y for x,y in zip(b,v))%q)
    v=[(v[j]+(v[j-1] if j else 0))%q for j in range(s)]
Q=[1]+[0]*6+[6]; P=[1,1,4]; assert len(gcd(P,Q,q))==1
assert conv(series,Q,q)[:len(series)]==P+[0]*(len(series)-len(P))
assert series[:4]==[1,1,4,0] and pow(6,-1,7)==6 and modcheck(Q,q)==0
print('Actual order-2 F7 DIRK: A=I+unit subdiagonal, b=',b,'; R=(1+X+4X^2)/(1-X^7); derivative-gcd credit=0 (distinct poles=1); unpaid tall coefficient 0 != 6.')

#!/usr/bin/env python3
"""Rational 15-stage order-nine construction, with exact tree replay."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import prod, lcm
from pathlib import Path
import json

DEFAULT_PREFIX = Path(__file__).parent.parent.parent / (
    "upper-bounds/real-algebraic/erk14-order9-seven-clock/prefix.json"
)


def mul(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j] += x*y
    return out


def hull(xs):
    ans=[F(1)]
    for x in xs:
        ans=mul(ans,[-x,F(1)])
    return ans


def integrate(a,exponent=0):
    return sum(F(q)/(j+exponent+1) for j,q in enumerate(a))


def masses(xs):
    return [integrate(hull([x for j,x in enumerate(xs) if j!=i]))
            / prod(a-x for j,x in enumerate(xs) if j!=i)
            for i,a in enumerate(xs)]


def geometry(x,v,w,z):
    fixed=list(map(F,[0,1,x,x/2,v,w,z]))
    assert len(set(fixed))==7
    P=hull(fixed)
    denom=integrate(P)
    if not denom:
        raise ZeroDivisionError("hull linear coefficient")
    t=integrate(P,1)/denom
    assert t not in fixed
    xs=[*fixed,t]
    ws=masses(xs)
    assert all(ws)
    assert all(sum(q*c**k for q,c in zip(ws,xs))==F(1,k+1) for k in range(9))
    return t,xs,ws


def reverse(x,v,w,z,t,ws,free_h=F(0)):
    # The two x labels share one mass, not a new scalar quadrature site.
    R=[F(1),x,v,w,z,t,x/2,x,F(0)]
    b=[ws[1],ws[2]/2,*ws[4:],ws[3],ws[2]/2,ws[0]]
    y=[1-u for u in R]
    r,V,U=y[1:4]
    u0=-r*r/2
    us=[F(0),u0,0,0,0,0,0,-u0,0]
    L=[[F(0)]*9 for _ in range(9)]
    L[1][0]=r
    L[2][1]=V*V/(2*r)
    L[2][0]=V-L[2][1]
    hv=L[2][1]*u0
    gv=L[2][1]*r*r-V**3/3
    hw=free_h
    L[3][1]=hw/u0
    L[3][2]=(U*U/2-r*L[3][1])/V
    L[3][0]=U-L[3][1]-L[3][2]
    gw=L[3][1]*r*r+L[3][2]*V*V-U**3/3

    def D(u):
        return u*(u-x)*(u-x/2)

    K=[b[i]*D(R[i]) for i in range(2,6)]
    Z=[c*(c-x) for c in (v,w,z,t)]
    assert K[2]*K[3]*(Z[3]-Z[2])
    def endvalues(a,b):
        RHS0=-K[0]*a-K[1]*b
        RHS1=-K[0]*Z[0]*a-K[1]*Z[1]*b
        return ((Z[3]*RHS0-RHS1)/(K[2]*(Z[3]-Z[2])),
                (RHS1-Z[2]*RHS0)/(K[3]*(Z[3]-Z[2])))

    h=(*endvalues(hv,hw),F(0),F(0),F(0))
    g=(*endvalues(gv,gw),F(0),F(0),F(0))
    for i in range(4,9):
        s=y[i]
        L[i][1]=h[i-4]/u0
        rem1=s*s/2+us[i]-L[i][1]*r
        rem2=s**3/3+g[i-4]-L[i][1]*r*r
        L[i][2]=(rem2-U*rem1)/(V*(V-U))
        L[i][3]=(rem2-V*rem1)/(U*(U-V))
        L[i][0]=s-sum(L[i])

    def act(v):
        return [sum(u*w for u,w in zip(row,v)) for row in L]
    assert act([1]*9)==y
    defects=[a-s*s/2 for a,s in zip(act(y),y)]
    assert defects==us
    assert us[1]*b[1]+us[7]*b[7]==0
    assert all(a==0 for a in [sum(b[i]*(act([s*s for s in y])[i]-y[i]**3/3)*D(R[i])*
        (R[i]*(R[i]-x))**j for i in range(9)) for j in (0,1)])
    assert all(a==0 for a in [sum(b[i]*act(us)[i]*D(R[i])*(R[i]*(R[i]-x))**j
        for i in range(9)) for j in (0,1)])
    return R,b,L


def read_prefix(prefix):
    data=json.loads(prefix.read_text())
    return [[[F(q) for q in row] for row in data[k]] for k in ("A","Pi")]


def build(x,v,w,z,A0,Pi,free_h=F(0)):
    t,xs,weights=geometry(x,v,w,z)
    R,d,L=reverse(x,v,w,z,t,weights,free_h)
    N=len(R)
    clocks,b=R[::-1],d[::-1]
    B=[[d[N-1-j]*L[N-1-j][N-1-i]/d[N-1-i] if i>j else F(0)
        for j in range(N)] for i in range(N)]
    loc=[0,7,8,9,10,11,12,13,14]
    full=[[x*c for c in row]+[F(0)]*(15-len(row)) for row in A0]
    for i in range(3,N):
        row=[sum((clocks[i]**(k+1)/(k+1)-sum(B[i][j]*clocks[j]**k
                    for j in range(i)))*Pi[k][col]/x**k for k in range(5))
             for col in range(9)]+[F(0)]*6
        for j in range(i):
            row[loc[j]]+=B[i][j]
        full.append(row)
    padded_b=[F(0)]*15
    for i,q in zip(loc,b):
        padded_b[i]=q
    assert all(sum(full[i])==c for i,c in zip(loc,clocks))
    for i,c in enumerate(clocks[:3]):
        read=[sum(c**(k+1)*Pi[k][j]/((k+1)*x**k) for k in range(5)) for j in range(9)]
        assert read==full[loc[i]][:9],(i,c)
        assert not any(B[i])
    return full,padded_b,t,xs,weights


@lru_cache(None)
def trees(n, lower=(0,())):
    if n==0:
        return ((),)
    return tuple((t,)+s for k in range(max(1,lower[0]),n+1)
                 for t in trees(k-1) if (k,t)>=lower for s in trees(n-k,(k,t)))


@lru_cache(None)
def size(t):
    return 1 + sum(size(s) for s in t)


@lru_cache(None)
def factorial(t):
    return size(t)*prod(factorial(s) for s in t)


def audit(A,b):
    assert len(A)==len(b)==15
    assert all(not any(r[i:]) for i,r in enumerate(A))
    assert len({tuple(r) for r in A})==15
    @lru_cache(None)
    def product(t):
        kids=[action(s) for s in t]
        return tuple(prod(cs[i] for cs in kids) for i in range(15))
    @lru_cache(None)
    def action(t):
        return tuple(sum(c*u for c,u in zip(row,product(t)) if c) for row in A)
    def gap(t):
        return factorial(t)*sum(c*u for c,u in zip(b,product(t)) if c)-1
    print("Rooted conditions through nine by grade:",
          [len(trees(k)) for k in range(9)])
    for k in range(9):
        for t in trees(k):
            assert gap(t)==0,(t,gap(t))
    tall=()
    for _ in range(9): tall=(tall,)
    ht=gap(tall)
    bush=((),)*9
    hb=gap(bush)
    assert ht or hb
    print("Tenth tall and bush residuals:", ht, hb)
    return ht,hb


def main():
    parser=ArgumentParser()
    parser.add_argument("--prefix",default=DEFAULT_PREFIX,type=Path)
    parser.add_argument("--geometry",default=["2/3","1/4","3/4","-1/2"],nargs=4)
    parser.add_argument("--free-h",default="0")
    parser.add_argument("--emit",type=Path)
    args=parser.parse_args()
    g=tuple(map(F,args.geometry))
    A0,Pi=read_prefix(args.prefix)
    A,b,t,xs,w=build(*g,A0,Pi,F(args.free_h))
    print("8 distinct quadrature clocks:",xs)
    print("Quadrature weights:",w)
    print("Common coefficient denominator:",lcm(*(a.denominator for r in A for a in r),*(a.denominator for a in b)))
    ht,hb=audit(A,b)
    if args.emit:
        out={"A":[[str(a) for a in row[:i]] for i,row in enumerate(A)],"b":list(map(str,b)),
             "xi_v_w_z":list(map(str,g)),"last_clock":str(t),"free_h":args.free_h,
             "tenth_tall_defect":str(ht),"tenth_bush_defect":str(hb)}
        args.emit.write_text(json.dumps(out,indent=2)+"\n")

if __name__=="__main__":
    main()

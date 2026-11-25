#!/usr/bin/env python3
"""Exact replay of the prescribed interval-contained seed, not a grid search."""
from collections import Counter
from fractions import Fraction as F
from math import prod


def need(b, msg):
    if not b:
        raise AssertionError(msg)


def nodal(roots):
    p=[F(1)]
    for root in roots:
        q=[F(0)]*(len(p)+1)
        for i,c in enumerate(p):
            q[i]-=root*c
            q[i+1]+=c
        p=q
    return p


def I(p, j=0, centered=True):
    return sum(c/F(i+j+1) for i,c in enumerate(p) if not centered or (i+j)%2==0)


def drop(roots, *values):
    q=list(roots)
    for x in values:
        q.remove(x)
    return q


def data(roots, centered=True):
    p=nodal(roots)
    C={x:I(nodal(drop(roots,x)),centered=centered) for x in set(roots)}
    h=I(p,2,centered)
    need(I(p,0,centered)==I(p,1,centered)==0 and h and all(C.values()),
         "paid shifts plus active cofactors and nonzero next defect")
    return p,C,h


def parameters(C,h,u,v):
    d=v-u
    return h/(C[u]*d**3), -h/(C[v]*d**3)


def chi(a,b):
    return (a+b-1)**3+27*a*b


def move(roots,u,v):
    p,C,h=data(roots)
    d=v-u
    a,b=parameters(C,h,u,v)
    need(a*b*(a-b)*(a+1)*(b+1) and chi(a,b),"smooth rank-free triple denominators")
    new=[u+d*t for t in (a*(b+1)/(a-b),(a-b)/(a+1),(a+1)/(b+1))]
    left=drop(roots,u,v)
    need(len(set(new))==3 and not (set(new)&(set(left)|{u,v})) and all(-1<x<1 for x in new),
         "strictly interior and distinct inserted roots")
    tau=sum(new)-u-v
    Ru,Rv=h/(C[u]*d),-h/(C[v]*d)
    G=nodal([u,v,tau])
    G[0]-=Ru*v+Rv*u
    G[1]+=Ru+Rv
    need(G==nodal(new),"literal residual cubic")
    new_roots=left+new
    _,_,h_new=data(new_roots)
    need(h_new==I(p,3)-h*sum(new),"exact next defect formula")
    return new_roots,new


def red(x,q):
    need(x.denominator%q,"reduction denoms")
    return x.numerator*pow(x.denominator,-1,q)%q


def certificate(a,b):
    need(a*b*chi(a,b),"smooth final model over Q")
    alpha,beta=b-a-1,a*(2*b+1)
    eta,theta=4*a*b*(a-b),-4*a*a*b*(b+1)
    q=31
    A,B,C,y=map(lambda x:red(x,q),(alpha*alpha-4*beta,2*alpha*eta-4*theta,eta*eta,-eta))
    disc=(A*A*B*B-4*B**3-4*A**3*C-27*C*C+18*A*B*C)%q
    need((A,B,C,y,disc)==(12,16,14,18,5) and y*y%q==C,"literal smooth mod-31 model")
    X,Y=0,y
    checks={}
    for j in range(2,13):
        num,den=(B,2*y) if j==2 else (Y-y,X)
        need(den%q,"affine denominator is a unit")
        slope=num*pow(den,-1,q)%q
        x=(slope*slope-A-X)%q
        z=(slope*(X-x)-Y)%q
        need((z*z-x**3-A*x*x-B*x-C)%q==0,"affine point valid")
        X,Y=x,z
        if j in (6,9,12):
            checks[j]=(X,Y)
    need(checks=={6:(26,27),9:(27,27),12:(0,13)},"finite [6],[9],[12]")
    return checks


m,p=F(-1),F(1)
nodes=[m]*3+[p]*3+[F(-1,3),F(1,3)]
_,C,h=data(nodes)
need(h==F(-256,31185) and [C[k] for k in sorted(C)]==[F(-16,945),F(16,105),F(-16,105),F(16,945)],
     "literal symmetric confluent moments")
print("Confluent centered degree 8: both shifts paid, h=-256/31185; endpoint multiplicities (3,3).")
pairs=[(F(1,3),p),(F(55,87),p),(m,F(5,44)),(m,F(5142230101,23576082933))]
for j,(u,v) in enumerate(pairs,1):
    nodes,tri=move(nodes,u,v)
    if j==1:
        need(tri==[F(5,44),F(-19,39),F(55,87)],"literal first triple")
    if j==2:
        need(tri==[F(3927397,16686208),F(5142230101,23576082933),F(40354847243,50117037387)],
             "literal second triple")
    count=Counter(nodes)
    endpoints=count[m],count[p]
    need(len(nodes)==8+j and len(count)==4+2*j and endpoints==[(3,2),(3,1),(2,1),(1,1)][j-1]
         and all(c==1 for v,c in count.items() if v not in (m,p)),"endpoint multiplicities only")
    print(f"Move {j}: degree {len(nodes)}, {len(count)} distinct values, endpoints {endpoints}, all in [-1,1].")
_,CY,hy=data(nodes)
mapped=[(1+y)/2 for y in nodes]
_,CX,hx=data(mapped,centered=False)
weights={x:CX[x]/prod(x-z for z in mapped if z!=x) for x in mapped}
need(len(weights)==12 and all(weights.values()) and hx*2**14==hy and hx!=0,"actual final weights and defect")
need(all(CX[(1+y)/2]*2**11==CY[y] for y in nodes),"cofactor scales")
actual=[sum(w*x**j for x,w in weights.items()) for j in range(15)]
need(actual[:14]==[F(1,j+1) for j in range(14)] and F(1,15)-actual[14]==hx and hx!=0,
     "all actual uniform moments and exact order")
negative=sum(w<0 for w in weights.values())
need(negative==3 and sum(0<x<1 for x in weights)==10 and set(weights)&{0,1}=={0,1},
     "interval/sign scope")
print("Uniform exact order 14: 12 contributing sites in [0,1], 10 interior, 3 negative weights.")
a,b=parameters(CX,hx,F(0),F(1))
need((a,b)==parameters(CY,hy,m,p),"affine-invariant normalized endpoint pair")
print("Good mod 31: (A,B,C,D_y,disc)=(12,16,14,18,5); [6],[9],[12]D =",list(certificate(a,b).values()))
print("PASS: exact interval-contained uniform seed; no order-20 computation or stage assertion.")

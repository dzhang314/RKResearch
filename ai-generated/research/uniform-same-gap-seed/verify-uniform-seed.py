#!/usr/bin/env python3
"""Exact verification of one prescribed uniform seed; no grid or point search."""
from collections import Counter
from fractions import Fraction as F
from math import prod


def need(good, text):
    if not good:
        raise AssertionError(text)


def nodal(nodes):
    result = [F(1)]
    for node in nodes:
        new = [F(0)]*(len(result)+1)
        for i, c in enumerate(result):
            new[i] -= node*c
            new[i+1] += c
        result = new
    return result


def integral(poly, shift=0):
    return sum(c/F(i+shift+1) for i,c in enumerate(poly))


def without(nodes, *removed):
    out = list(nodes)
    for node in removed:
        out.remove(node)
    return out


def inspect(nodes):
    P = nodal(nodes)
    C = {x:integral(nodal(without(nodes,x))) for x in set(nodes)}
    h = integral(P,2)
    need(integral(P)==integral(P,1)==0 and h and all(C.values()),
         "both paid shifts and nonzero cofactors and next defect")
    return P,C,h


def pair(nodes,u,v):
    _, C, h = inspect(nodes)
    ell = v-u
    need(ell and C[u] and C[v], "distinct eligible pair")
    return h/(C[u]*ell**3),-h/(C[v]*ell**3)


def chi(a,b):
    return (a+b-1)**3+27*a*b


def move(nodes,u,v):
    P,C,h = inspect(nodes)
    a,b = pair(nodes,u,v)
    ell = v-u
    need(a*b*(a-b)*(a+1)*(b+1) and chi(a,b),"smooth finite rank-free chart")
    new=[u+ell*t for t in (a*(b+1)/(a-b),(a-b)/(a+1),(a+1)/(b+1))]
    left=without(nodes,u,v)
    need(len(set(new))==3 and not set(new)&set(left) and u not in new and v not in new,
         "distinct new roots avoiding retained sites and both poles")
    tau=sum(new)-u-v
    Ru=h/(C[u]*ell)
    Rv=-h/(C[v]*ell)
    rhs=nodal([u,v,tau])
    rhs[0]-=Ru*v+Rv*u
    rhs[1]+=Ru+Rv
    need(rhs==nodal(new), "literal factored physical cubic")
    out=left+new
    _,_,h1=inspect(out)
    need(h1==integral(P,3)-h*sum(new), "exact defect update")
    return out,new


def reduce(n,p):
    need(n.denominator%p!=0,"rational reduction denominator")
    return n.numerator*pow(n.denominator,-1,p)%p


def nontorsion(nodes,u,v):
    a,b=pair(nodes,u,v)
    need(a*b*chi(a,b),"smooth final rational model")
    alpha,beta=b-a-1,a*(2*b+1)
    eta,theta=4*a*b*(a-b),-4*a*a*b*(b+1)
    A,B,C=alpha*alpha-4*beta,2*alpha*eta-4*theta,eta*eta
    dY=-eta
    need(dY*dY==C, "rational distinguished point on model")
    p=23
    A,B,C,dY=(reduce(x,p) for x in (A,B,C,dY))
    disc=(A*A*B*B-4*B**3-4*A**3*C-27*C*C+18*A*B*C)%p
    need((A,B,C,dY,disc)==(1,10,6,12,2),"exact good reduction at 23")
    X,Y=0,dY
    chain={}
    for j in range(2,13):
        if j==2:
            numerator,denominator=B,2*Y
        else:
            numerator,denominator=Y-dY,X
        need(denominator%p!=0,"affine division unit; same chain exists over Q")
        slope=numerator*pow(denominator,-1,p)%p
        NX=(slope*slope-A-X)%p
        NY=(slope*(X-NX)-Y)%p
        need((NY*NY-NX**3-A*NX*NX-B*NX-C)%p==0,"point on reduced model")
        X,Y=NX,NY
        chain[j]=(X,Y)
    need([chain[j] for j in (6,9,12)]==[(3,16),(11,21),(11,2)],
         "finite [6], [9], [12] certificates")
    return chain


one=F(1)
nodes=[F(0)]+[one]*4+[F(1,6),F(1,2)]
P,C,h=inspect(nodes)
need(h==F(1,30240) and [C[x] for x in sorted(C)]==
     [F(1,252),F(-1,140),F(1,252),F(-1,5040)],"Jacobi start")
print("Confluent uniform start: degree 7, multiplicity 4 at 1, two paid shifts, h=1/30240.")
for j,(u,n, distinct) in enumerate([(F(1,2),8,6),(F(1,6),9,8),(F(0),10,10)],1):
    nodes,triple=move(nodes,u,one)
    count=Counter(nodes)
    need(len(nodes)==n and len(count)==distinct and count[one]==4-j and
         all(m==1 for x,m in count.items() if x!=one),"exact multiplicity resolution")
    if j==1:
        need(triple==[F(25,57),F(-3,32),F(51,70)], "literal first triple")
    if j==2:
        need(triple==[F(9777623,76372175),F(163552904863,878981491848),F(875570293937,858514304382)],
             "literal second triple")
    _,_,h=inspect(nodes)
    if j==1:
        need(h==F(12283,21235737600),"literal first new defect")
    if j==2:
        need(h==F(-329702846797850500444001919792522379,203975743660430431841630082265843399680000),
             "literal second new defect")
    print(f"Move {j}: degree {n}, {distinct} distinct values; paid shifts and nonzero defect/cofactors.")
P,C,h=inspect(nodes)
weights={x:C[x]/prod(x-y for y in nodes if y!=x) for x in nodes}
need(len(weights)==10 and all(weights.values()), "squarefree full contributing support")
actual=[sum(w*x**j for x,w in weights.items()) for j in range(13)]
need(actual[:12]==[F(1,j+1) for j in range(12)] and F(1,13)-actual[12]==h!=0,
     "direct exact uniform scalar moments")
outside=sum(not 0<=x<=1 for x in nodes)
negative=sum(w<0 for w in weights.values())
need(outside>0 and negative>0,"actual interval/sign scope")
print(f"Uniform exact order 12: ten contributing sites, {outside} outside [0,1], {negative} negative weights.")
chain=nontorsion(nodes,F(25,57),F(51,70))
print("Good mod 23: (A,B,C,D_y,disc)=(1,10,6,12,2); [6],[9],[12]D =",
      [chain[j] for j in (6,9,12)])
print("PASS: exact unrestricted signed uniform seed; no higher-order search or stage assertion.")

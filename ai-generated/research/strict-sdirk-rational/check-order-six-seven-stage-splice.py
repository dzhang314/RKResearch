#!/usr/bin/env python3
"""Derive a seven-stage rational order-six splice and check literal trees."""
from fractions import Fraction as Q
from functools import cache
from itertools import combinations_with_replacement
from math import prod

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def pair(mass,weighted,a,b):
    l=(b*mass-weighted)/(b-a)
    return l,mass-l

def det(rows):
    a,b=rows
    return a[0]*b[1]-a[1]*b[0]

gamma=Q(1,4)
# Boole's fixed rule, in reflected chronology.
y=(Q(1,4),Q(3,4),Q(1,2),Q(0),Q(1))
x=tuple(1-t for t in y)
w=tuple(Q(n,90) for n in (32,32,12,7,7))
assert all(dot(w,[t**k for t in y])==Q(1,k+1) for k in range(6))
h=tuple(wi*prod(t-r for r in y if r!=t) for wi,t in zip(w,y))
alpha=gamma**2/2*h[0]
delta=tuple(alpha/hi for hi in h)
assert delta==(Q(1,32),Q(1,32),Q(-1,8),Q(-1,28),Q(-1,28))
assert delta[0]==gamma**2/2 and delta[1]==2*gamma*y[1]-gamma**2-y[1]**2/2
assert all(dot(w,[di*t**k for di,t in zip(delta,y)])==0 for k in range(4))

# Baseline L fixes row sums and the first reflected error.
L=[[gamma if i==j else Q(0) for j in range(5)] for i in range(5)]
L[1][0]=y[1]-gamma
for i in range(2,5):
    L[i][0],L[i][1]=pair(y[i]-gamma,y[i]**2/2+delta[i]-gamma*y[i],y[0],y[1])
assert [sum(row) for row in L]==list(y)
assert [dot(row,y)-t**2/2 for row,t in zip(L,y)]==list(delta)

def get_eps_sig(L):
    return [dot(row,[t*t for t in y])-t**3/3 for row,t in zip(L,y)], [dot(row,delta) for row in L]

eps,sig=get_eps_sig(L)
p3=(Q(-1,2),Q(-1,2),Q(1),Q(0),Q(0))
p4=(Q(-3,2),Q(1,2),Q(0),Q(1),Q(0))
assert not any(dot(p,v) for p in (p3,p4) for v in ([1]*5,y))
sq=[t*t for t in y]
G=((dot(p3,sq),dot(p4,sq)),(dot(p3,delta),dot(p4,delta)))
assert det(G)!=0
beta=G[1][0]/G[0][0]
assert beta==Q(5,2)
d=[s-beta*e for s,e in zip(sig,eps)]

def M(xi): return xi**2/2-2*gamma*xi+gamma**2
def P(xi,eta): return (3*gamma-eta)*xi+gamma*(eta-2*gamma)
def F(eta): return [(M(t),P(t,eta)) for t in x]

def weighted(z,F):
    return tuple(sum(wi*zi*fi[j] for wi,zi,fi in zip(w,z,F)) for j in range(2))

def compatibility(eta):
    F0=F(eta)
    return det((weighted(d,F0),F0[4]))

s0,s1=compatibility(Q(0)),compatibility(Q(1))
eta=-s0/(s1-s0)
assert eta!=gamma and compatibility(eta)==0
F0=F(eta)
D=det((F0[3],F0[4]))
assert D!=0
# Each error channel prescribes its changes at the same two receivers.
def changes(z):
    v=weighted(z,F0)
    return -det((v,F0[4]))/(D*w[3]),-det((F0[3],v))/(D*w[4])
de,ds=changes(eps),changes(sig)
assert ds[0]==beta*de[0]
a4=de[0]/G[0][0]
a5=det(((de[1],G[0][1]),(ds[1],G[1][1])))/det(G)
b5=det(((G[0][0],de[1]),(G[1][0],ds[1])))/det(G)
for j in range(5):
    L[3][j]+=a4*p3[j]
    L[4][j]+=a5*p3[j]+b5*p4[j]
assert [sum(row) for row in L]==list(y)
assert [dot(row,y)-t**2/2 for row,t in zip(L,y)]==list(delta)
eps,sig=get_eps_sig(L)
assert weighted(eps,F0)==weighted(sig,F0)==(0,0)

# Reverse the weighted transpose; interpolate at core clocks gamma,eta.
idx=tuple(reversed(range(5)))
T=[[L[j][i]*w[j]/w[i] for j in idx] for i in idx]
x_primal=[x[i] for i in idx]
basis=lambda s: ((s-eta)/(gamma-eta),(gamma-s)/(gamma-eta))
integral=lambda s: ((s*s/2-eta*s)/(gamma-eta),(gamma*s-s*s/2)/(gamma-eta))
A=[[gamma]+[Q(0)]*6,[eta-gamma,gamma]+[Q(0)]*5]
for row,t in zip(T,x_primal):
    base=[basis(s) for s in x_primal]
    k=[integral(t)[j]-dot(row,[B[j] for B in base]) for j in range(2)]
    A.append(k+row)
b=(Q(0),Q(0),*(w[i] for i in idx))
c=(gamma,eta,*x_primal)
assert [sum(row) for row in A]==list(c)
assert all(A[i][i]==gamma and all(aij==0 for aij in A[i][i+1:]) for i in range(7))
print("eta",eta,"change coordinates",a4,a5,b5)
print("L",*[tuple(map(str,row)) for row in L],sep="\n")
print("A",[tuple(map(str,row)) for row in A],sep="\n")
print("b",tuple(map(str,b)),"c",tuple(map(str,c)))

# Direct replay uses the published literal rows, independently of the splice.
literal_rows=(
    ("1/4",),
    ("-1/2","1/4"),
    ("-1/8","-1/8","1/4"),
    ("31/24","7/24","-5/6","1/4"),
    ("7/48","1/48","11/96","-1/32","1/4"),
    ("119/768","53/768","-155/1536","9/512","-9/64","1/4"),
    ("-119/256","-29/256","207/512","-31/512","15/64","1/2","1/4"),
)
literal_A=tuple(tuple(map(Q,row))+(Q(0),)*(7-len(row)) for row in literal_rows)
literal_b=tuple(map(Q,("0","0","7/90","7/90","2/15","16/45","16/45")))
assert tuple(map(tuple,A))==literal_A and b==literal_b
assert [sum(row) for row in literal_A]==list(c)
assert tuple(dot(literal_b,col) for col in zip(*literal_A))==tuple(
    bi*(1-ci) for bi,ci in zip(literal_b,c))
q_actual=tuple(dot(row,c)-ci**2/2 for row,ci in zip(literal_A,c))
assert q_actual[:2]==(Q(1,32),Q(-7,32)) and q_actual[2:]==(0,0,0,0,0)

@cache
def order(tree):
    return 1+sum(map(order,tree))

@cache
def factorial(tree):
    return order(tree)*prod(map(factorial,tree))

@cache
def phi(tree):
    children=list(map(phi,tree))
    return tuple(prod(dot(row,z) for z in children) for row in literal_A)

trees={1:[()]}
for n in range(2,8):
    pool=[tree for m in range(1,n) for tree in trees[m]]
    trees[n]=[m for k in range(1,n) for m in combinations_with_replacement(pool,k)
              if sum(map(order,m))==n-1]
    assert len(trees[n])==len(set(trees[n]))
assert [len(trees[n]) for n in range(1,8)]==[1,1,2,4,9,20,48]
passes=[sum(dot(literal_b,phi(tree))*factorial(tree)==1 for tree in trees[n]) for n in range(1,8)]
assert passes[:6]==[1,1,2,4,9,20]
print("paid counts",passes,"of",[len(trees[n]) for n in range(1,8)])
tall=()
for _ in range(6): tall=(tall,)
assert dot(literal_b,phi(tall))==Q(7,40960)
assert passes[6]==0
print("order-seven tall",dot(literal_b,phi(tall)),"instead of 1/5040")

def rank(rows):
    rows=[list(map(Q,r)) for r in rows]
    p=0
    for j in range(len(rows[0])):
        i=next((i for i in range(p,len(rows)) if rows[i][j]),None)
        if i is None:
            continue
        rows[p],rows[i]=rows[i],rows[p]
        z=rows[p][j]
        rows[p]=[x/z for x in rows[p]]
        for i in range(p+1,len(rows)):
            z=rows[i][j]
            rows[i]=[x-z*y for x,y in zip(rows[i],rows[p])]
        p+=1
    return p

grades=[rank([phi(t) for m in range(1,n+1) for t in trees[m]]) for n in range(1,7)]
assert grades==[1,2,4,6,7,7]
print("exact grade ranks E0..E5",grades)

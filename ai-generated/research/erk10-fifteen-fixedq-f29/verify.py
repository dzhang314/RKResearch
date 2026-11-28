"""Independent exact verifier of the 15-stage fixed-q F29 tableau."""
from pathlib import Path
from itertools import combinations_with_replacement
import json

data=json.loads((Path(__file__).parent/"tableau.json").read_text())
A,b,c=data["A"],data["b"],data["c"]
p=data["field"]
assert p==29 and len(A)==len(b)==len(c)==15
assert all(len(row)==15 and all(0<=i<p for i in row) for row in A)
assert all(0<=i<p for i in b+c)
assert all(A[i][j]==0 for i in range(15) for j in range(i,15))
assert c==[sum(row)%p for row in A]
assert b[1:5]==[0,0,0,0]

# Direct independent rooted-order evaluation. IDs are canonical multisets
# of lower-order rooted-tree IDs. All uses of field arithmetic are integers.
trees=[()]; totals=[1]; density=[1]; stages=[[1]*15]
counts=[1]
def bin_multisets(left,start=0):
    if left==0:
        yield ()
    else:
        for q in range(start,len(before)):
            if totals[q]>left: break
            for rest in bin_multisets(left-totals[q],q):
                yield (q,)+rest

def prod(xs):
    q=1
    for u in xs:q*=u
    return q

def dot(a,b):return sum(x*y for x,y in zip(a,b))%p
def apply(r):return [dot(row,r) for row in A]

for m in range(2,11):
    before=list(totals)
    choices=list(bin_multisets(m-1))
    assert len(set(choices))==len(choices)
    children=sorted(set(i for t in choices for i in t))
    derived={i:apply(stages[i]) for i in children}
    for t in choices:
        q=[prod(derived[i][j] for i in t)%p for j in range(15)]
        d=m*prod(density[i] for i in t)
        assert (d*dot(b,q))%p==1
        trees.append(t);totals.append(m);density.append(d);stages.append(q)
    counts.append(len(choices))
assert dot(b,stages[0])==1 and sum(counts)==1205
assert counts==[1,1,2,4,9,20,48,115,286,719]
D=(11*dot(b,[pow(x,10,p) for x in c])-1)%p
assert D==10 and 3*D%29==1
print("strict 15-stage F29 tableau and all 1,205 exact rooted conditions:",counts)
print("order-eleven normalized bush defect 10; inverse 3 modulo 29")

# Check the literal old fixed-q contact, without using the constructor.
o,e,s,k,q=c[:5]
assert o==0 and (2*k-s)*q%p==3*k*s%p
t=(2*q-3*s)%p
assert all(u for u in [e,s,k,q,t]) and len({s,k,q})==3
P=lambda x:x*(x-q)*(x-t)%p
assert P(s) and P(q)==0
alpha=k*k*(3*s-2*k)*pow(s**3,-1,p)%p
assert alpha*P(s)%p==P(k)
assert A[4][1]==0 and (A[4][2]+alpha*A[4][3])%p==0
def ev(f,x):return sum(u*pow(x,i,p) for i,u in enumerate(f))%p
J=lambda f:[0]+[u*pow(i+1,-1,p)%p for i,u in enumerate(f)]
# Exhaustive scalar quadratic inversion, 29^2 at most per retained coordinate.
for j in range(5):
    candidates=[]
    for v in range(p):
        for w in range(p):
            S=[int(j==0),v,w]
            if (ev(S,k)-alpha*ev(S,s))%p!=(int(j==3)-alpha*int(j==2))%p:continue
            if ev(S,q)!=int(j==4):continue
            candidates.append(S)
    assert len(candidates)==1
    f=candidates[0]
    for i in range(5,15):
        assert A[i][j]==(ev(J(f),c[i])-sum(A[i][l]*ev(f,c[l]) for l in range(5,i)))%p
print("literal fixed-q old opening and every high-to-old decoder column checked")

"""Finite S-separated rational nine-site grids, without a symmetry assumption."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd,lcm
from collections import Counter
import sys
from poly_utils import hull,interp,integ,val,scale,add,product,quad
def strip(n):
    n=abs(n)
    if not n:return 0
    for k in (2,3,5,7):
        while n%k==0:n//=k
    return n
def unit(z):
    z=Q(z)
    return strip(z.denominator)==strip(z.numerator)==1
H=int(sys.argv[1]) if len(sys.argv)>1 else 40
P=[i for i in range(1,H+1) if strip(i)==1]
adj={x:{y for y in P if y>x and strip(y-x)==1}for x in range(H+1)}
seen=set(); stats=Counter()
def eval_set(S):
    stats["cliques"]+=1
    if gcd(*S)!=1:return
    ds=hull(S)
    G=[0]+[2520//i*d for i,d in enumerate(ds,1)]
    vals=[val(G,s) for s in S]
    for (i,v),(j,w) in combinations(enumerate(vals),2):
        if v!=w:continue
        ab=[Q(z-S[i],S[j]-S[i]) for z in S]
        if tuple(ab) in seen:continue
        seen.add(tuple(ab));stats["deg9"]+=1
        W=dict(zip(ab,quad(ab,Q(1))))
        if not all(W.values()) or not unit(W[Q(1)]):continue
        stats["unit terminal"]+=1
        proper=[z for z in ab if z not in (0,1)]
        if not all(1<=x.denominator for x in ab):raise AssertionError
        for es in combinations(proper,3):
            scope=[Q(1)]+list(es)
            F=hull([Q(0)]+[z for z in proper if z not in es])
            G=[Q(0)]*4
            for h,x in zip(interp(scope),scope):
                v=Q(0) if x==1 else 1/(W[x]*x*product(x-y for y in proper if x!=y))
                G=add(G,scale(h,v))
            v=sum(W[z]*val(F,z)*(integ(G,Q(1))-integ(G,z)) for z in es)
            if not v:
                stats["exact mixed"]+=1
                print("PAID MESH",ab,"terminal",W[Q(1)],"early proper",es,flush=True)
def recur(prefix,avail):
    n=9-len(prefix)
    if len(avail)<n:return
    if n==0:
        eval_set(prefix);return
    for k in sorted(avail):
        recur(prefix+[k],avail.intersection(adj[k]))
recur([0],set(P))
print("diameter",H,"number of smooth offsets",len(P),"counts",dict(stats),flush=True)

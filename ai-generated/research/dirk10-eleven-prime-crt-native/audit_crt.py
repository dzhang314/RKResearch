"""Independent lower-DIRK and all-tree modular replay of the single CRT literal."""
from pathlib import Path
from math import gcd,prod,isqrt
from argparse import ArgumentParser
import json

HERE=Path(__file__).resolve().parent
INPUT=HERE.parent/"dirk10-eleven-prime-families"
p=ArgumentParser(description=__doc__)
p.add_argument("--seeds",type=Path,default=INPUT/"seeds.json")
p.add_argument("--literals",type=Path,default=INPUT/"tableaux.json")
p.add_argument("--crt",type=Path,default=HERE/"tableau-crt.json")
args=p.parse_args()
d=json.loads(args.crt.read_text())
T=json.loads(args.literals.read_text())
S=json.loads(args.seeds.read_text())
N=int(d["modulus"])
prime_list=[q["p"] for q in T]
assert sorted(set(prime_list))==prime_list and len(prime_list)==32
assert all(all(q%i for i in range(2,isqrt(q)+1)) for q in prime_list)
assert prime_list[0]==59 and N==prod(prime_list)*59
assert d["moduli"]==[59**2]+prime_list[1:]
assert gcd(d["star"],N)==1 and d["star"]*d["starInv"]%N==1

A,b,c=d["A"],d["b"],d["c"]
assert len(A)==len(b)==len(c)==11 and list(map(len,A))==list(range(1,12))
assert all(0<=v<N for row in A for v in row)
assert all(0<=v<N for v in b+c)
assert len({tuple(r+[0]*(11-len(r))) for r in A})==11
assert [sum(r)%N for r in A]==c
assert (11*sum(v*pow(x,10,N) for v,x in zip(b,c))-1)%N==d["star"]
for q in T:
    n=q["p"]
    assert [[x%n for x in r] for r in A]==q["A"]
    assert [x%n for x in b]==q["b"] and [x%n for x in c]==q["c"]
    assert d["star"]%n==q["scaled_order_11_star_defect"]
lift=S["examples"][1]
assert lift["p"]==59**2
assert [[x%3481 for x in r] for r in A]==lift["A"]
assert [x%3481 for x in b]==lift["bvec"] and [x%3481 for x in c]==lift["c"]
assert d["star"]%3481==lift["star"]==1604

# Independently enumerate unordered child multisets with exponentially
# many conceptual trees. No rank/flag information is used below.
parents=[]
counts=[]
def act(v):
    return tuple(sum(a*u for a,u in zip(r,v) if a and u)%N for r in A)
for n in range(1,11):
    layer=[]
    def children(left,k,phi,f):
        if not left:
            assert (f*sum(x*y for x,y in zip(b,phi)))%N==1
            layer.append((n,f,act(phi))); return
        for j in range(k,len(parents)):
            m,fj,v=parents[j]
            if m>left:break
            children(left-m,j,tuple(a*u%N for a,u in zip(phi,v)),f*fj)
    children(n-1,0,(1,)*11,n)
    counts.append(len(layer));parents.extend(layer)
assert counts==[1,1,2,4,9,20,48,115,286,719] and len(parents)==1205
print("literal 11-stage lower triangular and distinct rows; 32 verified prime projections and 59^2")
print("modulus",N)
print("all",len(parents),"independent integer-modular rooted conditions",counts)
print("eleventh bush normalized defect",d["star"])
print("unit inverse modulo composite",d["starInv"],"; mod 59^2 residue",d["star"]%3481)

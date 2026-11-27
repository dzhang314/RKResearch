"""Independent literal order checks, exact next-unit proof, and coefficient-domain census."""
from fractions import Fraction as Q
from math import lcm, gcd
from pathlib import Path
from argparse import ArgumentParser
import json

DIR=Path(__file__).resolve().parent
D1=101588047290852467338246934187117072000
D2=27200218281512417863777752865356303988517513768290967792990592000
BAD=[11,17,19,151,173,607,653,1063,1499,1553]
R0=[1,1,2,4,9,20,48,115,286,719]
REDUCTIONS=[(6,10),(14,16),(18,2),(115,34),(114,125),(600,478),
            (191,92),(863,1029),(360,1008),(256,341)]

def read(t):
    a=json.loads(t.read_text()); s=a["stages"]
    assert (s,a["order"])==(12,10)
    A=[[Q(v) for v in row] for row in a["A"]]
    b=list(map(Q,a["b"])); c=list(map(Q,a["c"]))
    assert len(b)==len(c)==s and list(map(len,A))==list(range(1,s+1))
    assert list(map(sum,A))==c
    assert len({tuple(r+[0]*(s-len(r))) for r in A})==s
    assert len({r[i] for i,r in enumerate(A) if r[i]})>=2
    D=lcm(*(n.denominator for r in A for n in r),*(v.denominator for v in b))
    N=[tuple((i,int(D*v)) for i,v in enumerate(r) if v) for r in A]
    w=[int(D*v) for v in b]
    cs=tuple(sum(v for _,v in r) for r in N)
    return (s,D,N,w,cs,Q(a["eleventh_bush_defect"]))

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def action(N,v):return tuple(sum(a*v[i] for i,a in r) for r in N)

def verify(named,t):
    s,D,N,w,cs,e=read(t)
    forest=[]
    counts=[]
    for n in range(1,11):
        layer=[]
        def children(left,beginning,v,fac):
            if not left:
                assert fac*dot(w,v)==D**n
                layer.append((n,fac,action(N,v)))
                return
            for j in range(beginning,len(forest)):
                k,f,u=forest[j]
                if k>left:break
                children(left-k,j,tuple(a*b for a,b in zip(u,v)),fac*f)
        children(n-1,0,(1,)*s,n)
        counts.append(len(layer))
        forest.extend(layer)
    assert counts==R0 and len(forest)==1205
    bush_int=11*dot(w,[v**10 for v in cs])-D**11
    mixed_int=77*dot(w,[x**3*y for x,y in zip(cs,action(N,[v**6 for v in cs]))])-D**11
    bush,mixed=Q(bush_int,D**11),Q(mixed_int,D**11)
    assert bush==11*e
    print(named, "literal 12-stage lower triangular matrix with distinct rows and unequal diagonals")
    print(named, "all",sum(counts),"integer order tests",counts)
    print(named, "normalized next bush",bush,"; normalized next (3 leaves + 7-bush child)",mixed)
    print(named, "literal D",D)
    return D,bush,mixed

if __name__=="__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("--base",type=Path,default=DIR.parent/"dirk10-twelve-rational-three-ports"/"tableau.json")
    args=p.parse_args()
    d1,e1,_=verify("base",args.base)
    d2,e2,m2=verify("alternate",DIR/"tableau-alternate.json")
    assert (d1,d2)==(D1,D2)
    assert e1==Q(1,2488320) and D1**2 % e1.denominator==0
    assert e2==Q(19891,520224768) and m2==Q(-3253,247726080)
    assert D2**2 % e2.denominator == D2**2 % m2.denominator == 0
    assert -907*e2.numerator-5546*m2.numerator==1
    print("integer Bézout for arbitrary D2-unit rings: -907(19891) - 5546(-3253) = 1")
    assert gcd(D1,D2*e2.numerator)==gcd(D1,D2)==27216000==2**7*3**5*5**3*7
    print("gcd(D1,D2) = gcd(D1,D2*19891) = 2^7*3^5*5^3*7")
    left=D1//(2**7*3**5*5**3*7)
    assert sorted(p for p in BAD if left%p==0)==BAD
    for r in BAD:
        while left%r==0:left//=r
    assert left==1
    for p,(d,v) in zip(BAD,REDUCTIONS):
        assert all(p%q for q in range(2,int(p**.5)+1))
        assert (D2%p,e2.numerator*pow(e2.denominator,-1,p)%p)==(d,v)
        assert d and v
        print("prime",p,": alternate D and normalized bush residues",d,v)

# Exact marked-stage replay for Stepanov's 15-stage order-ten tableau

Two independent audits verified all 1,205 rooted-tree conditions and the row sums, and reproduced the marked-tree thresholds in the 15:13 UTC Dreamer checkpoint. Source: [Stepanov's Zenodo dataset 15429897](https://zenodo.org/records/15429897), the specific coefficient file, not every member of the published family. The file's MD5 is be9e5e3ba1ff8ed21124ad285d7d2fd5.

Use the eight square-free products of \(x=\sqrt3,\ y=\sqrt7,\ z=21\sqrt{(7+2\sqrt7)/21}\). Reduction uses \(x^2=3,\ y^2=7,\ z^2=147+42y\). The positive second nested radical is \(zx(y-2)/63\). The eight elements are independent: since \(x\) is quadratic over \(\mathbb Q(y)\), a square root of \(147+42y\) in that field would be in \(\mathbb Q(y)\) or \(x\mathbb Q(y)\). The respective norms of \(147+42y\) and \((147+42y)/3\) in \(\mathbb Q(y)\) are \(9261\) and \(1029\), neither a rational square.

The exact stage residual \(A\mathbf c-\mathbf c^{\odot2}/2\) has support exactly stage 2, and \(A\mathbf e_2=(4/15)\mathbf e_3\). Thus stages 2 and 3 have residual substitution costs two and three. The first nonzero marked tree orders are as follows: stage 2, (9,7); stage 3, (8,5); stages 4, 5 and 6, (6,3); stages 7 and 8, (3,3), where pairs give one and two marks respectively. The stage-3 ordinary root with three marked children also has weight zero.

## Exact compression of a forced stage with a unique successor

Let an ERK have \(b_i=0\) and \(A\mathbf e_i=a\mathbf e_j\), where \(a\ne0\). The earliest universal additive-forcing response from stage \(i\) with forcing of order \(r\ge0\) equals the earliest response from stage \(j\) with forcing of order \(r+1\). This applies to the exact earliest possible degree over smooth vector fields, not the response to a particular forcing or deletion.

Every parent of an \(i\)-mark must have stage label \(j\). If any two of these parents are nested, the corresponding tree weight is zero: a nonzero labeled path must strictly advance from one to the other, impossible with both labels \(j\). Thus their subtrees are disjoint, and the vector for each such subtree is a scalar multiple of \(\mathbf e_j\). Contract each to a \(j\)-mark and pull out the scalar. If the original tree has \(m\) marks and order \(n\), and the contracted tree has \(k\) marks and order \(n'\), then \(k\le m\) and \(n-n'\ge m\). Consequently \(n'+(r+1)k\le n+rm\). Conversely, wrapping each \(j\)-mark in an ordinary unary root with an \(i\)-mark child adds one vertex per mark and multiplies the weight by a nonzero power of \(a\). The exact costs are therefore equal. The strict-triangular assumption is used for the nesting argument.

For Stepanov's stage 3 with forcing order \(R\ge1\), every tree with at least three marks costs at least \(4+3R\ge5+2R\). Its exact first possible response degree is therefore \(\min(8+R,5+2R)\). The formula also holds at \(R=0\), since the only extra potential obstruction at degree four is the three-mark star, checked zero. The compression theorem gives \(\min(9+r,7+2r)\) for stage 2, including \(r=0\). For stages 4–6, the analogous answer is \(\min(6+r,3+2r)\), and for stages 7–8 it is \(3+r\). This illustrates what exact lower-order residual support can reveal without saying a stage can be deleted.

## Standalone replay

Save as a Python file and pass the original Zenodo text file as its argument. The marked check uses integer ring arithmetic throughout and independently reproduces the table.
```python
"""Verify Zenodo 15429897 with integer arithmetic; pass its .txt file as argv[1]."""
import sys
from pathlib import Path
from functools import lru_cache
from math import lcm
from hashlib import md5

Z=(0,)*8
U=(1,)+(0,)*7

def const(k):return (k,)+(0,)*7
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(k,a):return tuple(k*x for x in a)
def mul(a,b):
    if a == Z or b == Z: return Z
    out=[0]*8
    for i,x in enumerate(a):
        if not x: continue
        for j,y in enumerate(b):
            if not y: continue
            overlap=i&j
            c=x*y*(3 if overlap&1 else 1)*(7 if overlap&2 else 1)
            t=i^j
            if overlap&4:
                out[t]+=147*c
                if t&2:out[t^2]+=294*c
                else:out[t^2]+=42*c
            else:out[t]+=c
    return tuple(out)
def dot(a,b):
    out=Z
    for x,y in zip(a,b):out=add(out,mul(x,y))
    return out

data=Path(sys.argv[1]).read_bytes()
assert md5(data).hexdigest()=="be9e5e3ba1ff8ed21124ad285d7d2fd5"
rows=[list(map(int,r.split())) for r in data.splitlines()]
D=63*lcm(*(r[-1] for r in rows))
def decode(r):
    a,b,c,d,e,f,g,h,q=r
    L=D//(63*q)
    return scale(L,(63*a,63*b,63*c,63*d,3*e,-2*f+7*h,3*g,f-2*h))
V=list(map(decode,rows))
c,b=V[:15],V[15:30]
A=[V[30+i*(i-1)//2:30+i*(i+1)//2] for i in range(15)]
def mat(v):return tuple(dot(row,v) for row in A)
def basis(j): return tuple(U if i==j-1 else Z for i in range(15))
assert mat((U,)*15)==tuple(c)
q=tuple(add(scale(2,x),scale(-1,mul(y,y))) for x,y in zip(mat(c),c))
assert [i+1 for i,v in enumerate(q) if v!=Z]==[2]
assert mat(basis(2))==tuple(const(4*D//15) if i==2 else Z for i in range(15))

def trees(max_n,max_m):
    T=[(),None] if max_m else [()]
    sizes=[1]*len(T); marks=list(range(len(T))); fact=[1]*len(T)
    for n in range(2,max_n+1):
        end=len(T)
        def child(left,j,budget):
            if left==0:
                yield ()
            else:
                for k in range(j,end):
                    if sizes[k]>left: break
                    if marks[k]>budget: continue
                    for rest in child(left-sizes[k],k,budget-marks[k]):
                        yield (k,)+rest
        for t in child(n-1,0,max_m):
            T.append(t); sizes.append(n); marks.append(sum(marks[k] for k in t))
            f=n
            for k in t:f*=fact[k]
            fact.append(f)
    return list(zip(T,sizes,marks,fact))
def weights(ts,stage=None,cut=None):
    stage_weights=[]
    @lru_cache(None)
    def branch(k):return mat(stage_weights[k])
    for t,n,m,f in ts:
        if cut and not cut(n,m): stage_weights.append(None);continue
        if t is None:
            P=basis(stage)
        else:
            P=(U,)*15
            for k in t:P=tuple(mul(x,y) for x,y in zip(P,branch(k)))
        stage_weights.append(P)
        yield n,m,f,dot(b,P)
count=0
for n,m,f,v in weights(trees(10,0)):
    assert scale(f,v)==const(D**n)
    count+=1
assert count==1205
print(f"Exact RKOC: {count} passed.",flush=True)
T=trees(9,2)
for j,expected in [(2,(9,7)),(3,(8,5)),(4,(6,3)),(5,(6,3)),(6,(6,3)),(7,(3,3)),(8,(3,3))]:
    low=[None,None,None]
    for n,m,f,v in weights(T,j,lambda n,m:m==0 or n<=expected[m-1]):
        if m and v!=Z and low[m] is None:low[m]=n
    assert tuple(low[1:])==expected,(j,low)
    print(j,*low[1:],flush=True)
v=mat(basis(3))
assert dot(b,tuple(mul(x,mul(x,x)) for x in v))==Z
print("The stage-3 three-mark star at order four also vanishes.")
```

#!/usr/bin/env python3
"""Read the literal rational coefficients, independently of the constructor."""
from fractions import Fraction as Q
from pathlib import Path
import json

def verify(path):
    rec=json.loads(path.read_text())
    n=rec['stages']
    A=[list(map(Q,r)) for r in rec['A']]
    b=list(map(Q,rec['b']))
    c=list(map(Q,rec['c']))
    assert len(A)==len(b)==len(c)==n
    assert all(len(row)==n for row in A)
    assert all(row[j]==0 for i,row in enumerate(A) for j in range(i+1,n))
    assert any(A[i][i]!=0 for i in range(n))
    assert all(sum(row)==ci for row,ci in zip(A,c))

    # A tree shape is a balanced bracket word, with the whole child
    # multiset sorted lexically. Repeated grafting of a branch enumerates
    # the quotient of the reviewed binary constructors by sibling order.
    leaves={1:{"()":((Q(1),)*n,1)}}
    counts=[1]
    for m in range(2,11):
        parent={}
        for k in range(1,m):
            for parent0,(v,f) in leaves[m-k].items():
                for child,(w,g) in leaves[k].items():
                    chunks=[]
                    level=0
                    inner=parent0[1:-1]
                    for j,ch in enumerate(inner):
                        if ch=="(":
                            if level==0:start=j
                            level+=1
                        else:
                            level-=1
                            if level==0:chunks.append(inner[start:j+1])
                    shape="("+"".join(sorted([*chunks,child]))+")"
                    h=tuple(v[i]*sum(aij*w[j] for j,aij in enumerate(row)) for i,row in enumerate(A))
                    inv_gamma=(f//(m-k))*g*m
                    if shape in parent:assert parent[shape]==(h,inv_gamma)
                    else:parent[shape]=(h,inv_gamma)
        counts.append(len(parent))
        leaves[m]=parent
    assert counts==[1,1,2,4,9,20,48,115,286,719]==rec['unordered_counts']
    for m,by_shape in leaves.items():
        for shape,(v,f) in by_shape.items():
            assert f*sum(w*phi for w,phi in zip(b,v))==1,(m,shape)
    scaled=11*sum(bi*ci**10 for bi,ci in zip(b,c))-1
    assert scaled==Q(rec['scaled_order_11_star_defect'])!=0
    print(f"{n} stages: {sum(counts)} rooted conditions; exact order, "
          f"scaled order-11 star residual {scaled}.")

if __name__=="__main__":
    for s in (14,15):verify(Path(__file__).with_name(f"dirk10-{s}.json"))

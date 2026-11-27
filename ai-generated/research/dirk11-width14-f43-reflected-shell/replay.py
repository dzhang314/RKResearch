#!/usr/bin/env python3
"""Independent literal F43 replay using binary grafts of unordered trees."""
from pathlib import Path
from functools import cache
import json

def verify():
    r=json.loads(Path(__file__).with_name("tableau.json").read_text())
    p,n=r["field"],r["stages"];A,b=r["A"],r["b"]
    assert p==43 and n==14 and len(A)==len(b)==n
    assert all(len(row)==n for row in A)
    assert all(0<=x<p for row in A for x in row) and all(0<=x<p for x in b)
    assert all(A[i][j]==0 for i in range(n)for j in range(i+1,n))
    assert any(A[i][i]for i in range(n))
    assert r["c"]==[sum(row)%p for row in A]
    @cache
    def tr(t):
        deg=1+sum(tr(c)[0]for c in t)
        fac=deg
        s=[1]*n
        for c in t:
            _,cf,cv=tr(c)
            fac=fac*cf%p
            act=[sum(a*x for a,x in zip(row,cv))%p for row in A]
            s=[x*y%p for x,y in zip(s,act)]
        return deg,fac,tuple(s)
    layers={1:{()}}
    counts=[1]
    for m in range(2,13):
        Q=set()
        for k in range(1,m):
            for s in layers[m-k]:
                for t in layers[k]:Q.add(tuple(sorted(s+(t,))))
        layers[m]=Q
        counts.append(len(Q))
    assert counts==[1,1,2,4,9,20,48,115,286,719,1842,4766]
    for m in range(1,12):
        for t in layers[m]:
            _,fac,v=tr(t)
            assert fac*sum(x*y for x,y in zip(b,v))%p==1,(m,t)
    failure=None
    for t in sorted(layers[12]):
        _,fac,v=tr(t)
        df=(fac*sum(x*y for x,y in zip(b,v))-1)%p
        if df:
            failure=(t,df,pow(df,-1,p));break
    assert failure
    print(sum(counts[:-1]),"literal rooted conditions through eleven;",counts[:-1])
    print("first failing tree of order 12:",failure)
    return failure
if __name__=="__main__":verify()

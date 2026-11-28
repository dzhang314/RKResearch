#!/usr/bin/env python3
"""Check only the frozen literal tableaux, with independent multiset trees."""
from functools import cache
from itertools import combinations_with_replacement,groupby,product
from pathlib import Path
from math import prod
import json,sys
HERE=Path(__file__).resolve().parent
def partitions(n,start=1):
    if n==0:
        yield ()
    for a in range(start,n+1):
        for rest in partitions(n-a,a):
            yield a,*rest
@cache
def trees(n):
    v=[]
    for s in partitions(n-1):
        pools=[tuple(combinations_with_replacement(trees(k),len(tuple(block))))
               for k,block in groupby(s)]
        for by_grade in product(*pools):
            v.append(tuple(t for batch in by_grade for t in batch))
    return tuple(v)
@cache
def weight(t):
    return 1+sum(weight(u)for u in t)
@cache
def gamma(t):
    return weight(t)*prod(gamma(u)for u in t)
def values(J):
    N=J['modulus'];p=J['field'];n=J['exponent']
    assert N==p**n
    A,b=J['A'],J['b']
    assert len(A)==len(b)==16
    assert all(len(r)==i for i,r in enumerate(A))
    assert len({tuple(r+[0]*(16-len(r)))for r in A})==16
    assert all(0<=x<N for r in A+[b] for x in r)
    @cache
    def elementary(t):
        rows=[action(s)for s in t]
        return tuple(prod(v[i]for v in rows)%N for i in range(16))
    @cache
    def action(t):
        vv=elementary(t)
        return tuple(sum(a*v for a,v in zip(row,vv))%N for row in A)
    rr=0
    T=((),)*10
    for i in range(1,11):
        for t in trees(i):
            assert weight(t)==i
            s=gamma(t)*sum(w*v for w,v in zip(b,elementary(t)))%N
            assert s==1,(p,n,t,s)
            rr+=1
    assert rr==1205
    assert gamma(T)==11 and J['next_failure_tree']==[[]]*10
    defect=(gamma(T)*sum(w*v for w,v in zip(b,elementary(T)))-1)%N
    assert defect==J['next_failure_value'] and defect%p
    return rr,defect
def compare(L,J):
    N=L['modulus']
    assert J['field']==L['field']
    assert J['exponent']==L['exponent']+1
    assert J['next_failure_value']%N==L['next_failure_value']
    assert [v%N for v in J['raw']]==L['raw']
    assert [[v%N for v in r]for r in J['A']]==L['A']
    assert [v%N for v in J['b']]==L['b']
def main(path):
    allrows=[json.loads(p.read_text())for p in Path(path).glob('f*-power*.json')]
    assert allrows
    seen={}
    for j in sorted(allrows,key=lambda r:(r['field'],r['exponent'])):
        q,n=j['field'],j['exponent'];u,d=values(j)
        if n>1:compare(seen[q],j)
        seen[q]=j
        print('p',q,'power',n,'modulus',j['modulus'],'rooted conditions',u,'unit bush defect',d)
if __name__=='__main__':
    main(sys.argv[1]if len(sys.argv)>1 else HERE/'literals')

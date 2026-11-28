#!/usr/bin/env python3
"""Standalone exact unordered-rooted replay in the selected F17 cubic field."""
from array import array
from math import prod
from pathlib import Path
import json

P=17
Q=P**3

def enc(v):
    return sum(x*P**i for i,x in enumerate(v))
def dec(z):
    return [z%P,z//P%P,z//(P*P)]
def add(a,b):
    a0,a1,a2=dec(a);b0,b1,b2=dec(b)
    return enc([(a0+b0)%P,(a1+b1)%P,(a2+b2)%P])
def mul(a,b):
    a0,a1,a2=dec(a);b0,b1,b2=dec(b)
    c0=a0*b0;c1=a0*b1+a1*b0;c2=a0*b2+a1*b1+a2*b0
    c3=a1*b2+a2*b1;c4=a2*b2
    # z^3=-10-3z-7z^2 in F17[z]/(z^3+7z^2+3z+10).
    c1-=10*c4;c2-=3*c4;c3-=7*c4
    c0-=10*c3;c1-=3*c3;c2-=7*c3
    return enc([c0%P,c1%P,c2%P])
def pw(a,n):
    r=1
    while n:
        if n%2:r=mul(r,a)
        n//=2
        if n:a=mul(a,a)
    return r
def sum_field(vals):
    s=0
    for a in vals:s=add(s,a)
    return s
def checked(v):
    assert len(v)==3 and all(type(x) is int and 0<=x<P for x in v)
    return enc(v)

def main():
    data=json.loads(Path(__file__).with_name('tableau.json').read_text())
    assert P==data['p'] and all(P%d for d in range(2,5))
    assert data['base']==[10,3,7,1] and data['orientation']==[]
    assert all((x**3+7*x*x+3*x+10)%P for x in range(P))
    A=[[checked(x) for x in row] for row in data['A']]
    b=list(map(checked,data['b']));c=list(map(checked,data['c']))
    s=len(b)
    assert s==len(A)==len(c)==15 and all(len(row)==s for row in A)
    assert all(A[i][j]==0 for i in range(s) for j in range(i+1,s))
    assert any(A[i][i] for i in range(s)) and A[0][0]==A[-1][-1]==0
    assert c==list(map(sum_field,A)) and sum_field(b)==1
    assert [i for i,z in enumerate(b) if not z]==[1,2,3,4]
    assert mul(2,c[5])==1 and data['chart']==9
    matrix=[[(j,coeff) for j,coeff in enumerate(row) if coeff] for row in A]
    cache={a:array('H',(mul(a,v) for v in range(Q)))
           for a in set(b).union(x for row in A for x in row) if a}
    M=[[(j,cache[coeff]) for j,coeff in row] for row in matrix]
    bc=[(j,cache[coeff]) for j,coeff in enumerate(b) if coeff]
    order=[1];gamma=[1];Apr=[tuple(c)]
    counts=[1]
    for n in range(2,13):
        stop=len(order);cnt=0
        def forests(total,least):
            if total==0:
                yield ();return
            for j in range(least,stop):
                if order[j]>total:break
                for tail in forests(total-order[j],j):yield (j,)+tail
        for row in forests(n-1,0):
            g=n*prod(gamma[i] for i in row)
            stage=[]
            for i in range(s):
                t=1
                for j in row:t=mul(t,Apr[j][i])
                stage.append(t)
            v=sum_field(mult[stage[j]] for j,mult in bc)
            assert mul(g%P,v)==1,(n,row)
            order.append(n);gamma.append(g)
            Apr.append(tuple(sum_field(mul_table[stage[j]] for j,mul_table in row0) for row0 in M))
            cnt+=1
        counts.append(cnt)
    assert counts==[1,1,2,4,9,20,48,115,286,719,1842,4766]
    star=add(mul(13,sum_field(mul(x,pw(y,12)) for x,y in zip(b,c))),16)
    assert star and dec(star)==data['scaled_order13_star']==[11,7,12]
    print(f"F17 cubic field; 15 ordinary DIRK stages; rooted counts {counts}, total {sum(counts)}")
    print(f"scaled degree-12 bush defect (order-13) {dec(star)}; exact order 12")

if __name__=='__main__':
    main()

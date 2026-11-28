#!/usr/bin/env python3
"""Exact 10+12-2 stage factorial-only DIRK order twelve."""
from fractions import Fraction as Q
from math import factorial, lcm, gcd
from pathlib import Path
import argparse
import json
from arith import cardinals,ev,prim,lin,strip,bank
from reverse import reduce_ranktwo


def build(path):
    lit=json.loads(path.read_text())
    x=tuple(map(Q,lit['x']))
    w=tuple(map(Q,lit['w']))
    w0=Q(lit['w0'])
    assert len(x)==12 and x[0]==1 and all(w) and w0
    assert w0+sum(w)==1
    assert all(sum(m*z**k for m,z in zip(w,x,strict=True))==Q(1,k+1) for k in range(1,12))
    u,z=x[-2:]
    A0,c0,ports,F=bank(u,z,lit['old_stem'])
    assert len(A0)==10 and len(F)==3
    assert all(f[0]==ev(f,u)==ev(f,z)==0 for f in F)
    rows,b0,replay,G,_,cols=reduce_ranktwo(x,w,F)
    taps=tuple(map(Q,lit['small_taps']))
    assert lin(rows,taps)==b0
    assert len(rows)==lit['rank'] and len(cols)==lit['direction_count']
    K=replay(taps)
    assert K==[list(map(Q,row)) for row in lit['K']]
    assert G==list(map(Q,lit['G']))
    assert all(strip(a.denominator)==1 for row in K for a in row)
    assert all(sum(g*a**k for g,a in zip(G,x,strict=True))==0 for k in range(1,9))

    n=len(x)
    T=[[K[n-1-j][n-1-i] if j<=i else Q(0) for j in range(n)] for i in range(n)]
    xs=x[::-1]
    Phi=cardinals(tuple(c0[i] for i in ports))
    raw=[[*q,*([Q(0)]*n)] for q in A0]
    for i,c in enumerate(xs):
        a=[Q(0)]*10
        for j,p in zip(ports,Phi,strict=True):
            a[j]=ev(prim(p),c)-sum(T[i][k]*ev(p,xs[k]) for k in range(i+1))
        raw.append([*a,*T[i]])
    raw_c=c0+list(xs)
    bb=[w0]+[Q(0)]*9+list(w[::-1])
    assert lin(raw,[Q(1)]*22)==raw_c
    assert all(all(a==0 for a in row[i+1:]) for i,row in enumerate(raw))
    shifts=[]
    for i in range(2):
        difference=[Q(0)]*22
        for j in range(i+1):
            t=T[i][j]
            difference[10+j]+=t; difference[8+j]-=t
        assert raw[10+i]==[a+b for a,b in zip(raw[8+i],difference,strict=True)]
        shifts.append(T[i][:i+1])
    for a in raw:
        a[8]+=a[10]; a[9]+=a[11]
    bb[8]+=bb[10]; bb[9]+=bb[11]
    keep=[i for i in range(22) if i not in (10,11)]
    A=[[raw[i][j] for j in keep] for i in keep]
    b=[bb[i] for i in keep]
    c=[raw_c[i] for i in keep]
    assert lin(A,[Q(1)]*20)==c
    assert all(not any(row[i+1:]) for i,row in enumerate(A))
    assert A[0][0]==0 and A[1][1]==Q(1,16)
    DA=lcm(*(a.denominator for row in A for a in row))
    DB=lcm(*(a.denominator for a in b))
    D=lcm(DA,DB)
    assert strip(D)==1
    e=next(i for i in range(1,80) if factorial(12)**i%D==0)
    read=lambda q:sum(a*v for a,v in zip(b,q,strict=True))
    bush=13*read([x**12 for x in c])-1
    zt=[Q(1)]*20
    for _ in range(12):
        zt=lin(A,zt)
    tall=factorial(13)*read(zt)-1
    assert bush and tall
    g=gcd(abs(bush.numerator),abs(tall.numerator))
    packet=dict(order=12,stages=20,A=[[str(a) for a in row] for row in A],
        b=list(map(str,b)),c=list(map(str,c)),matrix_denominator=DA,
        weight_denominator=DB,common_denominator=D,factorial_exponent=e,
        scaled_next_bush=str(bush),scaled_next_tall=str(tall),
        unit_cover_from_next_bush_tall=strip(g)==1)
    return packet,shifts,g

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--input',type=Path,default=Path(__file__).with_name('reverse-paid-fit.json'))
    p.add_argument('--emit',type=Path,required=True)
    opt=p.parse_args()
    P,shifts,g=build(opt.input)
    opt.emit.write_text(json.dumps(P,separators=(',',':'))+'\n')
    print('two exact causal row shifts:',shifts)
    print('D=',P["common_denominator"],'divides (12!)^'+str(P['factorial_exponent']))
    print('scaled next bush:',P['scaled_next_bush'])
    print('scaled next tall numerator bits:',abs(Q(P['scaled_next_tall']).numerator).bit_length())
    print('two defect numerator gcd:',g)
if __name__=='__main__':main()

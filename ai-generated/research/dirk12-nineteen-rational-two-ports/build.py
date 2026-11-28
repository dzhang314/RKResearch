#!/usr/bin/env python3
"""Exact 10+11-2 stage construction for rational DIRK12."""
from fractions import Fraction as Q
from math import factorial, lcm, gcd
from pathlib import Path
import argparse
import json
from probe import old_bank, cardinals, ev, prim, lin
from ranktwo import lift, early
from trap_design import setup


def exact_solve(M,b):
    M=[list(row)+[val] for row,val in zip(M,b,strict=True)]
    n=len(M[0])-1
    piv=[]
    for j in range(n):
        r=len(piv)
        idx=next((i for i in range(r,len(M)) if M[i][j]),None)
        if idx is None:
            continue
        M[r],M[idx]=M[idx],M[r]
        row=M[r]
        factor=row[j]
        row[j:]=[Q(a)/factor for a in row[j:]]
        for k in range(r+1,len(M)):
            line=M[k]
            factor=line[j]
            if factor:
                line[j:]=[a-factor*c for a,c in zip(line[j:],row[j:],strict=True)]
        piv.append(j)
    assert all(not row[-1] for row in M[len(piv):]), "inconsistent over Q"
    u=[Q(0)]*n
    for i,j in reversed(list(enumerate(piv))):
        u[j]=M[i][-1]-sum(a*v for a,v in zip(M[i][j+1:-1],u[j+1:],strict=True) if a and v)
    return u,len(piv)


def build():
    selected=tuple(Q(i,11) for i in (1,2,3,4,6,7,8,9,10))
    head=tuple(Q(i,11) for i in (2,4,3))
    u,z=Q(1,11),Q(6,11)
    x,w,w0,seed,v=setup(selected,head,u)
    assert v==Q(26881,94316)
    assert seed==Q(-17793879367,6805627317)
    perm=[i for i,a in enumerate(x) if a!=z]+[x.index(z)]
    x=tuple(x[i] for i in perm)
    w=[w[i] for i in perm]
    assert x[-2:]==(u,z)
    y=[1-a for a in x]
    assert all(w) and w0
    assert w0+sum(w)==1
    assert all(sum(b*c**k for b,c in zip(w,x,strict=True))==Q(1,k+1)
               for k in range(1,12))
    A0,c0,ports,actual=old_bank(u,z,fa=Q(9,14),fb=Q(1,2),fc=Q(5,14))
    assert len(actual)==3
    assert all(ev(a,u)==ev(a,z)==a[0]==0 for a in actual)
    F=actual
    M,rhs,indices=lift(x,w,F,seed)
    cof,rank=exact_solve(M,rhs)
    assert len(M)==64 and len(cof)==66 and rank==51
    assert lin(M,cof)==rhs
    n=len(x)
    L=[[Q(0)]*n for _ in range(n)]
    for (i,j),a in zip(indices,cof,strict=True):
        L[i][j]=a
    for i in range(1,4):
        assert L[i]==[y[i]/2]+[Q(0)]*(i-1)+[y[i]/2]+[Q(0)]*(10-i)
    test, (forms,*_)=early(x,w)
    assert ev(test,seed)==0
    G=[ev(a,seed) for a in forms]
    g4=lin(L,[a**3 for a in y])
    h4=lin(L,G)
    assert g4==[a**4/4+Q(3,2)*a*b for a,b in zip(y,G,strict=True)]
    assert h4==[a*b/2 for a,b in zip(y,G,strict=True)]
    assert all(sum(a*b*c**d for a,b,c in zip(w,G,x,strict=True))==0 for d in range(1,9))

    # Reverse the weighted transpose to obtain the actual, causal suffix.
    Ti=[[L[n-1-j][n-1-i]*w[n-1-j]/w[n-1-i] if j<=i else Q(0)
         for j in range(n)] for i in range(n)]
    xs=x[::-1]
    Phi=cardinals(tuple(c0[j] for j in ports))
    raw=[[*q,*([Q(0)]*n)] for q in A0]
    for i,c in enumerate(xs):
        a=[Q(0)]*10
        for j,p in zip(ports,Phi,strict=True):
            a[j]=ev(prim(p),c)-sum(Ti[i][k]*ev(p,xs[k]) for k in range(i+1))
        raw.append([*a,*Ti[i]])
    raw_c=c0+list(xs)
    bb=[w0]+[Q(0)]*9+w[::-1]
    assert lin(raw,[Q(1)]*21)==raw_c
    assert all(all(a==0 for a in row[i+1:]) for i,row in enumerate(raw))
    shifts=[]
    for i in range(2):
        difference=[Q(0)]*21
        for j in range(i+1):
            t=Ti[i][j]
            difference[10+j]+=t; difference[8+j]-=t
        assert raw[10+i]==[a+b for a,b in zip(raw[8+i],difference,strict=True)]
        shifts.append(Ti[i][:i+1])
    for a in raw:
        a[8]+=a[10]; a[9]+=a[11]
    bb[8]+=bb[10]; bb[9]+=bb[11]
    keep=[i for i in range(21) if i not in (10,11)]
    A=[[raw[i][j] for j in keep] for i in keep]
    b=[bb[i] for i in keep]
    c=[raw_c[i] for i in keep]
    assert lin(A,[Q(1)]*19)==c
    assert all(all(a==0 for a in row[i+1:]) for i,row in enumerate(A))
    assert A[0][0]==0 and A[1][1]!=0
    assert sum(b)==1
    DA=lcm(*(a.denominator for row in A for a in row))
    DB=lcm(*(a.denominator for a in b))
    D=lcm(DA,DB)
    read=lambda q:sum(a*v for a,v in zip(b,q,strict=True))
    bush=13*read([x**12 for x in c])-1
    zt=[Q(1)]*19
    for _ in range(12):
        zt=lin(A,zt)
    tall=factorial(13)*read(zt)-1
    assert bush
    strip=gcd(abs(bush.numerator),abs(tall.numerator))
    while (k:=gcd(strip,D))>1:
        strip//=k
    packet=dict(order=12,stages=19,A=[[str(a) for a in row] for row in A],
        b=list(map(str,b)),c=list(map(str,c)),matrix_denominator=DA,
        weight_denominator=DB,common_denominator=D,scaled_next_bush=str(bush),scaled_next_tall=str(tall),
        unit_cover_from_next_bush_tall=strip==1)
    return packet,(rank,shifts,v,seed),D.bit_length(),strip


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--emit",type=Path,required=True)
    opts=p.parse_args()
    data,details,bits,strip=build()
    opts.emit.write_text(json.dumps(data,separators=(',',':'))+"\n")
    print("rank, duplicate causal shifts, free scalar clock, affine slope:",details)
    print("coefficient denominator bits",bits,"unpaid defect gcd stripped",strip)
    print("next bush",data["scaled_next_bush"])


if __name__=="__main__":
    main()

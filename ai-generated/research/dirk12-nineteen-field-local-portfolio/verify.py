#!/usr/bin/env python3
"""Independent exact balanced-bracket rooted replay of the literal DIRK12 tableau."""
from fractions import Fraction as Q
from functools import cache
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json


def children(word):
    depth=0
    first=1
    out=[]
    for i,ch in enumerate(word[1:-1],1):
        depth+=1 if ch=="(" else -1
        if depth==0:
            out.append(word[first:i+1])
            first=i+1
    assert depth==0 and first==len(word)-1
    return tuple(out)


def rooted_catalog(p):
    # Enumerate multiset unions by successive insertion of nondecreasing trees.
    layers=[None, ("()",)]
    alltrees=["()"]
    for n in range(2,p+1):
        sizes=tuple(len(z)//2 for z in alltrees)

        @cache
        def tails(rem,k):
            if rem==0:
                return ("",)
            ls=[]
            for j in range(k,len(sizes)):
                if sizes[j]>rem:
                    break
                ls.extend(alltrees[j]+u for u in tails(rem-sizes[j],j))
            return tuple(ls)

        layer=tuple("("+u+")" for u in tails(n-1,0))
        assert len(layer)==len(set(layer))
        layers.append(layer)
        alltrees.extend(layer)
    return layers[1:]


def replay(file, expected_diag):
    P=json.loads(file.read_text())
    s,p=P["stages"],P["order"]
    assert s==19 and p==12
    mat=tuple(tuple(map(Q,row)) for row in P["A"])
    out=tuple(map(Q,P["b"]))
    clock=tuple(map(Q,P["c"]))
    assert len(out)==len(clock)==len(mat)==s
    assert all(len(row)==s and not any(row[i+1:]) for i,row in enumerate(mat))
    assert mat[0][0]==0 and mat[1][1]==expected_diag
    assert tuple(map(sum,mat))==clock
    DA=lcm(*(v.denominator for row in mat for v in row))
    DB=lcm(*(v.denominator for v in out))
    D=lcm(DA,DB)
    assert (DA,DB,D)==(P["matrix_denominator"],P["weight_denominator"],P["common_denominator"])

    def toint(x,z):
        q=x*z
        assert q.denominator==1
        return q.numerator

    A=tuple(tuple((j,toint(a,DA)) for j,a in enumerate(row) if a)
            for row in mat)
    b=tuple(toint(v,DB) for v in out)

    def mul(v):
        return tuple(sum(a*v[j] for j,a in row) for row in A)

    def read(v):
        return sum(a*z for a,z in zip(b,v,strict=True))

    @cache
    def elementary_after_primitive(word):
        f=children(word)
        k=len(word)//2
        den=k
        vec=[1]*s
        for child in f:
            gd,mv=elementary_after_primitive(child)
            den*=gd
            for i,a in enumerate(mv):
                vec[i]*=a
        assert den*read(vec)==DB*DA**(k-1),word
        return den,mul(vec) if k<p else None

    layers=rooted_catalog(p)
    counts=list(map(len,layers))
    assert counts==[1,1,2,4,9,20,48,115,286,719,1842,4766]
    for layer in layers:
        for word in layer:
            elementary_after_primitive(word)
    z=[1]*s
    for _ in range(p):
        z=mul(z)
    scale=DB*DA**p
    tall=Q(factorial(p+1)*read(z),scale)-1
    bush=Q((p+1)*read([toint(c,DA)**p for c in clock]),scale)-1
    assert str(tall)==P["scaled_next_tall"]
    assert str(bush)==P["scaled_next_bush"] and bush
    assert D**(p+1)%tall.denominator==D**(p+1)%bush.denominator==0
    common=gcd(abs(tall.numerator),abs(bush.numerator))
    stripped=common
    while (d:=gcd(stripped,D))>1:
        stripped//=d
    assert P["unit_cover_from_next_bush_tall"] and stripped==1
    assert D % expected_diag.denominator == D % abs(expected_diag.numerator) == 0
    assert common == 1
    print("rooted shapes:",counts,"total:",sum(counts))
    print("physical diagonal 0=",mat[0][0],"diagonal 1=",mat[1][1])
    print("common literal denominator bits:",D.bit_length())
    print("scaled next bush:",bush)
    print("two normalized defect numerator gcd:",common,"after removing D factors:",stripped)
    return D


def main():
    here=Path(__file__).resolve().parent
    files=[here.parent/'dirk12-nineteen-rational-two-ports'/'tableau19.json']+[
        here/f'tableau-{key}.json' for key in 'bcd'
    ]
    diags=map(Q,('9/616','1/112','621/1414','35/136'))
    D=[]
    for j,(path,diag) in enumerate(zip(files,diags,strict=True)):
        print('portfolio member', 'abcd'[j])
        D.append(replay(path,diag))
    g=gcd(*D)
    assert D[2]%13==11 and D[3]%19==17
    assert g==61963646976000 and factorial(12)**3%g==0
    assert factorial(12)**2%g!=0
    print('four-way denominator gcd',g,'divides (12!)^3')
    print('specific local coverage: third literal at p=13; fourth literal at p=19')


if __name__=='__main__':
    main()

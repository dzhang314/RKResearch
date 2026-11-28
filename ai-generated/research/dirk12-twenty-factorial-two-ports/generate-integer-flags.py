#!/usr/bin/env python3
"""Literal integer flags and tall recurrence for the universal DIRK12."""
from fractions import Fraction as Q
from argparse import ArgumentParser
from math import factorial,lcm
from pathlib import Path
import json

NAME="DIRK12FactorialTwentyFlag"

def dot(x,y):
    return sum(a*b for a,b in zip(x,y,strict=True) if a and b)

def act(M,v):
    return [dot(row,v) for row in M]

def cw(x,y):
    return [a*b for a,b in zip(x,y,strict=True)]

def rref(vectors):
    E={}
    for vec in vectors:
        v=list(map(Q,vec))
        for i,z in sorted(E.items()):
            if v[i]:
                a=v[i]; v=[x-a*y for x,y in zip(v,z,strict=True)]
        i=next((j for j,x in enumerate(v) if x),None)
        if i is None:continue
        z=[a/v[i] for a in v]
        for j,u in list(E.items()):
            if u[i]:
                a=u[i]; E[j]=[x-a*y for x,y in zip(u,z,strict=True)]
        E[i]=z
    R=[]
    for p,z in sorted(E.items()):
        d=lcm(*(a.denominator for a in z))
        R.append((p,d,[int(d*a) for a in z]))
    return R

def bez(a,b):
    r,s,u,v,p,q=a,b,1,0,0,1
    while s:
        t,m=divmod(r,s)
        r,s=s,m;u,v=v,u-t*v;p,q=q,p-t*q
    return (-u,-p,-r) if r<0 else (u,p,r)

def arr(x):
    return "#["+", ".join(arr(a) if isinstance(a,(list,tuple)) else str(a) for a in x)+"]"

def build(source):
    J=json.loads(source.read_text()); D=J["common_denominator"]
    assert J["stages"]==20 and J["order"]==12 and D==830216051280000
    assert factorial(12)**6%D==0
    def num(a):
        q=Q(a)*D
        assert q.denominator==1
        return q.numerator
    A=[list(map(num,row)) for row in J["A"]]
    b=list(map(num,J["b"])); c=list(map(sum,A))
    assert c==list(map(num,J["c"])) and all(not any(r[i+1:]) for i,r in enumerate(A))
    span=[[]]
    for d in range(1,12):
        v=act(A,[x**(d-1) for x in c])
        V=[[d*a-x**d for a,x in zip(v,c,strict=True)]]
        V+=[act(A,z) for _,_,z in span[-1]]+[cw(c,z) for _,_,z in span[-1]]
        for e in range(1,d):
            V.extend(cw(x[-1],y[-1]) for x in span[e] for y in span[d-e])
        R=rref(V); L=lcm(*(k for _,k,_ in R))
        assert all([L*a for a in z]==
                   [sum(z[p]*(L//k)*r[i] for p,k,r in R) for i in range(20)]
                   for z in V)
        assert all(not dot(z,b) for _,_,z in R)
        span.append(R)
    assert all((d+1)*dot(b,[x**d for x in c])==D**(d+1) for d in range(12))
    ds=[len(g) for g in span]
    assert ds==[0,0,0,1,2,4,6,10,14,16,17,18]
    scales=[lcm(*(k for _,k,_ in g)) for g in span]
    coeff=[[s//k for _,k,_ in g] for s,g in zip(scales,span,strict=True)]
    bush=13*dot(b,[x**12 for x in c])-D**13
    mix=117*dot(b,cw([x**3 for x in c],act(A,[x**8 for x in c])))-D**13
    assert Q(bush,D**13)==Q(J["scaled_next_bush"])==Q(97351,161663040)
    assert Q(mix,D**13)==Q(-281923,95800320)
    assert 1642*97351+567*(-281923)==1
    print("flag ranks",ds,"mixed next defect",Q(mix,D**13))
    head=r"""module

public import RKCert.ReviewedNative.ScaledIntegerFlagReplay

@[expose] public section

namespace RKResearch.Certified.DIRK12FactorialTwentyFlag
open RKResearch ScaledIntegerFlagReplay FiniteRootedTree
open scoped Matrix
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

"""
    xs=[
      ("rows","Array (Array ℤ)",A),("weights","Array ℤ",b),("clocks","Array ℤ",c),
      ("sizes","Array Nat",ds),
      ("pivots","Array (Array Nat)",[[p for p,_,_ in g] for g in span]),
      ("basisRows","Array (Array (Array ℤ))",[[z for _,_,z in g] for g in span]),
      ("scales","Array ℤ",scales),("coeffs","Array (Array ℤ)",coeff),

    ]
    out=head+"\n".join(f"def {q} : {t} := {arr(a)}\n" for q,t,a in xs)
    out+=f"\ndef D : ℤ := {D}\n"
    out+="""
def packet : Packet 20 where
  a i j := (rows.getD i.val #[]).getD j.val 0
  w i := weights.getD i.val 0
  clock i := clocks.getD i.val 0
  stageScale := D
  weightScale := D
  size k := sizes.getD k 0
  pivot k i := ⟨((pivots.getD k #[]).getD i.val 0)%20, Nat.mod_lt _ (by decide)⟩
  basis k i j := ((basisRows.getD k #[]).getD i.val #[]).getD j.val 0
  spanScale k := scales.getD k 1
  liftCoeff k i := (coeffs.getD k #[]).getD i.val 0

def blockA (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkA packet d)
def blockC (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : Nat) : Bool :=
  (List.finRange (packet.size d)).all fun i =>
    (List.finRange (packet.size e)).all (checkProduct packet d e i)

end RKResearch.Certified.DIRK12FactorialTwentyFlag
"""
    return out

if __name__=="__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("tableau",type=Path);p.add_argument("out",type=Path)
    q=p.parse_args();(q.out/(NAME+"Data.lean")).write_text(build(q.tableau))

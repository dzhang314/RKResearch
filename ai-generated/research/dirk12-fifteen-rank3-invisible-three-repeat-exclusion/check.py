#!/usr/bin/env python3
"""Exact fixed scalar opposing cut arithmetic using only the standard library."""
from itertools import combinations
from pathlib import Path
import sys

P=1013
D=(-42,840,-5040,12600,-13860,5544)
ROOTS=(347,468,507,546,667)
LIVE=(*ROOTS,1)


def add(a,b): return (a+b)%P


def mul(A,B):
    C=[0]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        for j,b in enumerate(B):
            C[i+j]=add(C[i+j],a*b)
    return C


def hull(nodes):
    f=[1]
    for x in nodes: f=mul(f,[-x,1])
    return f


def prim(f):
    return [0]+[a*pow(j+1,-1,P)%P for j,a in enumerate(f)]


def val(f,x):
    s=0
    for a in reversed(f): s=add(a,x*s)
    return s


def matrix(early,shared):
    # The first zero anchor belongs to the late-input hull F, regardless of
    # whether one early label is also still present in the future.
    late=tuple(x for x in LIVE if x not in early)
    F=hull((0,*early))
    G=hull(late if shared is None else (*late,shared))
    return [tuple(val(prim(mul([0]*i+G,prim([0]*j+F))),1)
                  for j in range(2)) for i in range(6-len(G)+1)]


def records():
    for early in combinations(LIVE,3):
        for share in (None,*early):
            A=matrix(early,share)
            assert len(A)==(3 if share is None else 2)
            assert any((a*d-b*c)%P for (a,b),(c,d) in combinations(A,2))
            yield early,share,A


def render_lean(records):
    header="""import Lean

/-! Literal determinant kernel receipts for the exact fixed Lobatto cuts.
The generating Python source reconstructs all entries from monomial integrals. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.InvisibleRepeatSpentCut

set_option maxRecDepth 30000
set_option maxHeartbeats 0

def p : Nat := 1013
def live : List Nat := [347,468,507,546,667,1]

structure Entry where
  early : List Nat
  shared : Option Nat
  rows : List (Nat × Nat)

def detNonzero (r s : Nat × Nat) : Bool :=
  (r.1 * s.2) % p != (s.1 * r.2) % p

def rankTwo (e : Entry) : Bool :=
  e.rows.length == (if e.shared.isSome then 2 else 3) &&
    e.rows.any (fun r => e.rows.any (detNonzero r))

def choose : Nat → List Nat → List (List Nat)
  | 0,_ => [[]]
  | _+1,[] => []
  | n+1,x::xs => (choose n xs).map (x::·) ++ choose (n+1) xs

def coverage : List (List Nat × Option Nat) :=
  (choose 3 live).flatMap fun xs => (none::xs.map some).map (fun z => (xs,z))

def data : List Entry := [
"""
    body=",\n".join(f"  ⟨{list(a)}, {('none' if z is None else 'some '+str(z))}, "
                    f"[{', '.join(f'({u},{v})' for u,v in rows)}]⟩"
                    for a,z,rows in records)
    footer="""]

theorem verifiedCoverage :
    data.map (fun e => (e.early,e.shared)) = coverage ∧ data.length = 80 := by decide +kernel

theorem allRankTwo : data.all rankTwo = true := by decide +kernel

#print axioms verifiedCoverage
#print axioms allRankTwo

end RKResearch.Certified.Graded.OrderTwelveFifteen.InvisibleRepeatSpentCut
"""
    return header+body+footer


def main():
    assert all(P%k for k in range(2,32))
    assert D[-1]%P
    assert tuple(z for z in range(P) if val(D,z)==0)==ROOTS
    rs=list(records())
    assert sum(z is None for _,z,_ in rs)==20
    assert sum(z is not None for _,z,_ in rs)==60
    if len(sys.argv)==2: Path(sys.argv[1]).write_text(render_lean(rs))
    print("mod 1013: rank two in 20 disjoint-role and 60 one-overlap-role matrices")


if __name__=="__main__": main()

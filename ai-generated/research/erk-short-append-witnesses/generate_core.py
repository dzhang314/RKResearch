#!/usr/bin/env python3
"""Produce core Lean replay of actual normalized zero relations (not lower-lemma source)."""
from fractions import Fraction as F
from math import lcm
from pathlib import Path
import argparse,json

def term(t):
    u='.leaf'
    for ch in t:u=f'(.butcher {u} {term(ch)})'
    return u
def string(a):return '['+', '.join(map(str,a))+']'
HEADER="""import Std

namespace RKResearch.Certified.ERKShortAppendCore
inductive Tree where
  | leaf
  | butcher (left right : Tree)

def size : Tree → Nat
  | .leaf => 1
  | .butcher a b => size a + size b

def dot (a b : List Int) : Int := (a.zipWith (· * ·) b).sum

def normProfile (A : List (List Int)) : Tree → List Int
  | .leaf => A.map fun _ => 1
  | .butcher a b =>
      let v := normProfile A b
      (normProfile A a).zipWith (fun x row => x * ((size b : Nat):Int) * dot row v) A

def moment (depth : Nat) (r : List (Tree × Int)) : Int :=
  (r.map fun t => t.2 * ((2520 / (depth + size t.1) : Nat):Int)).sum

def relation (A : List (List Int)) (d : Int) (r : List (Tree × Int)) : List Int :=
  r.foldl (fun v t => v.zipWith (· + ·)
       ((normProfile A t.1).map fun x => t.2 * d ^ (6-size t.1) * x))
    (A.map fun _ => 0)

set_option maxHeartbeats 0
set_option maxRecDepth 20000
"""
def main():
 p=argparse.ArgumentParser();p.add_argument('--sources',type=Path,required=True);p.add_argument('--emit',type=Path,required=True)
 a=p.parse_args();rt=Path(__file__).parent
 text=HEADER
 for i,z in enumerate(["erk-eight-dispersed","erk-eight-rank3-four","erk9-fourteen-rational-triple","erk9-fourteen-field-portfolio"]):
    old=json.loads((a.sources/z/'tableau.json').read_text())
    A=[list(map(F,row))for row in old["A"]];D=lcm(*(v.denominator for row in A for v in row))
    t=json.loads((rt/(z+".json")).read_text());n=len(A);d=t["target"]-t["grade_size_cap"]
    text+=f"\n/- {z} -/\ndef A{i} : List (List Int) :=\n  "+string([string(int(D*v)for v in row)for row in A])
    text+=f"\ndef rel{i} : List (Tree × Int) :=\n  "+string(f"({term(u['tree'])}, {u['coefficient']})"for u in t['terms'])
    text+=f"\n\ntheorem zero_relation{i} : relation A{i} {D} rel{i} = List.replicate {n} 0 := by\n  decide +kernel\n"
    text+=f"theorem future_moment{i} : moment {d} rel{i} ≠ 0 := by\n  decide +kernel\n"
 text+="\nend RKResearch.Certified.ERKShortAppendCore\n"
 a.emit.write_text(text)
if __name__=="__main__":main()

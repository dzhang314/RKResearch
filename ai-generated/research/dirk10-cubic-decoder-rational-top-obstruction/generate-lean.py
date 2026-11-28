#!/usr/bin/env python3
"""Generate the division-free core Lean replay of the 108 residue minors."""
from pathlib import Path
import argparse,json

def li(v):return "["+", ".join(map(str,v))+"]"
def render(src):
    a=[json.loads(l)for l in src.read_text().splitlines()]
    assert len(a)==108
    cases=[]
    for r in a:
        p=r["prime"]
        M=r["residue_rows"]
        assert p in (13,17,19) and len(M)==7 and all(len(v)==7 and all(0<=x<p for x in v)for v in M)
        cases.append("  ("+str(p)+", ["+", ".join(li(row)for row in M)+"])")
    return """import Init

namespace RKResearch.Certified.DIRK10CubicRationalTopArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def splitPivot (ls : List (List Nat)) :
    Option (List Nat × List (List Nat)) :=
  match ls with
  | [] => none
  | row :: rest =>
    if row.headD 0 != 0 then some (row, rest) else
      match splitPivot rest with
      | none => none
      | some (pivot, remain) => some (pivot, row :: remain)

def nonsingular (p : Nat) (fuel : Nat) (M : List (List Nat)) : Bool :=
  match fuel with
  | 0 => M.isEmpty
  | n+1 =>
    match splitPivot M with
    | none => false
    | some (r, rest) =>
      let a := r.headD 0
      let M' := rest.map (fun row => row.tail.zipWith
        (fun x y => (a * x + p*p - row.headD 0 * y) % p) r.tail)
      nonsingular p n M'

def checkMinor (z : Nat × List (List Nat)) : Bool :=
  let (p,M) := z
  (p == 13 || p == 17 || p == 19) && M.length == 7 &&
   M.all (fun row => row.length == 7 && row.all (fun x => x < p)) &&
   nonsingular p 7 M

def data : List (Nat × List (List Nat)) := [
"""+",\n".join(cases)+"""
]

theorem all_augmented_minors : data.length = 108 ∧ data.all checkMinor = true := by decide

#print axioms all_augmented_minors

end RKResearch.Certified.DIRK10CubicRationalTopArithmetic
"""

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("out",type=Path)
    ns=p.parse_args()
    ns.out.write_text(render(Path(__file__).with_name("exact-ranks.jsonl")))

#!/usr/bin/env python3
"""Emit small exact modular unit right-inverses for the Lean arithmetic receipt."""
import pathlib, sys
import check as c
def encode(v):
    out=0
    for i in reversed(v):
        out=13*out+int(i)
    return out
if __name__ == '__main__':
    c.P=13
    c.simple(c.seed(13),9,13); c.simple(c.first_port(9,13),6,13)
    c.simple(c.shifted_second(9,6,13),2,13)
    mats={}
    gates=c.gates(6,2,mats)
    assert len(gates)==37 and all(gates.values())
    out=pathlib.Path(sys.argv[1])
    first=r'''import Lean

/-! Exact auxiliary arithmetic for the open signed-ghost SDIRK9 chart.
    The mathematical chart reduction is separate. Each emitted matrix acts by
    multiplication in the 48-dimensional splitting algebra. The verifier
    checks that the stated candidate gives a right inverse of the unit
    coordinate, using ordinary kernel computation. -/

namespace RKResearch.SDIRK9SignedGhostMod13

private def decode : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, x => x % 13 :: decode n (x / 13)

private def dotMod : List Nat → List Nat → Nat
  | a :: as, b :: bs => (a*b + dotMod as bs) % 13
  | _, _ => 0

private def unitVectorCheck (rows : List Nat) (code : Nat) : Bool :=
  let inv := decode 48 code
  match rows with
  | [] => false
  | r :: rs =>
    (rs.length == 47) &&
    (dotMod (decode 48 r) inv == 1) &&
    rs.all (fun s => dotMod (decode 48 s) inv == 0)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
    with out.open('w') as f:
        f.write(first)
        for i,(n,A) in enumerate(mats.items()):
            inv=c.inv(A)
            assert inv is not None
            z=inv[:,0]
            assert all(((A@z)%13)==c.eye(len(A))[:,0])
            f.write(f'/-- {n} -/\n')
            f.write(f'theorem unitGate{i} : unitVectorCheck\n  [')
            f.write(',\n   '.join(str(encode(row)) for row in A))
            f.write(f']\n  {encode(z)} = true := by decide\n\n')
        f.write('end RKResearch.SDIRK9SignedGhostMod13\n')

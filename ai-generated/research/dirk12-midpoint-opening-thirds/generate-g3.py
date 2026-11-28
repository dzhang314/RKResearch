#!/usr/bin/env python3
"""Packed exact Q36 quotient of the actual G3 opening gate."""
from fractions import Fraction as Qq
from math import lcm
from pathlib import Path
import json,sys,flint as fl
p=Path(sys.argv[1]);out=Path(sys.argv[2])
f=json.loads((p/'field.json').read_text());r=json.loads((p/'projection.json').read_text())
P=fl.fmpz_poly(f['x'])
ys=[Qq(*w) for w in f['y']]
d=lcm(*(q.denominator for q in ys))
Y=fl.fmpz_poly([int(d*q) for q in ys]);X=fl.fmpz_poly([0,1])
assert all(k==0 for i,j,k,c in r['G3'])
ts=[(i,j,c) for i,j,k,c in r['G3']]
N=max(j for i,j,c in ts)
assert N==5
C=sum((c*d**(N-j) * X**i * Y**j for i,j,c in ts),fl.fmpz_poly())
q,rem=divmod(fl.fmpq_poly(C),fl.fmpq_poly(P))
assert not rem and all(w.denominator==1 for w in q)
q=fl.fmpz_poly([int(w) for w in q]);assert C==P*q
norm=lambda p:sum(abs(int(w)) for w in p)
upper=sum(abs(c)*d**(N-j)*norm(Y)**j for i,j,c in ts)+norm(P)*norm(q)
bits=upper.bit_length()+1
fmt=lambda p:'['+','.join(str(w) for w in p)+']'
out.write_text(f'''module

public import RKCert.ReviewedNative.IntegerPolyBivarReplay
public import RKCert.ReviewedNative.DIRK12Q36RealMomentDataBridge

@[expose] public section

/-! Generated exact Q36 quotient of the archived G3 opening gate. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open IntegerPolyRootReplay IntegerPolyRootReplay.Packing
open DIRK12Q36Moments DIRK12MidpointRealInterval DirectedRatBox

def g3Terms : List BivarTerm := [{','.join(f'⟨{i},{j},{c}⟩' for i,j,c in ts)}]
def g3Quot : ZP := {fmt(q)}
def g3Base : Nat := 2^{bits}
def g3Expr : Expr := bivarClear dy 5 g3Terms Y

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem g3_y_degree : ∀ t∈g3Terms, t.j≤5 := by simp [g3Terms]

theorem g3_pack :
    Packing.read (g3Base:Int) g3Expr = eval Q (g3Base:Int)*eval g3Quot (g3Base:Int) := by
  decide +kernel

theorem g3_bound : bound g3Expr+norm Q*norm g3Quot<g3Base := by
  decide +kernel

def g3 (x y : ℝ) : ℝ := bivar g3Terms x y

theorem g3_real_zero {{x : ℝ}} (hx : realX x=0) : g3 x (ratHorner yCoeffs x)=0 := by
  have e := quotient_from_packed x (q_at_real_root hx) g3_pack g3_bound
  have ey : eval Y x=(dy:ℝ)*ratHorner yCoeffs x := by
    rw [y_clear]
    exact eval_clearDen dy _ _ (denomOK_correct y_ok)
  rw [g3Expr,read_bivarClear x _ dy 5 g3Terms Y ey g3_y_degree] at e
  exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by decide +kernel)))

end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.g3_real_zero
''')
print(f'G3 terms={len(ts)}; substituted degree={C.degree()}; quotient degree={q.degree()}; packing bits={bits}; source bytes={out.stat().st_size}')

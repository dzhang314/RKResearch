"""Generate exact linear-system inverse receipts for four negative donor pairs."""
from pathlib import Path
import sympy as S
from sys import path
path.insert(0, str(Path(__file__).resolve().parent.parent))
from gen_symbolic13 import matrixDef
pairs=((6,-9,-11),(7,-1301,-1303),(8,-1501,-1503),(9,-1701,-1703))
source='''module

public import RKCert.ReviewedNative.TwoDonorDense
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-! Exact scalar mixed-moment inverses for the donor pairs used at orders 13,15,17,19.
These identities do not assume the old stage rows are pure. -/
namespace RKResearch.Certified.FixedOneMixedInverses
open TwoDonorDense

private theorem exactTable {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (p : (List.finRange m).all (fun i => (List.finRange n).all (fun j => decide (A i j = B i j))) = true) :
    A = B := by
  ext i j
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp p i (List.mem_finRange i))
    j (List.mem_finRange j))

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
'''
for q,a,b in pairs:
    M=S.Matrix([[S.Rational(1,i+k+1) for k in range(q+1)] for i in range(q-1)]
               +[[S.Integer(t)**k for k in range(q+1)] for t in (a,b)])
    n=q+1;target=2*q+1;name=f'left{target}'
    source+=matrixDef(name,M.inv())
    source+=f'''
theorem mixed{target}_inverse :
    {name} * mixed ℚ {q} ({a}) ({b}) = (1 : Matrix (Fin {n}) (Fin {n}) ℚ) :=
  exactTable _ _ (by decide +kernel)

'''
source+='#print axioms mixed19_inverse\nend RKResearch.Certified.FixedOneMixedInverses\n'
Path(__file__).with_name('FixedOneMixedInverses.lean').write_text(source)

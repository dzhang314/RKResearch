module

public import RKCert.ReviewedNative.ERKTaggedHorizonSupport

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Terminal E4 profile before any Newton, shape, or off-hull proof -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

noncomputable abbrev terminalCleanHull (A : Matrix (Fin 10) (Fin 10) K) : K[X] :=
  nodalHull ((cleanKnots A).erase 1)

/-- The actual E4 terminal column, normalizing its pure part to the literal
nonterminal clean hull. This is independent of any off curve degree or
nonvanishing, any clean primitive shape, and any Newton body. -/
theorem terminal_profile_of_unitNine (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2)
    (unitNine : Reverse.coordinate (K:=K) (9:Fin 10)∈treeSpace A 4)
    (gNine : g A (Fin.last 9)=0) (cNine : nodes A (Fin.last 9)=1)
    (cleanFive : (cleanKnots A).card=5) :
    ∃ R : K[X], R.natDegree≤2 ∧ (terminalCleanHull A).eval 1≠0 ∧
      evalNodes A (terminalCleanHull A)+diag (g A) (evalNodes A R)=
        (terminalCleanHull A).eval 1 • Pi.single (Fin.last 9) 1 := by
  let t : Fin 10 := Fin.last 9
  let S := (cleanKnots A).erase 1
  let H := terminalCleanHull A
  have u : Pi.single t (1:K)∈treeSpace A 4 := by
    rw [←coordinate_as_single]
    exact unitNine
  rw [treeSpace_coeff_sup ho (q:=4) (by decide),Submodule.mem_sup] at u
  obtain ⟨_,⟨a,rfl⟩,v,hv,physical⟩ := u
  obtain ⟨R0,dR0,r0⟩ := band_iff.mp (hF ▸ hv)
  let Q0 := Polynomial.ofFn 5 a
  have dQ0 : Q0.natDegree≤4 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
  have line0 : evalNodes A Q0+diag (g A) (evalNodes A R0)=Pi.single t 1 := by
    rw [show evalNodes A Q0=coeffEval A 4 a from ofFn_eval A 4 a,←r0]
    exact physical
  have one : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨t,gNine,cNine⟩
  have cd : S.card=4 := by
    change ((cleanKnots A).erase 1).card=4
    rw [Finset.card_erase_of_mem one,cleanFive]
  have hd : H.natDegree=4 := (natDegree_nodalHull S).trans cd
  have hn : H.eval 1≠0 :=
    LobattoEight.nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)
  have qeq : Q0=C ((H.eval 1)⁻¹)*H := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (cleanKnots A) ?_ ?_
    · intro x hx
      by_cases x1 : x=1
      · subst x
        rw [eval_mul,eval_C,inv_mul_cancel₀ hn]
        have hAt := profile_on_eval Q0 R0 line0 gNine
        rw [cNine] at hAt
        simpa [t] using hAt
      · obtain ⟨j,gj,jc⟩ := mem_cleanKnots.mp hx
        have nj : j≠t := fun z=> x1 (jc.symm.trans ((congrArg (nodes A) z).trans cNine))
        have hAt := profile_on_eval Q0 R0 line0 gj
        have qAt : Q0.eval x=0 := by simpa [jc,nj,Ne.symm nj] using hAt
        have hAt0 : H.eval x=0 := nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨x1,hx⟩)
        rw [qAt,eval_mul,eval_C,hAt0,mul_zero]
    · rw [cleanFive]
      exact (max_le dQ0 ((natDegree_C_mul_le _ _).trans hd.le)).trans_lt (by decide)
  refine ⟨C (H.eval 1)*R0,(natDegree_C_mul_le _ _).trans dR0,hn,?_⟩
  ext j
  have jr := congrFun line0 j
  let terminalVector : Fin 10 → K := Pi.single t (1:K)
  change Q0.eval (nodes A j)+g A j*R0.eval (nodes A j)=terminalVector j at jr
  change H.eval (nodes A j)+g A j*(C (H.eval 1)*R0).eval (nodes A j)=
    H.eval 1*(terminalVector j)
  have sc : H.eval 1*Q0.eval (nodes A j)=H.eval (nodes A j) := by
    rw [qeq,eval_mul,eval_C,←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  rw [eval_mul,eval_C,←sc]
  linear_combination (H.eval 1) * jr

end RKResearch.Certified.Graded.FourOffNewton

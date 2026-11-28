module

public import RKCert.ReviewedNative.DIRK12Midpoint21Data
import Mathlib.Tactic.Ring

@[expose] public section

/-! The fixed compact rational checks: block constancy, one even-power
primitive decomposition per degree, and scalar annihilation of the
paid profile monomials. All computed equalities are kernel decisions. -/
namespace RKResearch.Certified.DIRK12Midpoint21

open RKResearch Graded
open scoped Matrix BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 30000

def eqV (u v : V) : Bool :=
  (List.finRange 21).all fun i => decide (u i=v i)

def eqVI (u v : VI) : Bool :=
  (List.finRange 21).all fun i => decide (u i=v i)

theorem from_eqV {u v : V} (h : eqV u v = true) : u=v :=
  funext fun i => of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

theorem from_eqVI {u v : VI} (h : eqVI u v = true) : u=v :=
  funext fun i => of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

theorem act_eq (v : V) : act v=mat matrix v := by
  funext i
  simp only [act,sumFin_eq,mat_apply,Matrix.mulVec_apply_eq_sum]

theorem output_eq (v : V) : output v=row weights v := by
  simp only [output,sumFin_eq,row_apply,dotProduct]

theorem actI_eq (v : VI) : actI v=integerA *ᵥ v := by
  funext i
  simp only [actI,sumFin_eq,Matrix.mulVec_apply_eq_sum]

theorem outputI_eq (v : VI) : outputI v=integerB ⬝ᵥ v := by
  simp only [outputI,sumFin_eq,dotProduct]

private theorem check_clock : eqV (act 1) clock=true := by decide +kernel

theorem node_eq : nodes matrix=clock := by
  change mat matrix (1:V)=clock
  rw [←act_eq]
  exact from_eqV check_clock

private theorem check_block :
    (List.finRange 21).all (fun i => (List.finRange 21).all fun j =>
      decide (matrix i j=0 ∨ hSq i=hSq j)) = true := by decide +kernel

theorem block (i j : Fin 21) : matrix i j=0 ∨ hSq i=hSq j :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp check_block i (List.mem_finRange i)) j (List.mem_finRange j))

private theorem check_reads :
    (List.range 11).all (fun d =>
      eqV (((d+1:Nat):ℚ) • act (clock^d)) (clock^(d+1)+tail d))=true := by
  decide +kernel

theorem normal_read (d : Nat) (hd : d+1 < 12) :
    ((d+1:Nat):ℚ) • mat matrix (clock^d)=clock^(d+1)+tail d := by
  rw [←act_eq]
  exact from_eqV (List.all_eq_true.mp check_reads d (List.mem_range.mpr (by omega)))

private theorem check_silent :
    (List.range 5).all (fun k => (List.range (12-2*(k+1))).all fun d =>
      decide (output (gen (k+1) d)=0)) = true := by decide +kernel

theorem monomial_silent (k d : Nat) (hk : 1 ≤ k) (h : 2*k+d < 12) :
    row weights (gen k d)=0 := by
  let r := k-1
  have r1 : r+1=k := by dsimp [r]; omega
  have hr : r < 5 := by dsimp [r]; omega
  have hd : d < 12-2*(r+1) := by omega
  have t := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp check_silent r (List.mem_range.mpr hr)) d (List.mem_range.mpr hd))
  rw [output_eq,r1] at t
  exact t

private theorem check_scalar :
    (List.range 12).all (fun d => decide (((d+1:Nat):ℚ)*output (clock^d)=1))=true := by
  decide +kernel

theorem scalar_paid (d : Nat) (hd : d < 12) :
    ((d+1:Nat):ℚ)*row weights (clock^d)=1 := by
  rw [←output_eq]
  exact of_decide_eq_true (List.all_eq_true.mp check_scalar d (List.mem_range.mpr hd))

private theorem integer_scales_checked :
    (List.finRange 21).all (fun i =>
      (List.finRange 21).all fun j =>
        decide ((integerA i j:ℚ)=(stageScale:ℚ)*matrix i j))=true ∧
      (List.finRange 21).all (fun i =>
        decide ((integerB i:ℚ)=(weightScale:ℚ)*weights i))=true := by
  decide +kernel

theorem integerA_Q : integerA.map (Int.castRingHom ℚ)=(stageScale:ℚ) • matrix := by
  funext i j
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp integer_scales_checked.1 i (List.mem_finRange i)) j (List.mem_finRange j))

theorem integerB_Q : Int.castRingHom ℚ ∘ integerB=(weightScale:ℚ) • weights := by
  funext i
  exact of_decide_eq_true (List.all_eq_true.mp integer_scales_checked.2 i (List.mem_finRange i))

private theorem int_tall_checked :
    eqVI (tallView 0) (1:VI)=true ∧
      (List.range 12).all (fun d => eqVI (actI (tallView d)) (tallView (d+1)))=true := by
  decide +kernel

theorem tall_zero : tallView 0=1 := from_eqVI int_tall_checked.1

theorem tall_step (d : Nat) (h : d < 12) :
    integerA *ᵥ tallView d=tallView (d+1) := by
  rw [←actI_eq]
  exact from_eqVI (List.all_eq_true.mp int_tall_checked.2 d (List.mem_range.mpr h))

theorem tall_at (d : Nat) (h : d≤12) : integerA^d *ᵥ (1:VI)=tallView d := by
  induction d with
  | zero => rw [pow_zero,Matrix.one_mulVec,tall_zero]
  | succ n ih =>
    rw [pow_succ',←Matrix.mulVec_mulVec,ih (by omega),tall_step n (by omega)]

theorem integer_tall_defect :
    (1024:ℤ)*(Int.ofNat (Nat.factorial 13)*outputI (tallView 12)-
      weightScale*stageScale^12)=(-231)* (weightScale*stageScale^12) := by
  decide +kernel

end RKResearch.Certified.DIRK12Midpoint21

#print axioms RKResearch.Certified.DIRK12Midpoint21.normal_read
#print axioms RKResearch.Certified.DIRK12Midpoint21.monomial_silent
#print axioms RKResearch.Certified.DIRK12Midpoint21.integer_tall_defect

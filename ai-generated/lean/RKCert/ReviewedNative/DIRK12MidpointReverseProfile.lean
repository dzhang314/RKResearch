module

public import RKCert.ReviewedNative.DIRK12MidpointReverseMasses
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! The exact nine-label profile, pushed onto the real physical rows.
The two reversed repeated entries really are different rows: the
barycentric amplitude at their common label is put at row 11 only. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded DIRK12MidpointForward DIRK12MidpointForward.Opening
open DIRK12MidpointForward.Late DIRK12MidpointRealInterval DirectedRatBox
open scoped BigOperators Matrix

def representative : Fin 9 → Fin 15 := ![0,5,6,7,8,9,11,12,10]

@[simp] theorem represented_tag (i : Fin 9) : stageTag (representative i)=i.succ := by
  fin_cases i <;> decide

theorem representative_nonghost (i : Fin 9) : ¬ ghostRow (representative i) := by
  fin_cases i <;> decide

theorem representative_inj : Function.Injective representative := by
  intro i j e
  apply Fin.succ_injective 9
  simpa only [represented_tag] using congrArg stageTag e

noncomputable def baryVector (x f : ℝ) (i : Fin 15) : ℝ :=
  ∑ j : Fin 9, if representative j=i then rho x f * liveWeight x f j else 0

theorem bary_at_rep (x f : ℝ) (j : Fin 9) :
    baryVector x f (representative j)=rho x f*liveWeight x f j := by
  simp [baryVector,representative_inj.eq_iff]

theorem bary_absent (x f : ℝ) (i : Fin 15) (h : ∀ j, representative j≠i) :
    baryVector x f i=0 := Finset.sum_eq_zero (fun j _ => ite_eq_right (h j))

theorem bary_hidden (x f : ℝ) (g : Fin 4) :
    baryVector x f (DIRK12MidpointForward.hidden g)=0 := by
  apply bary_absent
  intro i e
  exact representative_nonghost i (e ▸ ghost_hidden g)

theorem bary_13 (x f : ℝ) : baryVector x f 13=0 := by
  apply bary_absent
  intro i
  fin_cases i <;> decide

theorem bary_terminal (x f : ℝ) : baryVector x f terminal=0 := by
  apply bary_absent
  intro i
  fin_cases i <;> decide

theorem bary_row (x f : ℝ) (w : V15 ℝ) :
    row (baryVector x f) w=
      rho x f*(∑ j : Fin 9, liveWeight x f j*w (representative j)) := by
  rw [row_apply,dotProduct]
  simp only [baryVector,Finset.sum_mul]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp
  ring

theorem bary_sum (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    (∑ i, baryVector x f i)=0 := by
  have h := Bary.annihilate_reflected (liveNode x f) (liveNode_distinct hx hf) 0 (by decide)
  simp only [pow_zero,mul_one] at h
  change (∑ i, liveWeight x f i)=0 at h
  have e := bary_row x f (1:V15 ℝ)
  rw [row_apply,dotProduct] at e
  simpa [h] using e

noncomputable def zeroHead (x f : ℝ) : Feed ℝ := fiveFeed x f (fun _ _ => 0)

noncomputable def groupedAmplitude (x f : ℝ) (i : Fin 6) : ℝ :=
  let ix := visible (Physical.earlyTarget i)
  baryVector x f ix / ((d x f)^4*physicalWeight x f ix)

noncomputable def exactData (x f : ℝ) : Physical.Data ℝ := data x f (groupedAmplitude x f)

noncomputable def assembled (x f : ℝ) : Feed ℝ := installed x f (groupedAmplitude x f)

noncomputable def profileG (x f : ℝ) : V15 ℝ :=
  Physical.G (zeroHead x f) (exactData x f)

noncomputable def profileH (x f : ℝ) : V15 ℝ :=
  Physical.H (zeroHead x f) (exactData x f)

theorem assembled_geom (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Physical.Geom (zeroHead x f) (exactData x f) := installed_geom x f _ hx hf

theorem actual_H_eq (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    profileH x f=baryVector x f := by
  have hG := assembled_geom x f hx hf
  let P := zeroHead x f
  let D := exactData x f
  have vis (i : Fin 10) : Physical.H P D (visible i)=baryVector x f (visible i) := by
    rw [Physical.H_visible,Physical.hv]
    revert i
    apply Physical.target_cases
    · intro i
      rw [Physical.ampl_early]
      have g := mul_ne_zero (pow_ne_zero 4 hG.d0) (hG.bNZ (Physical.earlyTarget i))
      change (d x f)^4*physicalWeight x f (visible (Physical.earlyTarget i))*
        (baryVector x f (visible (Physical.earlyTarget i))/
          ((d x f)^4*physicalWeight x f (visible (Physical.earlyTarget i))))=_
      change (d x f)^4*physicalWeight x f (visible (Physical.earlyTarget i))≠0 at g
      rw [←mul_div_assoc,mul_div_cancel_left₀ _ g]
    · intro i
      rw [Physical.ampl_seed]
      fin_cases i
      · change (d x f)^4*(cardinalWeight x f 7/2)*(Seed.k (r x f)*Seed.delta)=
          baryVector x f (representative 6)
        rw [bary_at_rep,rho_at_d x f hx hf,mass_d,Seed.delta]
        ring
      · change (d x f)^4*cardinalWeight x f 8*(Seed.sigma*Seed.p (r x f))=
          baryVector x f (representative 7)
        rw [bary_at_rep,rho,mass_v]
        ring
      · change (d x f)^4*(cardinalWeight x f 7/2)*0=baryVector x f 13
        rw [bary_13,mul_zero]
    · rw [Physical.ampl_terminal,mul_zero,Physical.physical_term,bary_terminal]
  have gh (i : Fin 4) :
      Physical.H P D (DIRK12MidpointForward.hidden i)=
        baryVector x f (DIRK12MidpointForward.hidden i) := by
    rw [Physical.H_hidden,bary_hidden]
  have o := Physical.sum_eq_origin (Physical.H P D) (baryVector x f)
    ((Physical.H_sum P D).trans (bary_sum x f hx hf).symm) gh vis
  funext i
  exact stage_cases (P:=fun i => Physical.H P D i=baryVector x f i) o gh vis i

theorem assembled_real_nodes (x f : ℝ) (i : Fin 15) (hi : ¬ghostRow i) :
    1-nodes (assembled x f).tableau i=site x f (stageTag i) := by
  rw [assembled,installed,Physical.nodes_eq,←(fiveFeed x f (fun _ _=>0)).nodes_tableau]
  exact real_nodes x f _ _ _ _ i hi

theorem actual_H_silent (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
    (m : Nat) (hm : m≤7) :
    row (profileH x f) ((nodes (assembled x f).tableau)^m)=0 := by
  rw [actual_H_eq x f hx hf,bary_row]
  have eq (j : Fin 9) : ((nodes (assembled x f).tableau)^m) (representative j)=
      (1-liveNode x f j)^m := by
    have g := assembled_real_nodes x f (representative j) (representative_nonghost j)
    rw [represented_tag] at g
    rw [Pi.pow_apply]
    congr 1
    change nodes (assembled x f).tableau (representative j)=1-site x f j.succ
    linear_combination -g
  simp only [eq,liveWeight]
  rw [Bary.annihilate_reflected (liveNode x f) (liveNode_distinct hx hf) m (by omega),mul_zero]

theorem actual_G_silent (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) (m : Nat) :
    row (profileG x f) ((nodes (assembled x f).tableau)^m)=0 := by
  change row (physicalPair (Physical.paired (zeroHead x f) (exactData x f)))
    ((nodes (assembled x f).tableau)^m)=0
  rw [physicalPair_read]
  have g := Physical.same_seed_clocks _ _ (assembled_geom x f hx hf)
  change nodes (assembled x f).tableau 11=nodes (assembled x f).tableau 13 at g
  simp [g]

theorem actual_pair_identity (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    mat (assembled x f).tableau.transpose (profileG x f)=
      (d x f/2) • profileG x f+profileH x f :=
  installed_pair x f (groupedAmplitude x f) hx hf

theorem actual_pair_forward (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
    (m : Nat) (hm : m≤7) :
    DualSupport12.forward (assembled x f).tableau m 11=
      DualSupport12.forward (assembled x f).tableau m 13 := by
  have g := assembled_geom x f hx hf
  exact paired_primitive_equal (assembled x f).tableau (Physical.paired _ _) (d x f/2)
    (profileH x f) m (Physical.paired_nz _ _ g) (Physical.same_seed_clocks _ _ g)
    (actual_H_silent x f hx hf m hm) (actual_pair_identity x f hx hf)

end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_H_eq
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_H_silent
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_pair_identity
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_pair_forward

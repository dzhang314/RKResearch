module

public import RKCert.ReviewedNative.PhysicalLabelOrbit
public import RKCert.ReviewedNative.ClockBlockDetection
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

@[expose] public section

/-! # Finite coordinate algebras described by their actual label fibres

The native weighted-label range and its measured rank are reused. A
label slice is earned by finitely many masks of genuine elements of the
submodule, with the supplied support vector as their initial multiplier.
No infinite-field or generic-element argument is needed. -/
namespace RKResearch.Certified.Graded.PhysicalCensus

open scoped Classical BigOperators
noncomputable section
variable {K α : Type*} [Field K] {s : ℕ}
variable {V : Submodule K (Fin s→K)} {lab : Fin s→α} {e : Fin s→K}
set_option maxHeartbeats 600000

/-- Construct the whole literal class slice by masking inside the
given coordinate algebra, not by choosing a compressed representative. -/
theorem labelSlice_mem_of_coordinate_separation
    (closed : ∀ u∈V, ∀ v∈V, u*v∈V) (inE : e∈V)
    (agree : ∀ u∈V, ∀ i j, e i≠0 → e j≠0 → lab i=lab j → u i=u j)
    (separate : ∀ i j, e i≠0 → e j≠0 → lab i≠lab j → ∃u∈V,u i≠u j)
    (i : Fin s) (ei : e i≠0) : labelSlice lab e (lab i)∈V := by
  have pick (j : Fin s) : ∃ u∈V, e j≠0 → lab j≠lab i → u i≠u j := by
    by_cases yes : e j≠0 ∧ lab j≠lab i
    · obtain ⟨v,hv,ne⟩ := separate i j ei yes.1 (fun eq => yes.2 eq.symm)
      exact ⟨v,hv,fun _ _=>ne⟩
    · exact ⟨0,V.zero_mem,fun nz ne=>(yes ⟨nz,ne⟩).elim⟩
  choose u uV uno using pick
  let D (j : Fin s) : Fin s→K := fun k=>if u j k=u j i then 1 else 0
  have step (j : Fin s) (v : Fin s→K) (hv : v∈V) : D j*v∈V :=
    clock_function_mem (c:=u j) (fun z hz => closed _ (uV j) _ hz)
      (fun x=>if x=u j i then 1 else 0) hv
  have inside (S : Finset (Fin s)) : (∏ j∈S,D j)*e∈V := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty,one_mul] using inE
    | @insert j S no ih =>
      rw [Finset.prod_insert no,mul_assoc]
      exact step j _ ih
  have eq : (∏ j : Fin s,D j)*e=labelSlice lab e (lab i) := by
    ext k
    rw [labelSlice_apply,Pi.mul_apply,Finset.prod_apply]
    by_cases ek : e k=0
    · simp only [ek,mul_zero,ite_self]
    · by_cases same : lab k=lab i
      · have all (j : Fin s) (_ : j∈Finset.univ) : D j k=1 :=
          if_pos (agree (u j) (uV j) k i ek ei same)
        rw [Finset.prod_eq_one all,one_mul,if_pos same]
      · have one : D k k=0 := if_neg (Ne.symm (uno k ek same))
        have prod0 : (∏ j : Fin s, D j k) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) one
        rw [prod0, zero_mul, if_neg same]
  rw [←eq]
  exact inside Finset.univ

/-- The native label range is exactly the supplied coordinate
submodule when its support mask is 0/1, and labels are precisely the
indistinguishable classes on that support. -/
theorem labelOrbit_eq_of_coordinate_separation
    (closed : ∀ u∈V, ∀ v∈V, u*v∈V) (inE : e∈V)
    (ones : ∀ i,e i≠0 → e i=1)
    (off : ∀ v∈V, ∀ i,e i=0 → v i=0)
    (agree : ∀ v∈V, ∀ i j,e i≠0 → e j≠0 → lab i=lab j → v i=v j)
    (separate : ∀ i j,e i≠0 → e j≠0 → lab i≠lab j → ∃v∈V,v i≠v j) :
    labelOrbit lab e=V := by
  let rep (a : activeLabels lab e) : Fin s :=
    Classical.choose (mem_activeLabels.mp a.property)
  have has (a : activeLabels lab e) : e (rep a)≠0 ∧ lab (rep a)=a.val :=
    Classical.choose_spec (mem_activeLabels.mp a.property)
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    change (∑ a : activeLabels lab e, f a • labelSlice lab e a.val)∈V
    refine V.sum_mem (fun a _=>V.smul_mem _ ?_)
    rw [←(has a).2]
    exact labelSlice_mem_of_coordinate_separation closed inE agree separate _ (has a).1
  · intro v hv
    let f (a : activeLabels lab e) := v (rep a)
    refine ⟨f,?_⟩
    ext i
    by_cases ei : e i=0
    · rw [labelCombination_eval_of_off lab e f ei,off _ hv i ei]
    · let a : activeLabels lab e := ⟨lab i,mem_activeLabels.mpr ⟨i,ei,rfl⟩⟩
      calc
        _ = f a * e i := labelCombination_eval_of_live lab e f ei
        _ = f a * 1 := congrArg (fun z : K => f a * z) (ones i ei)
        _ = f a := mul_one _
        _ = v i := agree v hv (rep a) i (has a).1 ei (has a).2

end
end RKResearch.Certified.Graded.PhysicalCensus

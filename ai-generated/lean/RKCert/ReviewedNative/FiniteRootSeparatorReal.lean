module

public import RKCert.ReviewedNative.FiniteRootSeparator
public import Mathlib.Analysis.Polynomial.Order

@[expose] public section

/-! # Real instance of the selected-polynomial root source -/
namespace RKCert.ReviewedNative.FiniteRootSeparator

open Polynomial Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem unit_root_source_real (e : K →+* ℝ) (ord : StrictMono e) (P : K[X]) :
    UnitRootSource e P := by
  intro a b _ _ ab opposite
  let F := P.map e
  have ab' := ord ab
  have get (h : (0:ℝ) ∈ F.eval '' Icc (e a) (e b))
      (ane : F.eval (e a) ≠ 0) (bne : F.eval (e b) ≠ 0) :
      ∃ r : ℝ, e a<r ∧ r<e b ∧ F.IsRoot r := by
    obtain ⟨r,hr,h0⟩ := h
    have har : e a ≠ r := by
      intro eq
      rw [← eq] at h0
      exact ane h0
    have hrb : r ≠ e b := by
      intro eq
      rw [eq] at h0
      exact bne h0
    refine ⟨r,lt_of_le_of_ne hr.1 har,lt_of_le_of_ne hr.2 hrb,?_⟩
    exact h0
  have pos {x : K} (h : 0<P.eval x) : 0<F.eval (e x) := by
    simpa only [F,eval_on_base,map_zero] using ord h
  have neg {x : K} (h : P.eval x<0) : F.eval (e x)<0 := by
    simpa only [F,eval_on_base,map_zero] using ord h
  rcases opposite with ⟨ap,bn⟩ | ⟨an,bp⟩
  · have pa := pos ap
    have nb := neg bn
    exact get (intermediate_value_Icc' ab'.le F.continuous.continuousOn ⟨nb.le,pa.le⟩) pa.ne' nb.ne
  · have na := neg an
    have pb := pos bp
    exact get (intermediate_value_Icc ab'.le F.continuous.continuousOn ⟨na.le,pb.le⟩) na.ne pb.ne'

theorem unit_root_source_real_self (P : ℝ[X]) :
    UnitRootSource (RingHom.id ℝ) P :=
  unit_root_source_real (RingHom.id ℝ) strictMono_id P

end RKCert.ReviewedNative.FiniteRootSeparator

module

public import RKCert.ReviewedNative.WeakFiveSoleInnerCapEndpoint
public import RKCert.ReviewedNative.ERKOrder16WeakFiveSoleInnerStructural

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Native weak-five SoleInner cap assembly, conditional on paid chronology

The only remaining premise of this adapter is the left-oriented chronology
and adjacent sign alternation at the three actual unit marks. The
published source proof earns that premise by true stopped-side
erasure; this file does not assert a kernel replay of that producer. -/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.WeakFiveSoleInner
open RKCert.ReviewedNative.WeakFiveSoleInnerUniform

universe u
noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The one outstanding producer of the uniform-density route. These are
chronological signs at the original marks, not assumptions about fitted
corner roots or signed quadrature masses. -/
structure PaidInnerChronology (e u h z r₀ r₁ r₂ : K) : Prop where
  zh : z < h
  hu : h < u
  first : (profile e r₀ r₁ r₂).eval z * (profile e r₀ r₁ r₂).eval h < 0
  second : (profile e r₀ r₁ r₂).eval h * (profile e r₀ r₁ r₂).eval u < 0

private theorem sign_bands {e r₀ r₁ r₂ x : K}
    (e0 : e < 0) (x0 : 0 < x) (r01 : r₀ < r₁) (r12 : r₁ < r₂)
    (live : (profile e r₀ r₁ r₂).eval x ≠ 0) :
    (x < r₀ ∧ (profile e r₀ r₁ r₂).eval x < 0) ∨
    (r₀ < x ∧ x < r₁ ∧ 0 < (profile e r₀ r₁ r₂).eval x) ∨
    (r₁ < x ∧ x < r₂ ∧ (profile e r₀ r₁ r₂).eval x < 0) ∨
    (r₂ < x ∧ 0 < (profile e r₀ r₁ r₂).eval x) := by
  have pe : 0 < x-e := sub_pos.mpr (e0.trans x0)
  have ev : (profile e r₀ r₁ r₂).eval x = (x-e)*((x-r₀)*(x-r₁)*(x-r₂)) := by
    simp only [profile,cubic,eval_mul,eval_sub,eval_X,eval_C]
  have n₀ : x≠r₀ := fun k => live (ev.trans (by simp only [k, sub_self, zero_mul, mul_zero]))
  have n₁ : x≠r₁ := fun k => live (ev.trans (by simp only [k, sub_self, zero_mul, mul_zero]))
  have n₂ : x≠r₂ := fun k => live (ev.trans (by simp only [k, sub_self, zero_mul, mul_zero]))
  by_cases a : x < r₀
  · exact Or.inl ⟨a,by
      rw [ev]
      exact mul_neg_of_pos_of_neg pe (mul_neg_of_pos_of_neg
        (mul_pos_of_neg_of_neg (sub_neg.mpr a) (sub_neg.mpr (a.trans r01)))
        (sub_neg.mpr (a.trans (r01.trans r12))))⟩
  have a' : r₀ < x := lt_of_le_of_ne (le_of_not_gt a) n₀.symm
  by_cases b : x < r₁
  · exact Or.inr (Or.inl ⟨a',b,by
      rw [ev]
      exact mul_pos pe (mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg (sub_pos.mpr a') (sub_neg.mpr b))
        (sub_neg.mpr (b.trans r12)))⟩)
  have b' : r₁ < x := lt_of_le_of_ne (le_of_not_gt b) n₁.symm
  by_cases c : x < r₂
  · exact Or.inr (Or.inr (Or.inl ⟨b',c,by
      rw [ev]
      exact mul_neg_of_pos_of_neg pe (mul_neg_of_pos_of_neg
        (mul_pos (sub_pos.mpr a') (sub_pos.mpr b')) (sub_neg.mpr c))⟩))
  have c' : r₂ < x := lt_of_le_of_ne (le_of_not_gt c) n₂.symm
  exact Or.inr (Or.inr (Or.inr ⟨c',by
    rw [ev]
    exact mul_pos pe (mul_pos (mul_pos (sub_pos.mpr a') (sub_pos.mpr b')) (sub_pos.mpr c'))⟩))

private theorem two_phase_orders {a e u h z r₀ r₁ r₂ : K}
    (P : OrientedPorts a e u h z r₀ r₁ r₂) (T : PaidInnerChronology e u h z r₀ r₁ r₂) :
    (r₀ < z ∧ z < r₁ ∧ r₁ < h ∧ h < r₂ ∧ r₂ < u) ∨
      (z < r₀ ∧ r₀ < h ∧ h < r₁ ∧ r₁ < u ∧ u < r₂) := by
  let q := profile e r₀ r₁ r₂
  have pos {x : K} (x0 : 0 < x) (qp : 0 < q.eval x) : (r₀ < x ∧ x < r₁) ∨ r₂ < x := by
    rcases sign_bands P.eNeg x0 P.roots01 P.roots12 qp.ne' with ⟨_,bad⟩ | ⟨b,c,_⟩ | ⟨_,_,bad⟩ | ⟨a,_⟩
    · exact (not_lt_of_ge qp.le bad).elim
    · exact Or.inl ⟨b,c⟩
    · exact (not_lt_of_ge qp.le bad).elim
    · exact Or.inr a
  have neg {x : K} (x0 : 0 < x) (qn : q.eval x < 0) : x < r₀ ∨ (r₁ < x ∧ x < r₂) := by
    rcases sign_bands P.eNeg x0 P.roots01 P.roots12 qn.ne with ⟨a,_⟩ | ⟨_,_,bad⟩ | ⟨b,c,_⟩ | ⟨_,bad⟩
    · exact Or.inl a
    · exact (not_lt_of_ge qn.le bad).elim
    · exact Or.inr ⟨b,c⟩
    · exact (not_lt_of_ge qn.le bad).elim
  have zh := T.zh
  have hu := T.hu
  rcases mul_neg_iff.mp T.first with ⟨zp,hn⟩ | ⟨zn,hp⟩
  · have up : 0 < q.eval u := ((mul_neg_iff.mp T.second).resolve_left (fun x =>
      not_lt_of_ge hn.le x.1)).2
    rcases pos P.zUnit.1 zp with ⟨z₀,z₁⟩ | z₂ <;>
      rcases neg P.hUnit.1 hn with h₀ | ⟨h₁,h₂⟩ <;>
      rcases pos P.uUnit.1 up with ⟨u₀,u₁⟩ | u₂
    all_goals first
      | exact Or.inl ⟨z₀,z₁,h₁,h₂,u₂⟩
      | exfalso; linarith [P.roots01,P.roots12]
  · have un : q.eval u < 0 := ((mul_neg_iff.mp T.second).resolve_right (fun x =>
      not_lt_of_ge hp.le x.1)).2
    rcases neg P.zUnit.1 zn with z₀ | ⟨z₁,z₂⟩ <;>
      rcases pos P.hUnit.1 hp with ⟨h₀,h₁⟩ | h₂ <;>
      rcases neg P.uUnit.1 un with u₀ | ⟨u₁,u₂⟩
    all_goals first
      | exact Or.inr ⟨z₀,h₀,h₁,u₁,u₂⟩
      | exfalso; linarith [P.roots01,P.roots12]

private theorem consume_phase {a e u h z r₀ r₁ r₂ : K}
    (M : RankedPacket a e u h z r₀ r₁ r₂) (p : Phase) (v : Fin 6 → K)
    (vOrd : StrictMono v) (vUnit : ∀ i, v i ∈ Set.Ioo (0 : K) 1)
    (vRoot : ∀ i, (cubic r₀ r₁ r₂*((X-C z)*(X-C h)*(X-C u))).IsRoot (v i))
    (vz : v p.zIndex=z)
    (other : cubic r₀ r₁ r₂=(X-C (v (p.rootIndex 0)))*(X-C (v (p.rootIndex 1)))*
      (X-C (v (p.rootIndex 2)))) : False := by
  let B := M.ports
  have a0 := B.ae.trans B.eNeg
  have posA := neg_pos.mpr a0
  have ratio : e/a=(-e)/(-a) := by field_simp [a0.ne] <;> ring
  have lo : (2 : K)/3≤e/a := by
    rw [ratio]
    exact ((lt_div_iff₀ posA).mpr M.exteriorScale.1).le
  have hi : e/a≤(6 : K)/7 := by
    rw [ratio]
    exact ((div_lt_iff₀ posA).mpr M.exteriorScale.2).le
  have mono : (cubic r₀ r₁ r₂).Monic :=
    ((monic_X_sub_C r₀).mul (monic_X_sub_C r₁)).mul (monic_X_sub_C r₂)
  apply no_paid_sole_inner_phase p a0 B.eNeg B.zUnit.2 lo hi
    (show profile e r₀ r₁ r₂=(X-C e)*cubic r₀ r₁ r₂ from rfl)
    mono (WeakFiveSoleInner.cubic_degree _ _ _) _ B.reverseFirst B.reverseSecond
    v vOrd vUnit vRoot vz other
  intro H dH
  have k := B.global H dH
  have e : unitWeight K*(X-C a)*profile e r₀ r₁ r₂*((X-C z)*(X-C h)*(X-C u))*H =
      X*(1-X)*(profile e r₀ r₁ r₂*rawFourHull u a h z)*H := by
    simp only [unitWeight,rawFourHull]
    ring
  rwa [e]

/-- The interval argument excludes the complete physical left branch
once its three live marks have the earned right-side chronology. -/
theorem no_ranked_sole_inner_with_paid_chronology {a e u h z r₀ r₁ r₂ : K}
    (M : RankedPacket a e u h z r₀ r₁ r₂) (T : PaidInnerChronology e u h z r₀ r₁ r₂) : False := by
  let B := M.ports
  rcases two_phase_orders B T with ⟨a₀,a₁,a₂,a₃,a₄⟩ | ⟨b₀,b₁,b₂,b₃,b₄⟩
  · let v : Fin 6 → K := ![r₀,z,r₁,h,r₂,u]
    apply consume_phase M .A v _ _ _ _ _
    · refine Fin.strictMono_iff_lt_succ.mpr ?_
      intro i
      fin_cases i <;> simp [v,a₀,a₁,a₂,a₃,a₄]
    · intro i
      fin_cases i
      · exact B.roots0
      · exact B.zUnit
      · exact B.roots1
      · exact B.hUnit
      · exact B.roots2
      · exact B.uUnit
    · intro i
      fin_cases i <;> simp [v,cubic,IsRoot]
    · rfl
    · simp [v,cubic,Phase.rootIndex]
  · let v : Fin 6 → K := ![z,r₀,h,r₁,u,r₂]
    apply consume_phase M .B v _ _ _ _ _
    · refine Fin.strictMono_iff_lt_succ.mpr ?_
      intro i
      fin_cases i <;> simp [v,b₀,b₁,b₂,b₃,b₄]
    · intro i
      fin_cases i
      · exact B.zUnit
      · exact B.roots0
      · exact B.hUnit
      · exact B.roots1
      · exact B.uUnit
      · exact B.roots2
    · intro i
      fin_cases i <;> simp [v,cubic,IsRoot]
    · rfl
    · simp [v,cubic,Phase.rootIndex]

/-- The sole open assumption at the original Moments boundary. It must
hold uniformly on the actual oriented packet, not on sampled fibres. -/
def PaidInnerChronologyGate : Prop :=
  ∀ {L : Type u} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    {a e u h z r₀ r₁ r₂ : L}, OrientedPorts a e u h z r₀ r₁ r₂ →
    PaidInnerChronology e u h z r₀ r₁ r₂

/-- Both actual sole-inner alternatives reduce to this one precise
chronology producer. All cap, cover, phase, and scaling work is internal. -/
theorem no_actual_sole_inner_of_paid_chronology {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (S : SoleInner q c) (paid : PaidInnerChronologyGate.{u}) : False := by
  apply no_actual_sole_inner_of_structural_gate M S
  intro L _ _ _ a e u h z r₀ r₁ r₂ P
  exact no_ranked_sole_inner_with_paid_chronology P (paid P.ports)

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

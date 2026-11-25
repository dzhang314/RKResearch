module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePencilSource
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveReflectedMoments

import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Native source-level terminal rule for the actual interior four-change sector

This statement does not create roots in a non-real-closed base field.
Rather it directly excludes an actual eight-root tuple in whichever ordered
field the original paid moments inhabit. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem no_moments_with_eight_interior_sites {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) {β : Fin 8 → K} (order : StrictMono β)
    (unit : ∀ i, β i ∈ Set.Ioo 0 1) (roots : ∀ i, (q * nodalTail c Z).IsRoot (β i)) : False := by
  obtain ⟨d, κ, pencil⟩ := raw_eight_site_pencil M order.injective roots
  obtain ⟨s, hs, t, ht, direct | reflected⟩ :=
    exists_compact_chart_or_reflection order.injective unit pencil
  · exact no_four_change_moments_all_orders M hs ht order (fun i => ⟨(unit i).1.le, (unit i).2.le⟩)
      direct roots
  · have atOne : q.eval 1 ≠ 0 := by
      intro eq
      have rr : (q * nodalTail c Z).IsRoot 1 := by simp only [IsRoot, eval_mul, eq, zero_mul]
      obtain ⟨nz, dg⟩ := source_product_bound M
      obtain ⟨i, hi⟩ := site_of_eight_roots nz dg order.injective roots rr
      exact (ne_of_lt (unit i).2) hi
    let β' : Fin 8 → K := fun i => 1-β i.rev
    have ord : StrictMono β' := by
      intro i j hij
      exact sub_lt_sub_left (order (Fin.rev_lt_rev.mpr hij)) 1
    have bounded (i : Fin 8) : β' i ∈ Set.Icc 0 1 := by
      exact ⟨sub_nonneg.mpr (unit i.rev).2.le, sub_le_self _ (unit i.rev).1.le⟩
    apply no_four_change_moments_all_orders (reflected_moments M atOne) hs ht ord bounded
      (fun i => reflected i.rev)
    intro i
    rw [← reflected_source_product M]
    change ((q*nodalTail c Z).comp (1-X)).eval (1-β i.rev) = 0
    simpa only [eval_comp, eval_sub, eval_one, eval_X, sub_sub_cancel, IsRoot] using roots i.rev

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

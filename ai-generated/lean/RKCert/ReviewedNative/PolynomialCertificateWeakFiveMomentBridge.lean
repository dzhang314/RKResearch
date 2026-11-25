module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePhysicalPorts
public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Direct source-Moments bridge for the four-change weak-five sector

No vanishing port, polynomial factorization, nonzero scalar, or nonzero
mark span is assumed. Those are produced from the actual six chronological
fields and the selected roots of q. Constructing the centered chart and
the permitted order, possibly in a larger ordered field, is upstream. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The injective list gives the whole factorization when its length
reaches the degree bound. Both multiplicities and the scalar are proved. -/
theorem factor_of_full_root_list {q : K[X]} (hn : q ≠ 0) (v : List K) (distinct : v.Nodup)
    (deg : q.natDegree ≤ v.length) (hr : ∀ x ∈ v, q.IsRoot x) :
    q = C q.leadingCoeff * leftProduct v := by
  classical
  let S : Finset K := ⟨(v : Multiset K), distinct⟩
  have hs : ∀ x ∈ S, q.eval x = 0 := by
    intro x hx
    change x ∈ (v : Multiset K) at hx
    exact hr x (by simpa only [Multiset.mem_coe] using hx)
  have cardS : S.card = v.length := rfl
  have roots : q.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero hs
    (deg.trans_eq cardS.symm) hn
  have hc : q.roots.card = v.length := (congrArg Multiset.card roots).trans cardS
  have split : q.Splits := splits_iff_card_roots.mpr
    (le_antisymm (card_roots' q) (deg.trans_eq hc.symm))
  calc
    q = C q.leadingCoeff * (q.roots.map (fun x => X - C x)).prod := split.eq_prod_roots
    _ = C q.leadingCoeff * leftProduct v := by
      rw [roots]
      change C q.leadingCoeff * ((v : Multiset K).map (fun x => X - C x)).prod = _
      simp only [Multiset.map_coe, Multiset.prod_coe, leftProduct]

private theorem leftProduct_append_one (rs : List K) (u : K) :
    leftProduct (rs ++ [u]) = leftProduct rs * (X - C u) := by simp [leftProduct]

/-- Only the four labels, the eight chart-root equations and the actual
quartic root selections/ordering enter from the structural producer.
All six physical zero equations come from the unchanged source record. -/
theorem no_four_change_moments_with_centered_chart {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (chartRoots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    {σ : List (Fin 8)} (perm : σ.Perm (List.finRange 8)) (good : (decodeWord σ).permitted = true)
    (selected : ∀ i ∈ (decodeWord σ).roots, q.IsRoot (β i))
    (hu : β (decodeWord σ).u = c 1) (ha : β (decodeWord σ).a = c 2)
    (hh : β (decodeWord σ).h = c 3) (hz : β (decodeWord σ).z = c 4) : False := by
  let w := decodeWord σ
  have hu' : β w.u = c 1 := hu
  have ha' : β w.a = c 2 := ha
  have hh' : β w.h = c 3 := hh
  have hz' : β w.z = c 4 := hz
  let rs := w.roots.map β
  let Q := leftProduct rs
  have hlen : σ.length = 8 := by simpa using perm.length_eq
  have rlen : rs.length = 4 := by simp [rs, w, decodeWord, hlen]
  have nodup : σ.Nodup := perm.symm.nodup (List.nodup_finRange 8)
  have nr : w.roots.Nodup := show (σ.take 4).Nodup from nodup.take
  have nq : rs.Nodup := nr.map order.injective
  have even : Even rs.length := by rw [rlen]; decide
  have bounds : q.natDegree ≤ rs.length := by simpa only [rlen] using M.qDegree
  have factor : q = C q.leadingCoeff * Q := by
    apply factor_of_full_root_list M.qNonzero rs nq bounds
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact selected j hj
  have cq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr M.qNonzero
  have loc (l r : K) (P : K[X]) (paid : integral l r (P * q) = 0) :
      integral l r (P * Q) = 0 := by
    have eqn : P * q = q.leadingCoeff • (P * Q) := by
      calc
        P * q = P * (C q.leadingCoeff * Q) := congrArg (fun f => P * f) factor
        _ = q.leadingCoeff • (P * Q) := by rw [Polynomial.smul_eq_C_mul]; ring
    rw [eqn, map_smul, smul_eq_mul] at paid
    exact (mul_eq_zero.mp paid).resolve_left cq
  have rfour : rightProduct rs = Q := rightProduct_eq_leftProduct_of_even rs even
  have lu := loc 0 (c 1) X M.forwardFirst
  have l2 := loc 0 (c 1) (X ^ 2) M.forwardSecond
  have li := loc 0 (c 2) (X * (X - C (c 1))) M.forwardInner
  have rz := loc (c 4) 1 (1 - X) M.reverseFirst
  have r2 := loc (c 4) 1 ((1 - X) ^ 2) M.reverseSecond
  have ri := loc (c 3) 1 ((1 - X) * (C (c 4) - X)) M.reverseInner
  apply no_six_physical_ports_on_chart hs ht order unit chartRoots perm good
  · intro p hp
    change p ∈ w.six at hp
    simp only [PortWord.six, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · change β w.u ≠ 0
      rw [hu']
      exact M.clock_ne_zero (i := 1) (by decide)
    · change 1 - β w.z ≠ 0
      rw [hz']
      exact sub_ne_zero.mpr (M.active 4).1.symm
    · change β w.u ≠ 0
      rw [hu']
      exact M.clock_ne_zero (i := 1) (by decide)
    · change 1 - β w.z ≠ 0
      rw [hz']
      exact sub_ne_zero.mpr (M.active 4).1.symm
    · change β w.a ≠ 0
      rw [ha']
      exact M.clock_ne_zero (i := 2) (by decide)
    · change 1 - β w.h ≠ 0
      rw [hh']
      exact sub_ne_zero.mpr (M.active 3).1.symm
  · intro p hp
    change p ∈ w.six at hp
    simp only [PortWord.six, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · change integral 0 (β w.u) (X ^ 1 * Q) = 0
      rw [hu', pow_one]
      exact lu
    · change integral (β w.z) 1 ((1 - X) ^ 1 * rightProduct rs) = 0
      rw [hz', pow_one, rfour]
      exact rz
    · change integral 0 (β w.u) (X ^ 2 * Q) = 0
      rw [hu']
      exact l2
    · change integral (β w.z) 1 ((1 - X) ^ 2 * rightProduct rs) = 0
      rw [hz', rfour]
      exact r2
    · change integral 0 (β w.a) (X ^ 1 * leftProduct ((w.roots ++ [w.u]).map β)) = 0
      rw [List.map_append, List.map_cons, List.map_nil, leftProduct_append_one, ha, hu, pow_one]
      change integral 0 (c 2) (X * (Q * (X - C (c 1)))) = 0
      simpa only [mul_assoc, mul_comm Q (X - C (c 1))] using li
    · change integral (β w.h) 1 ((1-X) ^ 1 * rightProduct ((w.roots ++ [w.z]).map β)) = 0
      rw [List.map_append, List.map_cons, List.map_nil, rightProduct_append_mark rs even, hh, hz, pow_one]
      change integral (c 3) 1 ((1-X) * (Q * (C (c 4) - X))) = 0
      simpa only [mul_assoc, mul_comm Q (C (c 4) - X)] using ri

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

module

public import RKCert.ReviewedNative.PolynomialCertificateAllWordPorts
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveMomentBridge

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Eight physical roots, in every placement of the four chronological marks

No chronological ordering, sign-window implication, or additional vanishing
test is an input. A last wrapper recovers the four marked sites from the source
product and its eight simple roots. An ordered extension may supply those roots.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem no_six_physical_ports_all_orders {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    {u a h z : Fin 8} (d : ([u, a, h, z] : List (Fin 8)).Nodup)
    (nonzero : ∀ p ∈ (wordOfMarks u a h z).six, portSite p.reflected β p.stop ≠ 0)
    (paid : ∀ p ∈ (wordOfMarks u a h z).six, p.physicalValue β = 0) : False := by
  apply no_six_ports_all_orders hs ht order unit roots d
  intro p hp
  have h := paid p hp
  rw [LocalPort.physicalValue_eq] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (nonzero p hp))

private theorem leftAppendSingle (rs : List K) (u : K) :
    leftProduct (rs ++ [u]) = leftProduct rs * (X - C u) := by simp [leftProduct]

theorem no_all_order_moments_of_marked_sites {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (chartRoots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    {u a h z : Fin 8} (hu : β u = c 1) (ha : β a = c 2)
    (hh : β h = c 3) (hz : β z = c 4)
    (selected : ∀ j : Fin 8, (j ≠ u ∧ j ≠ a ∧ j ≠ h ∧ j ≠ z) → q.IsRoot (β j)) : False := by
  let w := wordOfMarks u a h z
  let rs := w.roots.map β
  let Q := leftProduct rs
  have ne {x y : Fin 8} {i j : Fin 5} (hx : β x = c i) (hy : β y = c j) (hn : i ≠ j) : x ≠ y := by
    intro eq
    exact hn (M.clockSimple (hx.symm.trans ((congrArg β eq).trans hy)))
  have d : ([u, a, h, z] : List (Fin 8)).Nodup := by
    simp [ne hu ha (by decide), ne hu hh (by decide), ne hu hz (by decide),
      ne ha hh (by decide), ne ha hz (by decide), ne hh hz (by decide)]
  have rlen : rs.length = 4 := by
    simpa only [rs, w, List.length_map] using (all_mark_word_spec u a h z d).1
  have nq : rs.Nodup := (markWord_roots_nodup u a h z).map order.injective
  have even : Even rs.length := by rw [rlen]; decide
  change β w.u = c 1 at hu
  change β w.a = c 2 at ha
  change β w.h = c 3 at hh
  change β w.z = c 4 at hz
  have bounds : q.natDegree ≤ rs.length := by simpa only [rlen] using M.qDegree
  have factor : q = C q.leadingCoeff * Q := by
    apply factor_of_full_root_list M.qNonzero rs nq bounds
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact selected j (markWord_roots_iff.mp hj)
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
  apply no_six_physical_ports_all_orders hs ht order unit chartRoots d
  · intro p hp
    change p ∈ w.six at hp
    simp only [PortWord.six, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [portSite, Bool.false_eq_true, if_false, hu] using M.clock_ne_zero (i := 1) (by decide)
    · simpa only [portSite, if_true, hz] using sub_ne_zero.mpr (M.active 4).1.symm
    · simpa only [portSite, Bool.false_eq_true, if_false, hu] using M.clock_ne_zero (i := 1) (by decide)
    · simpa only [portSite, if_true, hz] using sub_ne_zero.mpr (M.active 4).1.symm
    · simpa only [portSite, Bool.false_eq_true, if_false, ha] using M.clock_ne_zero (i := 2) (by decide)
    · simpa only [portSite, if_true, hh] using sub_ne_zero.mpr (M.active 3).1.symm
  · intro p hp
    change p ∈ w.six at hp
    simp only [PortWord.six, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · change integral 0 (β w.u) (X ^ 1 * Q) = 0
      simpa only [hu, pow_one] using lu
    · change integral (β w.z) 1 ((1 - X) ^ 1 * rightProduct rs) = 0
      simpa only [hz, pow_one, rfour] using rz
    · change integral 0 (β w.u) (X ^ 2 * Q) = 0
      simpa only [hu] using l2
    · change integral (β w.z) 1 ((1 - X) ^ 2 * rightProduct rs) = 0
      simpa only [hz, rfour] using r2
    · change integral 0 (β w.a) (X ^ 1 * leftProduct ((w.roots ++ [w.u]).map β)) = 0
      rw [List.map_append, List.map_cons, List.map_nil, leftAppendSingle, ha, hu, pow_one]
      change integral 0 (c 2) (X * (Q * (X - C (c 1)))) = 0
      simpa only [mul_assoc, mul_comm Q (X - C (c 1))] using li
    · change integral (β w.h) 1 ((1-X) ^ 1 * rightProduct ((w.roots ++ [w.z]).map β)) = 0
      rw [List.map_append, List.map_cons, List.map_nil, rightProduct_append_mark rs even, hh, hz, pow_one]
      change integral (c 3) 1 ((1-X) * (Q * (C (c 4) - X))) = 0
      simpa only [mul_assoc, mul_comm Q (C (c 4) - X)] using ri

/-- No root extraction by IVT: all roots of the degree-eight polynomial
belong to the supplied eight-site tuple by equality of finite root multisets. -/
theorem site_of_eight_roots {N : K[X]} (nonzero : N ≠ 0) (deg : N.natDegree ≤ 8)
    {β : Fin 8 → K} (inj : Function.Injective β) (roots : ∀ i, N.IsRoot (β i))
    {x : K} (hx : N.IsRoot x) : ∃ i, β i = x := by
  classical
  let S : Finset K := Finset.univ.image β
  have card : S.card = 8 := by simp [S, Finset.card_image_of_injective _ inj]
  have allroot : ∀ y ∈ S, N.eval y = 0 := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact roots i
  have full : N.roots = S.val :=
    roots_eq_of_natDegree_le_card_of_ne_zero allroot (deg.trans_eq card.symm) nonzero
  have h := (mem_roots nonzero).mpr hx
  rw [full] at h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (show x ∈ S from h)
  exact ⟨i, hi⟩

/-- Native terminal rule for the actual four-change source polynomial.
No permutations, selected factors, location of any mark, or local integral
hypothesis appear. Only the common physical and unit-chart root equations
and the sorted distinct sites must be supplied by the structural reduction. -/
theorem no_four_change_moments_all_orders {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (chartRoots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    (sourceRoots : ∀ i, (q * nodalTail c Z).IsRoot (β i)) : False := by
  classical
  let N := q * nodalTail c Z
  have form : N = q * (((X - C (c 1)) * (X - C (c 4))) * ((X - C (c 2)) * (X - C (c 3)))) := by
    simp only [N, nodalTail, M.middleFactor]
  have nonzero : N ≠ 0 := by
    rw [form]
    exact mul_ne_zero M.qNonzero (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
      (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)))
  have deg : N.natDegree ≤ 8 := by
    rw [form]
    exact natDegree_mul_le_of_le M.qDegree (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le)
      (natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le))
  have liftRoot {x : K} (hx : N.IsRoot x) := site_of_eight_roots nonzero deg order.injective sourceRoots hx
  obtain ⟨u, hu⟩ := liftRoot (x := c 1) (by simp [IsRoot, form])
  obtain ⟨a, ha⟩ := liftRoot (x := c 2) (by simp [IsRoot, form])
  obtain ⟨h, hh⟩ := liftRoot (x := c 3) (by simp [IsRoot, form])
  obtain ⟨z, hz⟩ := liftRoot (x := c 4) (by simp [IsRoot, form])
  apply no_all_order_moments_of_marked_sites M hs ht order unit chartRoots hu ha hh hz
  intro j distinct
  have d {k : Fin 8} {i : Fin 5} (hk : β k = c i) (hn : j ≠ k) : β j - c i ≠ 0 := by
    intro eq
    exact hn (order.injective ((sub_eq_zero.mp eq).trans hk.symm))
  have hroot : N.eval (β j) = 0 := sourceRoots j
  rw [form] at hroot
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hroot
  exact (mul_eq_zero.mp hroot).resolve_right
    (mul_ne_zero (mul_ne_zero (d hu distinct.1) (d hz distinct.2.2.2))
      (mul_ne_zero (d ha distinct.2.1) (d hh distinct.2.2.1)))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

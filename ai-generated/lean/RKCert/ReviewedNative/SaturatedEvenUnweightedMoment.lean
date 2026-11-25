module

public import RKCert.ReviewedNative.EvenExteriorBarycentric
public import RKCert.ReviewedNative.OneWeightOrderedSigns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Unweighted positivity for a saturated two-left/two-right weight

The only quotients used under an integral are already polynomials.
No real closure, fixed Jacobi data, or additional moment is assumed. -/
namespace RKCert.ReviewedNative.SaturatedEvenMoment

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.EvenExteriorBarycentric

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def fourWeight (l₀ l₁ r₀ r₁ : K) : K[X] :=
  (X-C l₀)*(X-C l₁)*(C r₀-X)*(C r₁-X)

private theorem degree_right (r : K) : (C r-X : K[X]).natDegree ≤ 1 := by
  simpa only [natDegree_C, natDegree_X, max_eq_right (Nat.zero_le 1)] using
    (natDegree_sub_le (C r) (X : K[X]))

private theorem scale_integral (c : K) (P : K[X]) :
    integral 0 1 (C c*P) = c*integral 0 1 P := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (integral (0 : K) 1).map_smul c P

private theorem square_pos {D T : K[X]}
    (tn : T ≠ 0) (small : T.natDegree < 19)
    (pay : D.natDegree + 2*T.natDegree ≤ 19)
    (dp : ∀ x ∈ Set.Ioo (0 : K) 1, 0 < D.eval x) :
    0 < integral 0 1 (D*T^2) := by
  have sqd : (T^2).natDegree ≤ 2*T.natDegree := by
    have b := natDegree_pow_le (p := T) (n := 2)
    omega
  have deg : (D*T^2).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le le_rfl sqd).trans pay
  obtain ⟨i, ne⟩ := exists_nonzero_grid_sample (zero_lt_one : (0 : K)<1) tn small
  refine integral_pos_of_grid_samples zero_lt_one deg ?_ ?_
  · intro j
    simp only [eval_mul, eval_pow]
    exact mul_nonneg (dp _ (intervalPoint_mem zero_lt_one j)).le (sq_nonneg _)
  · refine ⟨i, ?_⟩
    simp only [eval_mul, eval_pow]
    exact mul_pos (dp _ (intervalPoint_mem zero_lt_one i)) (sq_pos_of_ne_zero ne)

/-- Difference quotient of the actual T, paid strictly below its degree.
The two signs of a displayed external factor share the same identity. -/
private theorem cauchy {W D T : K[X]} {n : ℕ} {c : K}
    (n0 : 0 < n) (td : T.natDegree = 2*n)
    (mesh : ∀ R : K[X], R.natDegree < 2*n → integral 0 1 (W*T*R) = 0)
    (factors : W = (X-C c)*D ∨ W = (C c-X)*D) :
    T.eval c * integral 0 1 (D*T) = integral 0 1 (D*T^2) := by
  have root : (T-C (T.eval c)).IsRoot c := by
    change (T-C (T.eval c)).eval c = 0
    simp only [eval_sub, eval_C, sub_self]
  obtain ⟨Q,e⟩ := dvd_iff_isRoot.mpr root
  have qd : Q.natDegree < 2*n := by
    by_cases zero : Q = 0
    · rw [zero, natDegree_zero]
      omega
    · have bound : (T-C (T.eval c)).natDegree ≤ 2*n :=
        (natDegree_sub_le _ _).trans (max_le td.le (by simp))
      rw [e, natDegree_mul (X_sub_C_ne_zero c) zero, natDegree_X_sub_C] at bound
      omega
  have zero : integral 0 1 (D*T*(T-C (T.eval c))) = 0 := by
    rw [e]
    rcases factors with eL | eR
    · rw [show D*T*((X-C c)*Q) = W*T*Q by rw [eL]; ring]
      exact mesh Q qd
    · rw [show D*T*((X-C c)*Q) = -(W*T*Q) by rw [eR]; ring,
        map_neg, mesh Q qd, neg_zero]
  rw [show D*T*(T-C (T.eval c)) = D*T^2-C (T.eval c)*(D*T) by ring,
    map_sub, scale_integral] at zero
  exact (sub_eq_zero.mp zero).symm

private theorem pos_of_pos_mul {s t : K} (sp : 0 < s) (st : 0 < s*t) : 0 < t := by
  apply lt_of_not_ge
  intro tn
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos sp.le tn)) st

private theorem quotient_order {a b x y U V : K}
    (ba : b < a) (bp : 0 < b) (xp : 0 < x)
    (ax : a*x = U) (by' : b*y = V) (UV : U < V) : x < y := by
  apply lt_of_not_ge
  intro yx
  have e : b*x < b*y := calc
    b*x < a*x := mul_lt_mul_of_pos_right ba xp
    _ = U := ax
    _ < V := UV
    _ = b*y := by'.symm
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left yx bp.le)) e

/-- The exact bound is 4 + d + (d-1) = 2d+3. The coefficient
direction of degree d is not assumed paid. -/
theorem integral_pos_of_saturated_even {T : K[X]} {n : ℕ}
    {l₀ l₁ r₀ r₁ : K} (n0 : 0 < n) (tm : T.Monic) (td : T.natDegree = 2*n)
    (pay : 4*n+3 ≤ 19)
    (ll : l₀ < l₁) (l1 : l₁ ≤ 0) (r0 : 1 ≤ r₀) (rr : r₀ < r₁)
    (mesh : ∀ R : K[X], R.natDegree < 2*n →
      integral 0 1 (fourWeight l₀ l₁ r₀ r₁*T*R) = 0) :
    0 < integral 0 1 T := by
  let A : K[X] := X-C l₀
  let B : K[X] := X-C l₁
  let C₀ : K[X] := C r₀-X
  let D : K[X] := C r₁-X
  let W : K[X] := fourWeight l₀ l₁ r₀ r₁
  have wEq : W = A*B*C₀*D := rfl
  have aD : A.natDegree ≤ 1 := (natDegree_X_sub_C l₀).le
  have bD : B.natDegree ≤ 1 := (natDegree_X_sub_C l₁).le
  have cD : C₀.natDegree ≤ 1 := degree_right r₀
  have dD : D.natDegree ≤ 1 := degree_right r₁
  have wD : W.natDegree ≤ 4 := by
    rw [wEq]
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le aD bD) cD) dD
  have aP (x : K) (hx : x ∈ Set.Ioo 0 1) : 0 < A.eval x := by
    simpa only [A, eval_sub, eval_C, eval_X] using sub_pos.mpr (ll.trans (l1.trans_lt hx.1))
  have bP (x : K) (hx : x ∈ Set.Ioo 0 1) : 0 < B.eval x := by
    simpa only [B, eval_sub, eval_C, eval_X] using sub_pos.mpr (l1.trans_lt hx.1)
  have cP (x : K) (hx : x ∈ Set.Ioo 0 1) : 0 < C₀.eval x := by
    simpa only [C₀, eval_sub, eval_C, eval_X] using sub_pos.mpr (hx.2.trans_le r0)
  have dP (x : K) (hx : x ∈ Set.Ioo 0 1) : 0 < D.eval x := by
    simpa only [D, eval_sub, eval_C, eval_X] using sub_pos.mpr (hx.2.trans (r0.trans_lt rr))
  have wP (x : K) (hx : x ∈ Set.Ioo 0 1) : 0 < W.eval x := by
    rw [wEq]
    simp only [eval_mul]
    exact mul_pos (mul_pos (mul_pos (aP x hx) (bP x hx)) (cP x hx)) (dP x hx)
  have small : T.natDegree < 19 := by omega
  have gridPay : W.natDegree + T.natDegree + (2*n-1) ≤ 19 := by omega
  have alt : HasAlternationsOn T (Set.Ioo (0 : K) 1) (2*n) := by
    refine HasAlternationsOn.of_grid zero_lt_one
      (grid_variation_of_positive_moments (U := W) (m := 2*n)
        zero_lt_one tm.ne_zero small gridPay wP ?_)
    intro i
    have ix := i.isLt
    apply mesh
    exact (natDegree_X_pow_le _).trans_lt ix
  obtain ⟨lpos,rpos,ldrift,rdrift⟩ := exterior_of_even_alternations n0 tm td alt

  have sq {F : K[X]} (fd : F.natDegree ≤ 3)
      (fp : ∀ x ∈ Set.Ioo (0 : K) 1, 0 < F.eval x) :
      0 < integral 0 1 (F*T^2) :=
    square_pos tm.ne_zero small (by omega) fp
  let L₀ := B*C₀*D
  let L₁ := A*C₀*D
  let R₀ := A*B*D
  let R₁ := A*B*C₀
  have l₀D : L₀.natDegree ≤ 3 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le bD cD) dD
  have l₁D : L₁.natDegree ≤ 3 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le aD cD) dD
  have r₀D : R₀.natDegree ≤ 3 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le aD bD) dD
  have r₁D : R₁.natDegree ≤ 3 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le aD bD) cD
  have l₀P : 0 < integral 0 1 (L₀*T^2) :=
    sq l₀D (fun x hx => by simp only [L₀, eval_mul]; exact mul_pos (mul_pos (bP x hx) (cP x hx)) (dP x hx))
  have l₁P : 0 < integral 0 1 (L₁*T^2) :=
    sq l₁D (fun x hx => by simp only [L₁, eval_mul]; exact mul_pos (mul_pos (aP x hx) (cP x hx)) (dP x hx))
  have r₀P : 0 < integral 0 1 (R₀*T^2) :=
    sq r₀D (fun x hx => by simp only [R₀, eval_mul]; exact mul_pos (mul_pos (aP x hx) (bP x hx)) (dP x hx))
  have r₁P : 0 < integral 0 1 (R₁*T^2) :=
    sq r₁D (fun x hx => by simp only [R₁, eval_mul]; exact mul_pos (mul_pos (aP x hx) (bP x hx)) (cP x hx))
  have cqL₀ := cauchy (W := W) (D := L₀) (c := l₀) n0 td mesh
    (Or.inl (by simp only [W, fourWeight, L₀, A, B, C₀, D] <;> ring))
  have cqL₁ := cauchy (W := W) (D := L₁) (c := l₁) n0 td mesh
    (Or.inl (by simp only [W, fourWeight, L₁, A, B, C₀, D] <;> ring))
  have cqR₀ := cauchy (W := W) (D := R₀) (c := r₀) n0 td mesh
    (Or.inr (by simp only [W, fourWeight, R₀, A, B, C₀, D] <;> ring))
  have cqR₁ := cauchy (W := W) (D := R₁) (c := r₁) n0 td mesh
    (Or.inr (by simp only [W, fourWeight, R₁, A, B, C₀, D] <;> ring))
  have al₀ : 0 < integral 0 1 (L₀*T) :=
    pos_of_pos_mul (lpos _ (ll.le.trans l1)) (cqL₀.symm ▸ l₀P)
  have al₁ : 0 < integral 0 1 (L₁*T) :=
    pos_of_pos_mul (lpos _ l1) (cqL₁.symm ▸ l₁P)
  have ar₀ : 0 < integral 0 1 (R₀*T) :=
    pos_of_pos_mul (rpos _ r0) (cqR₀.symm ▸ r₀P)
  have ar₁ : 0 < integral 0 1 (R₁*T) :=
    pos_of_pos_mul (rpos _ (r0.trans rr.le)) (cqR₁.symm ▸ r₁P)

  have cdSq : 0 < integral 0 1 ((C₀*D)*T^2) := by
    apply sq ((natDegree_mul_le_of_le cD dD).trans (by decide))
    intro x hx
    simp only [eval_mul]
    exact mul_pos (cP x hx) (dP x hx)
  have abSq : 0 < integral 0 1 ((A*B)*T^2) := by
    apply sq ((natDegree_mul_le_of_le aD bD).trans (by decide))
    intro x hx
    simp only [eval_mul]
    exact mul_pos (aP x hx) (bP x hx)
  have lSqLt : integral 0 1 (L₀*T^2) < integral 0 1 (L₁*T^2) := by
    apply sub_pos.mp
    rw [← map_sub, show L₁*T^2-L₀*T^2 = C (l₁-l₀)*((C₀*D)*T^2) by
      simp only [L₁, L₀, A, B, map_sub]; ring, scale_integral]
    exact mul_pos (sub_pos.mpr ll) cdSq
  have rSqLt : integral 0 1 (R₁*T^2) < integral 0 1 (R₀*T^2) := by
    apply sub_pos.mp
    rw [← map_sub, show R₀*T^2-R₁*T^2 = C (r₁-r₀)*((A*B)*T^2) by
      simp only [R₀, R₁, C₀, D, map_sub]; ring, scale_integral]
    exact mul_pos (sub_pos.mpr rr) abSq
  have llT : integral 0 1 (L₀*T) < integral 0 1 (L₁*T) :=
    quotient_order (ldrift l₀ l₁ ll l1) (lpos _ l1) al₀ cqL₀ cqL₁ lSqLt
  have rrT : integral 0 1 (R₁*T) < integral 0 1 (R₀*T) :=
    quotient_order (rdrift r₀ r₁ r0 rr) (rpos _ r0) ar₁ cqR₁ cqR₀ rSqLt
  have cdT : 0 < integral 0 1 ((C₀*D)*T) := by
    have e := sub_pos.mpr llT
    rw [← map_sub, show L₁*T-L₀*T = C (l₁-l₀)*((C₀*D)*T) by
      simp only [L₁, L₀, A, B, map_sub]; ring, scale_integral] at e
    exact pos_of_pos_mul (sub_pos.mpr ll) e
  have abT : 0 < integral 0 1 ((A*B)*T) := by
    have e := sub_pos.mpr rrT
    rw [← map_sub, show R₀*T-R₁*T = C (r₁-r₀)*((A*B)*T) by
      simp only [R₀, R₁, C₀, D, map_sub]; ring, scale_integral] at e
    exact pos_of_pos_mul (sub_pos.mpr rr) e
  have sep (l r : K) (h₁ : l ≤ 0) (h₂ : 1 ≤ r) : 0 < r-l :=
    sub_pos.mpr (h₁.trans_lt (zero_lt_one.trans_le h₂))
  have adT : 0 < integral 0 1 ((A*D)*T) := by
    have e : C (r₀-l₁)*((A*D)*T) = R₀*T+L₁*T := by
      simp only [R₀, L₁, B, C₀, map_sub]; ring
    have h := congrArg (integral (0 : K) 1) e
    simp only [scale_integral, map_add] at h
    exact pos_of_pos_mul (sep _ _ l1 r0) (h.symm ▸ add_pos ar₀ al₁)
  have bcT : 0 < integral 0 1 ((B*C₀)*T) := by
    have e : C (r₁-l₀)*((B*C₀)*T) = R₁*T+L₀*T := by
      simp only [R₁, L₀, A, D, map_sub]; ring
    have h := congrArg (integral (0 : K) 1) e
    simp only [scale_integral, map_add] at h
    exact pos_of_pos_mul (sep _ _ (ll.le.trans l1) (r0.trans rr.le))
      (h.symm ▸ add_pos ar₁ al₀)
  have e : C (r₀-l₀) * (C (r₁-l₁)*T) =
      (A*B)*T+(A*D)*T+(B*C₀)*T+(C₀*D)*T := by
    simp only [A, B, C₀, D, map_sub]
    ring
  have h := congrArg (integral (0 : K) 1) e
  simp only [scale_integral, map_add] at h
  exact pos_of_pos_mul (sep _ _ l1 (r0.trans rr.le))
    (pos_of_pos_mul (sep _ _ (ll.le.trans l1) r0)
      (h.symm ▸ add_pos (add_pos (add_pos abT adT) bcT) cdT))

/-- The six exact global tests of the physical double-exterior chart. -/
theorem integral_pos_of_six {T : K[X]} {l r : K}
    (tm : T.Monic) (td : T.natDegree = 6) (l0 : l < 0) (r1 : 1 < r)
    (mesh : ∀ R : K[X], R.natDegree ≤ 5 → integral 0 1 (fourWeight l 0 1 r*T*R) = 0) :
    0 < integral 0 1 T :=
  integral_pos_of_saturated_even (n := 3) (by decide) tm (by simpa using td)
    (by decide) l0 le_rfl le_rfl r1 (fun R rd => mesh R (by omega))

end
end RKCert.ReviewedNative.SaturatedEvenMoment

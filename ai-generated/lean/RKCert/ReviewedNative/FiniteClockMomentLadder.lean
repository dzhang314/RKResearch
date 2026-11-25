module

public import RKCert.NodalPrimitive
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Finite polynomial duality on clock locations. No tableau, tree order,
ordered field, or sharpness construction belongs to this leaf. -/

namespace RKCert.ReviewedNative.FiniteClockMoments

open Polynomial RKCert.Endpoint
open scoped BigOperators Classical

noncomputable section

variable {K : Type*} [Field K]

/-- A finite signed clock law as an evaluation functional. -/
def moment (H : Finset K) (mass : K → K) : K[X] →ₗ[K] K :=
  ∑ x ∈ H, mass x • Polynomial.leval x

theorem moment_apply (H : Finset K) (mass : K → K) (P : K[X]) :
    moment H mass P = ∑ x ∈ H, mass x * P.eval x := by
  simp only [moment, LinearMap.sum_apply, LinearMap.smul_apply,
    Polynomial.leval_apply, smul_eq_mul]

/-- A monomial prefix covers every polynomial of strictly smaller degree. -/
theorem linearMap_zero_of_monomials (L : K[X] →ₗ[K] K) {count : ℕ}
    (tests : ∀ k : ℕ, k < count → L (X ^ k) = 0)
    (P : K[X]) (degree : P.natDegree < count) : L P = 0 := by
  have expand : P = ∑ n ∈ P.support, P.coeff n • (X : K[X]) ^ n := by
    simpa only [Polynomial.smul_eq_C_mul] using P.as_sum_support_C_mul_X_pow
  calc
    L P = L (∑ n ∈ P.support, P.coeff n • (X : K[X]) ^ n) := congrArg L expand
    _ = ∑ n ∈ P.support, P.coeff n • L (X ^ n) := by simp only [map_sum, map_smul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [tests n ((Polynomial.le_natDegree_of_mem_supp n hn).trans_lt degree), smul_zero]

theorem hull_eval_ne_zero (E : Finset K) {a : K} (off : a ∉ E) :
    (nodalHull E).eval a ≠ 0 := by
  rw [nodalHull, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun h => off (h.symm ▸ hx))

theorem moment_eq_single (H : Finset K) (mass : K → K) {a : K} (ha : a ∈ H)
    (P : K[X]) (off : ∀ x ∈ H, x ≠ a → P.eval x = 0) :
    moment H mass P = mass a * P.eval a := by
  rw [moment_apply]
  apply Finset.sum_eq_single_of_mem a ha
  intro x hx ne
  rw [off x hx ne, mul_zero]

/-- A finite law with at most `count` distinct sites is detected by
exactly the first `count` monomials. Empty support uses no tests. -/
theorem mass_zero_of_monomials (H : Finset K) (mass : K → K) {count : ℕ}
    (size : H.card ≤ count)
    (tests : ∀ k : ℕ, k < count → moment H mass (X ^ k) = 0) :
    ∀ a ∈ H, mass a = 0 := by
  intro a ha
  let P := nodalHull (H.erase a)
  have degree : P.natDegree < count := by
    dsimp only [P]
    rw [natDegree_nodalHull, Finset.card_erase_of_mem ha]
    have hp : 0 < H.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  have hP := linearMap_zero_of_monomials (moment H mass) tests P degree
  have single := moment_eq_single H mass ha P (fun x hx ne =>
    nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨ne, hx⟩))
  have live : P.eval a ≠ 0 := hull_eval_ne_zero _ (Finset.notMem_erase a H)
  exact (mul_eq_zero.mp (single.symm.trans hP)).resolve_right live

/-- The same law after multiplying each mass by the complementary hull. -/
def tilted (E : Finset K) (mass : K → K) (x : K) : K :=
  mass x * (nodalHull E).eval x

def TiltedTests (H E : Finset K) (mass : K → K) (count : ℕ) : Prop :=
  ∀ k : ℕ, k < count → moment H (tilted E mass) (X ^ k) = 0

theorem tiltedTests_iff_sums (H E : Finset K) (mass : K → K) (count : ℕ) :
    TiltedTests H E mass count ↔
      ∀ k : ℕ, k < count → (∑ x ∈ H, (mass x * (nodalHull E).eval x) * x ^ k) = 0 := by
  simp only [TiltedTests, moment_apply, tilted, eval_pow, eval_X]

theorem moment_mul_hull (H E : Finset K) (mass : K → K) (P : K[X]) :
    moment H mass (nodalHull E * P) = moment H (tilted E mass) P := by
  simp only [moment_apply, tilted, eval_mul, mul_assoc]

theorem mass_zero_of_tilted_tests {H E : Finset K} (mass : K → K) {count : ℕ}
    (apart : ∀ x ∈ H, x ∉ E) (size : H.card ≤ count)
    (tests : TiltedTests H E mass count) : ∀ a ∈ H, mass a = 0 := by
  intro a ha
  have h := mass_zero_of_monomials H (tilted E mass) size tests a ha
  change mass a * (nodalHull E).eval a = 0 at h
  exact (mul_eq_zero.mp h).resolve_right (hull_eval_ne_zero E (apart a ha))

/-- Number of consecutive tests paid after removing the complement of
`S` among the visible sites `T`. The use of `< count` handles zero tests. -/
def paidCount (T S : Finset K) (D : ℕ) : ℕ :=
  D + 1 - (T \ S).card

theorem paidCount_eq_add {T S : Finset K} {D : ℕ}
    (sub : S ⊆ T) (base : T.card ≤ D + 1) :
    paidCount T S D = (D + 1 - T.card) + S.card := by
  have card := Finset.card_sdiff_add_card_eq_card sub
  unfold paidCount
  omega

/-- Paid source polynomials with the same visible values have the same
hidden pairing. In particular paid normalized corrections cannot change it. -/
theorem moment_eq_of_same_paid_values {H T : Finset K} {D : ℕ}
    (mass defect : K → K)
    (law : ∀ Q : K[X], Q.natDegree ≤ D → moment H mass Q = moment T defect Q)
    (P Q : K[X]) (hp : P.natDegree ≤ D) (hq : Q.natDegree ≤ D)
    (same : ∀ x ∈ T, P.eval x = Q.eval x) : moment H mass P = moment H mass Q := by
  calc
    moment H mass P = moment T defect P := law P hp
    _ = moment T defect Q := by
      simp only [moment_apply]
      apply Finset.sum_congr rfl
      intro x hx
      rw [same x hx]
    _ = moment H mass Q := (law Q hq).symm

/-- The simultaneous ladder for an arbitrary paid finite-law equality.
No distinctness between the two laws is needed for this equivalence.
Disjointness is used only when recovering the untilted masses. -/
theorem zero_on_stops_iff_tilted_tests {T S H : Finset K} {D : ℕ}
    (mass defect : K → K) (sub : S ⊆ T) (base : T.card ≤ D + 1)
    (law : ∀ Q : K[X], Q.natDegree ≤ D → moment H mass Q = moment T defect Q) :
    (∀ a ∈ S, defect a = 0) ↔ TiltedTests H (T \ S) mass (paidCount T S D) := by
  have card := Finset.card_sdiff_add_card_eq_card sub
  constructor
  · intro zero k hk
    let Q := nodalHull (T \ S) * (X : K[X]) ^ k
    have deg : Q.natDegree ≤ (T \ S).card + k := by
      simpa only [Q, natDegree_nodalHull, natDegree_X_pow] using
        (natDegree_mul_le (p := nodalHull (T \ S)) (q := (X : K[X]) ^ k))
    have hk' : k < D + 1 - (T \ S).card := hk
    have test : Q.natDegree ≤ D := by omega
    have right : moment T defect Q = 0 := by
      rw [moment_apply]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hs : x ∈ S
      · rw [zero x hs, zero_mul]
      · have he : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hs⟩
        simp only [Q, eval_mul, nodalHull_eval_of_mem he, zero_mul, mul_zero]
    exact (moment_mul_hull H (T \ S) mass ((X : K[X]) ^ k)).symm.trans
      ((law Q test).trans right)
  · intro tests a ha
    let P := nodalHull (S.erase a)
    let Q := nodalHull (T \ S) * P
    have hS : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
    have degP : P.natDegree = S.card - 1 := by
      simp only [P, natDegree_nodalHull, Finset.card_erase_of_mem ha]
    have degLt : P.natDegree < paidCount T S D := by
      rw [paidCount_eq_add sub base, degP]
      omega
    have degQ : Q.natDegree ≤ (T \ S).card + P.natDegree := by
      simpa only [Q, natDegree_nodalHull] using
        (natDegree_mul_le (p := nodalHull (T \ S)) (q := P))
    have test : Q.natDegree ≤ D := by omega
    have left : moment H mass Q = 0 :=
      (moment_mul_hull H (T \ S) mass P).trans
        (linearMap_zero_of_monomials (moment H (tilted (T \ S) mass)) tests P degLt)
    have evalOther : ∀ x ∈ T, x ≠ a → Q.eval x = 0 := by
      intro x hx ne
      by_cases hs : x ∈ S
      · have he : x ∈ S.erase a := Finset.mem_erase.mpr ⟨ne, hs⟩
        simp only [Q, P, eval_mul, nodalHull_eval_of_mem he, mul_zero]
      · have he : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hs⟩
        simp only [Q, eval_mul, nodalHull_eval_of_mem he, zero_mul]
    have live₁ : (nodalHull (T \ S)).eval a ≠ 0 :=
      hull_eval_ne_zero _ (fun hx => (Finset.mem_sdiff.mp hx).2 ha)
    have live₂ : P.eval a ≠ 0 := hull_eval_ne_zero _ (Finset.notMem_erase a S)
    have live : Q.eval a ≠ 0 := by simpa only [Q, eval_mul] using mul_ne_zero live₁ live₂
    have stop := moment_eq_single T defect (sub ha) Q evalOther
    exact (mul_eq_zero.mp (stop.symm.trans ((law Q test).symm.trans left))).resolve_right live

end
end RKCert.ReviewedNative.FiniteClockMoments

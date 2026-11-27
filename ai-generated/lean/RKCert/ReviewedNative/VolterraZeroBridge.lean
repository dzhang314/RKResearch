module

public import Init.Grind

@[expose] public section

/-! # Chronological pivots of the actual lower-triangular Volterra commutator

All statements are finite-prefix statements. `A i j` is the coefficient
in physical row `i`, column `j`; entries above the diagonal are ignored.
Specialize `c` to `nodes A` for Runge–Kutta. The two-step identity uses
no division, ordering, characteristic restriction, or order assumption.
-/
namespace RKResearch.Certified.Graded.VolterraZeroBridge

open Lean.Grind

variable {K : Type} [CommRing K]

def sumBefore (f : Nat → K) : Nat → K
  | 0 => 0
  | n+1 => sumBefore f n + f n

/-- The action of the physical lower-triangular coefficient matrix. -/
def act (A : Nat → Nat → K) (v : Nat → K) (i : Nat) : K :=
  sumBefore (fun j => A i j * v j) (i+1)

def nodes (A : Nat → Nat → K) : Nat → K := act A (fun _ => 1)

def cmul (c v : Nat → K) (i : Nat) : K := c i * v i

/-- The literal commutator, `CA − AC − A²`. -/
def vol (A : Nat → Nat → K) (c v : Nat → K) (i : Nat) : K :=
  c i * act A v i - act A (cmul c v) i - act A (act A v) i

private theorem sumBefore_zero (f : Nat → K) (n : Nat)
    (h : ∀ j, j < n → f j = 0) : sumBefore f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBefore, ih (fun j hj => h j (by omega)), h n (by omega)]
    grind

private theorem prefix_zero (A : Nat → Nat → K) (v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) (k : Nat) :
    sumBefore (fun j => A k j * v j) i = 0 :=
  sumBefore_zero _ _ (fun j hj => by rw [h j hj]; grind)

private theorem act_below (A : Nat → Nat → K) (v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) (j : Nat) (hj : j < i) : act A v j = 0 :=
  sumBefore_zero _ _ (fun k hk => by rw [h k (by omega)]; grind)

private theorem cmul_below (c v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) (j : Nat) (hj : j < i) : cmul c v j = 0 := by
  rw [cmul, h j hj]; grind

private theorem act_zero (A : Nat → Nat → K) (v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) : act A v i = A i i * v i := by
  rw [act, sumBefore, prefix_zero A v h]; grind

private theorem act_one (A : Nat → Nat → K) (v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) :
    act A v (i+1) = A (i+1) i * v i + A (i+1) (i+1) * v (i+1) := by
  rw [act, sumBefore, sumBefore, prefix_zero A v h]; grind

private theorem act_two (A : Nat → Nat → K) (v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) :
    act A v (i+2) = A (i+2) i * v i + A (i+2) (i+1) * v (i+1)
       + A (i+2) (i+2) * v (i+2) := by
  rw [act, sumBefore, sumBefore, sumBefore, prefix_zero A v h]; grind

theorem vol_zero (A : Nat → Nat → K) (c v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) : vol A c v i = -(A i i)^2 * v i := by
  rw [vol, act_zero A (cmul c v) (cmul_below c v h),
    act_zero A (act A v) (act_below A v h), act_zero A v h, cmul]
  grind

theorem vol_one (A : Nat → Nat → K) (c v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) :
    vol A c v (i+1) =
      A (i+1) i * (c (i+1) - c i - A i i - A (i+1) (i+1)) * v i
      - (A (i+1) (i+1))^2 * v (i+1) := by
  rw [vol, act_one A (cmul c v) (cmul_below c v h),
    act_one A (act A v) (act_below A v h), act_one A v h, act_zero A v h]
  simp only [cmul]
  grind

theorem vol_two (A : Nat → Nat → K) (c v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) :
    vol A c v (i+2) =
      (A (i+2) i * (c (i+2) - c i - A i i - A (i+2) (i+2))
        - A (i+2) (i+1) * A (i+1) i) * v i
      + A (i+2) (i+1) * (c (i+2) - c (i+1) - A (i+1) (i+1) - A (i+2) (i+2)) * v (i+1)
      - (A (i+2) (i+2))^2 * v (i+2) := by
  rw [vol, act_two A (cmul c v) (cmul_below c v h),
    act_two A (act A v) (act_below A v h), act_two A v h, act_one A v h, act_zero A v h]
  simp only [cmul]
  grind

/-- The consecutive rows `i+1,i+2`, columns `i,i+1` minor of `vol`
when the two outer diagonal entries of `A` vanish. -/
def bridgeMinor (x y z d u v w : K) : K :=
  (z-x) * d^2 * w + u*v * ((y-x)*(z-y) - d*(z-x))

/-- The middle clock can witness a nonzero minor even when the outer
clocks coincide. Neither the direct skip nor the middle diagonal remains. -/
theorem return_minor (x y d u v w : K) :
    bridgeMinor x y x d u v w = -(u*v*(y-x)^2) := by
  unfold bridgeMinor
  grind

theorem minor_eliminates (A : Nat → Nat → K) (c v : Nat → K) {i : Nat}
    (h : ∀ j, j < i → v j = 0) (h₀ : A i i = 0) (h₂ : A (i+2) (i+2) = 0) :
    bridgeMinor (c i) (c (i+1)) (c (i+2)) (A (i+1) (i+1))
       (A (i+1) i) (A (i+2) (i+1)) (A (i+2) i) * v i =
      (A (i+2) (i+1) * (c (i+2) - c (i+1) - A (i+1) (i+1))) * vol A c v (i+1)
      + (A (i+1) (i+1))^2 * vol A c v (i+2) := by
  rw [vol_one A c v h, vol_two A c v h, h₀, h₂, bridgeMinor]
  grind

/-- A pivot index can be omitted when recording a kernel vector. The
intervals witnessing different omitted indices need not be disjoint. -/
def pivotSite (A : Nat → Nat → K) (c : Nat → K) (n i : Nat) : Prop :=
  A i i ≠ 0 ∨
    (i+1 < n ∧ A i i = 0 ∧ A (i+1) (i+1) = 0 ∧
      A (i+1) i * (c (i+1) - c i) ≠ 0) ∨
    (i+2 < n ∧ A i i = 0 ∧ A (i+2) (i+2) = 0 ∧
      bridgeMinor (c i) (c (i+1)) (c (i+2)) (A (i+1) (i+1))
        (A (i+1) i) (A (i+2) (i+1)) (A (i+2) i) ≠ 0)

end RKResearch.Certified.Graded.VolterraZeroBridge

namespace RKResearch.Certified.Graded.VolterraZeroBridge
open Lean.Grind
variable {K : Type} [Field K]

/-- The equal-clock two-hop test works over every field, including characteristic two. -/
theorem return_minor_ne_zero (x y d u v w : K) (hc : y ≠ x) (hu : u ≠ 0) (hv : v ≠ 0) :
    bridgeMinor x y x d u v w ≠ 0 := by
  rw [return_minor]
  intro he
  have hh : u*v*(y-x)^2 = 0 := by grind
  rcases Field.of_mul_eq_zero hh with huv | hxy
  · exact (Field.of_mul_eq_zero huv).elim hu hv
  · have hz := Field.of_pow_eq_zero (y-x) 2 hxy
    apply hc
    grind

private theorem pivot_zero (A : Nat → Nat → K) (c v : Nat → K) {n i : Nat}
    (hz : ∀ j, j < n → vol A c v j = 0) (hi : i < n)
    (hpre : ∀ j, j < i → v j = 0) (h : pivotSite A c n i) : v i = 0 := by
  rcases h with hd | ⟨hpaid, hl, hr, hedge⟩ | ⟨hpaid, hl, hr, hminor⟩
  · have he := hz i hi
    rw [vol_zero A c v hpre] at he
    rcases Field.of_mul_eq_zero he with hbad | hgood
    · have hsq : (A i i)^2 = 0 := by grind
      exact False.elim (hd (Field.of_pow_eq_zero _ 2 hsq))
    · exact hgood
  · have he := hz (i+1) hpaid
    rw [vol_one A c v hpre, hl, hr] at he
    have hprod : (A (i+1) i * (c (i+1)-c i)) * v i = 0 := by grind
    exact (Field.of_mul_eq_zero hprod).resolve_left hedge
  · have he := minor_eliminates A c v hpre hl hr
    rw [hz (i+1) (by omega), hz (i+2) hpaid] at he
    have he' : bridgeMinor (c i) (c (i+1)) (c (i+2)) (A (i+1) (i+1))
        (A (i+1) i) (A (i+2) (i+1)) (A (i+2) i) * v i = 0 := by
      rw [he]; grind
    exact (Field.of_mul_eq_zero he').resolve_left hminor

/-- Kernel restriction to nonpivot coordinates has trivial kernel, hence over
any field its dimension is at most their number. The proof eliminates the
leftmost nonzero coordinate, so successful checks sharing endpoints incur
no double-count provided their starting coordinates differ. -/
theorem kernel_zero_of_free_zero (A : Nat → Nat → K) (c v : Nat → K) (n : Nat)
    (hz : ∀ j, j < n → vol A c v j = 0)
    (hf : ∀ j, j < n → ¬pivotSite A c n j → v j = 0) :
    ∀ j, j < n → v j = 0 := by
  have aux : ∀ k, ∀ j, j < k → j < n → v j = 0 := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj jn
      by_cases jk : j < k
      · exact ih j jk jn
      · have he : j = k := by omega
        subst j
        by_cases hp : pivotSite A c n k
        · exact pivot_zero A c v hz jn (fun t ht => ih t ht (by omega)) hp
        · exact hf k jn hp
  exact fun j hj => aux (j+1) j (by omega) hj

end RKResearch.Certified.Graded.VolterraZeroBridge

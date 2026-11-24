module

public import RKCert.ReviewedNative.ERKCharZero
public import RKCert.ReviewedNative.ERKDoublingHead
public import RKCert.ReviewedNative.NativeFlatClockHead
public import Mathlib.Data.Nat.Log

public section

/-! # Native logarithmic ERK stage obstruction

At every fully paid doubling interval above grade five the actual
homogeneous defect flag gains strictly more than one dimension per
grade on average. The argument combines the generic intrinsic flat
head, a physical short-polynomial contradiction, and the already
reviewed rank-to-stage and coefficient specialization joins.
-/
namespace RKResearch.Certified.Graded

open RKResearch Module RKCert.OneEscape

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- At least one rank gain in the actual j,…,2j band is larger than one.
The hypothesis 4j ≤ p pays polynomial separation through degree 2j. -/
theorem erk_doubling_rank_surplus (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b p)
    {j : ℕ} (j5 : 5≤j) (pay : 4*j≤p) :
    finrank K (zeroSpace A j)+j+1 ≤ finrank K (zeroSpace A (2*j)) := by
  by_contra! low
  cases s with
  | zero =>
    have chain := RKResearch.Certified.explicit_order_le_stages ha ho
    omega
  | succ s =>
    have coeffSep := explicit_coeff_separated ha ho (q:=j+j) (by omega)
    have sep : PolySeparated A (j+j) := PolySeparated.of_coeff coeffSep
    have cap : finrank K (zeroSpace A (j+j)) ≤ finrank K (zeroSpace A j)+j := by
      rw [show j+j=2*j by omega]
      omega
    obtain ⟨r,U,v,head⟩ := flat_clock_head ha coeffSep (by omega) (by omega) cap
    have gain := clock_invariant_outgoing ha (sep.mono (show j≤j+j by omega))
      head.coreInside head.coreStable
    have rank := head.ranks 1 (by omega)
    have base := head.baseRank
    have r2 : 2≤r := by omega
    have first : zeroSpace A j=chain (diag (nodes A)) U v r := by
      simpa only [Nat.add_zero] using head.flags 0 (by omega)
    have last := head.flags j le_rfl
    apply no_explicit_doubling_head ha ho j5 (by omega) sep r2 head.coreStable head.coreInside first last
    intro stableLast
    apply head.unpaid
    have prev :=
      ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=v) (r+j)).mp last.ge).2 (r+j-1) (by omega)
    rw [show r+j=(r+j-1)+1 by omega,pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact stableLast (Submodule.mem_map_of_mem prev)

/-- The grade-five rank and every paid dyadic doubling of it earn one
more stage than the preceding characteristic-zero floor. -/
theorem erk_logarithmic_field_dyadic (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b p) (d : ℕ) (budget : 10*2^d≤p) :
    (3*p+1)/2-1+d ≤ s := by
  let q := p/2
  have power (n : ℕ) : 0 < (2:ℕ)^n := pow_pos (by decide) _
  have hp : 10≤p := by have := power d; omega
  have h5 := grade_five_surplus_of_reviewed_order ha ho hp
  have band (n : ℕ) (paid : 5*2^n≤q) : 5*2^n+n≤finrank K (zeroSpace A (5*2^n)) := by
    induction n with
    | zero => simpa using h5
    | succ n ih =>
      have eq : 5*2^(n+1)=2*(5*2^n) := by rw [pow_succ]; ring
      rw [eq] at paid ⊢
      have := power n
      have before := ih (by omega)
      have gain := erk_doubling_rank_surplus ha ho (j:=5*2^n) (by omega)
        (by dsimp [q] at paid; omega)
      omega
  have paid : 5*2^d≤q := by dsimp [q]; omega
  have initial := band d paid
  have grow := Reverse.erk_paid_rank_interval ha ho (a:=5*2^d) (q:=q)
    (by have := power d; omega) paid (by dsimp [q]; omega)
  apply Reverse.erk_count_of_midpoint_rank ha ho (by omega) d
  change q+d≤finrank K (zeroSpace A q)
  omega

end RKResearch.Certified.Graded

namespace RKResearch
universe u

/-- Logarithmic ERK floor over every characteristic-zero commutative ring,
possibly with zero divisors. Strictness and native order survive the
characteristic-zero field specialization, on the same physical indices. -/
theorem HasOrder.erk_logarithmic_stages {R : Type u} [CommRing R] [CharZero R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b p) (ha : ∀ i j, i ≤ j → A i j=0) (hp : 10≤p) :
    (3*p+1)/2-1+Nat.log 2 (p/10) ≤ s := by
  have power := Nat.pow_log_le_self 2 (by omega : p/10≠0)
  exact h.strict_lower_triangular_of_charZero_fields ha (fun _ _ _ _ _ ht ho =>
    Certified.Graded.erk_logarithmic_field_dyadic ht ho (Nat.log 2 (p/10)) (by omega))

/-- The logarithmic refinement first increases the grade-five count at
order twenty, where it proves thirty original stages. -/
theorem HasOrder.erk_order_twenty_charZero_stages {R : Type u} [CommRing R] [CharZero R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b 20) (ha : ∀ i j, i ≤ j → A i j=0) : 30≤s :=
  h.erk_logarithmic_stages ha (by decide)

end RKResearch

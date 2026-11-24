module

public import RKCert.ScaledRootCuts
public import RKCert.ResidueTransfer
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
/-! Direct DIRK lower endpoints for orders up to five, over every field,
then transferred to nontrivial commutative rings.  The tree conditions themselves
supply the required small integer units. No sign, real-pole premise, weight
restriction, or node ordering enters. -/
namespace RKCert.DIRKFinite
open RKCert

variable {K : Type*} [Field K] {s : ℕ}

/-- Scalar moment at a specified degree. -/
def mass (b c : Fin s → K) (k : ℕ) : K := ∑ i, b i * c i ^ k

private theorem mass_eq {A : Fin s → Fin s → K} {b : Fin s → K} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (k : ℕ) (hk : k+1 ≤ p) :
    mass b (nodes A) k = 1 / ((k+1 : ℕ) : K) := by
  apply (eq_div_iff (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (Nat.succ_pos k) hk).ne_zero).2
  simpa only [mass, mul_comm] using hasMomentsThrough_of_treeOrder ho k hk

private theorem pure_moment {A : Fin s → Fin s → K} {b : Fin s → K} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (d k : ℕ) (hk : d+1+(k+1) ≤ p) :
    mass (fun i => b i * scaledStageResidual A (Tree.bush d) i) (nodes A) k = 0 := by
  have h0 := balancedRootCut_of_treeOrder ho (Tree.bush d) (Tree.bush k)
    (by simpa only [Tree.order_bush] using hk)
  have h1 : scaledRootCutPair A b (Tree.bush d) (Tree.bush k) = 0 := by
    rw [scaledRootCutPair_eq, sub_eq_zero]
    exact h0
  simpa only [mass, scaledRootCutPair, stageWeight_bush, mul_assoc] using h1

/-- Weighted two-knot Vandermonde determinant equals the first Hilbert minor. -/
theorem massDet2 (b c : Fin 2 → K) :
    b 0 * b 1 * (c 1-c 0)^2 = mass b c 0 * mass b c 2 - mass b c 1 ^ 2 := by
  simp only [mass, Fin.sum_univ_two, pow_zero, pow_one, mul_one]
  ring

/-- A three-knot signed measure, repeated sites allowed, satisfies the exact Hankel identity. -/
theorem massDet3 (b c : Fin 3 → K) :
    b 0*b 1*b 2 * (c 1-c 0)^2 * (c 2-c 0)^2 * (c 2-c 1)^2 =
      mass b c 0 * (mass b c 2 * mass b c 4 - mass b c 3 ^ 2) -
      mass b c 1 * (mass b c 1 * mass b c 4 - mass b c 3 * mass b c 2) +
      mass b c 2 * (mass b c 1 * mass b c 3 - mass b c 2 ^ 2) := by
  simp only [mass, Fin.sum_univ_three, pow_zero, pow_one, mul_one]
  ring

private theorem origin_of_quad {A : Fin s → Fin s → K} (i : Fin s)
    (hrow : ∀ j, j ≠ i → A i j = 0)
    (hg : scaledStageResidual A (Tree.bush 1) i = 0) :
    nodes A i = 0 := by
  have hrowSum : nodes A i = A i i := by
    unfold nodes
    exact Finset.sum_eq_single i (by intro j _ hji; exact hrow _ hji)
      (by simp)
  have hsq : (nodes A i)^2 = 0 := by
    have hs : (∑ j, A i j * nodes A j ^ 1) = A i i * nodes A i ^ 1 := by
      exact Finset.sum_eq_single i (by intro j _ hji; rw [hrow _ hji, zero_mul]) (by simp)
    simp only [scaledStageResidual, Tree.order_bush, Tree.density_bush, stageWeight_bush, hs] at hg
    norm_num only at hg
    rw [← hrowSum] at hg
    linear_combination hg
  exact (sq_eq_zero_iff).mp hsq

private theorem weaken {A : Fin s → Fin s → K} {b : Fin s → K} {p q : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hq : q ≤ p) : HasTreeOrderAtLeast A b q :=
  fun t ht => ho t (ht.trans hq)

/-- Even a nondiagonal RK tableau of order three needs two stages, over any characteristic-zero field. -/
theorem order_three {A : Fin s → Fin s → K} {b : Fin s → K}
    (ho : HasTreeOrderAtLeast A b 3) : 2 ≤ s := by
  have nz2 : ((2 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 2) (by decide : 2 ≤ 3)).ne_zero
  have nz3 : ((3 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 3) (by decide : 3 ≤ 3)).ne_zero
  by_contra hn
  have hs : s = 0 ∨ s = 1 := by omega
  rcases hs with rfl | rfl
  · have h := ho Tree.leaf (by decide)
    simp [weight, Tree.density, Tree.order, Tree.childDensityProduct] at h
  · have m0 := mass_eq ho 0 (by decide)
    have m1 := mass_eq ho 1 (by decide)
    have m2 := mass_eq ho 2 (by decide)
    norm_num [mass, Fin.sum_univ_one] at m0 m1 m2
    rw [m0, one_mul] at m1 m2
    rw [m1] at m2
    field_simp [nz2,nz3] at m2
    norm_num at m2
    exact one_ne_zero (by linear_combination m2)

/-- Three physical stages are necessary for order four. -/
theorem order_four {A : Fin s → Fin s → K} {b : Fin s → K}
    (ltA : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b 4) : 3 ≤ s := by
  have nz2 : ((2 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 2) (by decide : 2 ≤ 4)).ne_zero
  have nz3 : ((3 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 3) (by decide : 3 ≤ 4)).ne_zero
  have nz4 : ((4 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 4) (by decide : 4 ≤ 4)).ne_zero
  have hprev := order_three (weaken ho (by decide : 3 ≤ 4))
  by_contra hn
  have hs : s = 2 := by omega
  subst s
  let c := nodes A
  let g := scaledStageResidual A (Tree.bush 1)
  have h0m : (1 : K) * mass b c 0 = 1 :=
    by simpa only [Nat.reduceAdd,Nat.cast_one,mass,c] using hasMomentsThrough_of_treeOrder ho 0 (by decide)
  have h1m : (2 : K) * mass b c 1 = 1 :=
    hasMomentsThrough_of_treeOrder ho 1 (by decide)
  have h2m : (3 : K) * mass b c 2 = 1 :=
    hasMomentsThrough_of_treeOrder ho 2 (by decide)
  have hcert : (12:K)*(b 0 * b 1 * (c 1 - c 0)^2) = 1 := by
    rw [massDet2]
    linear_combination (12*mass b c 2)*h0m + (-(6*mass b c 1)-3)*h1m + 4*h2m
  have hv : b 0 * b 1 * (c 1 - c 0)^2 ≠ 0 := by intro hz; rw [hz, mul_zero] at hcert; exact zero_ne_one hcert
  have hb0 : b 0 ≠ 0 := by intro h; apply hv; simp [h]
  have h10 : c 1 - c 0 ≠ 0 := by intro h; apply hv; simp [h]
  have t0 := pure_moment ho 1 0 (by decide)
  have t1 := pure_moment ho 1 1 (by decide)
  change mass (fun i => b i * g i) c 0 = 0 at t0
  change mass (fun i => b i * g i) c 1 = 0 at t1
  simp only [mass, Fin.sum_univ_two, pow_zero, pow_one, mul_one] at t0 t1
  have h0 : b 0 * (c 1 - c 0) * g 0 = 0 := by linear_combination c 1 * t0 - t1
  have hg0 := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hb0 h10)
  have hc0 : c 0 = 0 := origin_of_quad 0 (by intro j hj; apply ltA; apply Nat.pos_of_ne_zero; intro he; apply hj; exact Fin.ext he) hg0
  have k1 := mass_eq ho 1 (by decide)
  have k2 := mass_eq ho 2 (by decide)
  have k3 := mass_eq ho 3 (by decide)
  change mass b c 1 = _ at k1
  change mass b c 2 = _ at k2
  change mass b c 3 = _ at k3
  have hk : mass b c 1 * mass b c 3 = mass b c 2 ^ 2 := by
    simp only [mass, Fin.sum_univ_two, hc0, zero_pow (by decide : 1 ≠ 0), zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero, zero_add]
    ring
  rw [k1,k2,k3] at hk
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hk
  field_simp [nz2,nz3,nz4] at hk
  norm_num at hk
  exact one_ne_zero (by linear_combination -hk)

/-- Four physical stages are necessary for order five. -/
theorem order_five {A : Fin s → Fin s → K} {b : Fin s → K}
    (ltA : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b 5) : 4 ≤ s := by
  have nz2 : ((2 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 2) (by decide : 2 ≤ 5)).ne_zero
  have nz3 : ((3 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 3) (by decide : 3 ≤ 5)).ne_zero
  have nz4 : ((4 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 4) (by decide : 4 ≤ 5)).ne_zero
  have nz5 : ((5 : ℕ) : K) ≠ 0 := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) (by decide : 0 < 5) (by decide : 5 ≤ 5)).ne_zero
  have hprev := order_four ltA (weaken ho (by decide : 4 ≤ 5))
  by_contra hn
  have hs : s = 3 := by omega
  subst s
  let c := nodes A
  let g := scaledStageResidual A (Tree.bush 1)
  let h := scaledStageResidual A (Tree.bush 2)
  have h0m : (1 : K) * mass b c 0 = 1 :=
    by simpa only [Nat.reduceAdd,Nat.cast_one,mass,c] using hasMomentsThrough_of_treeOrder ho 0 (by decide)
  have h1m : (2 : K) * mass b c 1 = 1 :=
    hasMomentsThrough_of_treeOrder ho 1 (by decide)
  have h2m : (3 : K) * mass b c 2 = 1 :=
    hasMomentsThrough_of_treeOrder ho 2 (by decide)
  have h3m : (4 : K) * mass b c 3 = 1 :=
    hasMomentsThrough_of_treeOrder ho 3 (by decide)
  have h4m : (5 : K) * mass b c 4 = 1 :=
    hasMomentsThrough_of_treeOrder ho 4 (by decide)
  have hcert : (2160:K)*(b 0*b 1*b 2 * (c 1-c 0)^2 * (c 2-c 0)^2 * (c 2-c 1)^2) = 1 := by
    rw [massDet3]
    linear_combination (2160*mass b c 2*mass b c 4-2160*(mass b c 3)^2)*h0m +
      (-(1080*mass b c 1*mass b c 4)+2160*mass b c 2*mass b c 3-540*mass b c 4)*h1m +
      (-(720*(mass b c 2)^2)-240*mass b c 2+720*mass b c 3+720*mass b c 4-80)*h2m +
      (45-540*mass b c 3)*h3m + 36*h4m
  have hv : b 0*b 1*b 2 * (c 1-c 0)^2 * (c 2-c 0)^2 * (c 2-c 1)^2 ≠ 0 := by intro hz; rw [hz, mul_zero] at hcert; exact zero_ne_one hcert
  have hb0 : b 0 ≠ 0 := by intro e; apply hv; simp [e]
  have hb1 : b 1 ≠ 0 := by intro e; apply hv; simp [e]
  have h10 : c 1 - c 0 ≠ 0 := by intro e; apply hv; simp [e]
  have h20 : c 2 - c 0 ≠ 0 := by intro e; apply hv; simp [e]
  have h21 : c 2 - c 1 ≠ 0 := by intro e; apply hv; simp [e]
  have t0 := pure_moment ho 1 0 (by decide)
  have t1 := pure_moment ho 1 1 (by decide)
  have t2 := pure_moment ho 1 2 (by decide)
  change mass (fun i => b i * g i) c 0 = 0 at t0
  change mass (fun i => b i * g i) c 1 = 0 at t1
  change mass (fun i => b i * g i) c 2 = 0 at t2
  simp only [mass, Fin.sum_univ_three, pow_zero, pow_one, mul_one] at t0 t1 t2
  have e0 : b 0 * (c 1-c 0) * (c 2-c 0) * g 0 = 0 := by
    linear_combination c 1*c 2*t0 - (c 1+c 2)*t1 + t2
  have e1 : b 1 * (c 1-c 0) * (c 2-c 1) * g 1 = 0 := by
    linear_combination -(c 0*c 2)*t0 + (c 0+c 2)*t1 - t2
  have hg0 := (mul_eq_zero.mp e0).resolve_left (mul_ne_zero (mul_ne_zero hb0 h10) h20)
  have hg1 := (mul_eq_zero.mp e1).resolve_left (mul_ne_zero (mul_ne_zero hb1 h10) h21)
  have hc0 : c 0 = 0 := origin_of_quad 0 (by intro j hj; apply ltA; apply Nat.pos_of_ne_zero; intro he; apply hj; exact Fin.ext he) hg0
  have hc1 : c 1 ≠ 0 := by simpa only [hc0,sub_zero] using h10
  have za : A 0 1 = 0 := ltA 0 1 (by decide)
  have zb : A 0 2 = 0 := ltA 0 2 (by decide)
  have zd : A 1 2 = 0 := ltA 1 2 (by decide)
  have hh0 : h 0 = 0 := by
    simp only [h, scaledStageResidual, Tree.order_bush, Tree.density_bush, stageWeight_bush, Fin.sum_univ_three]
    change _ * (A 0 0*c 0 ^ 2 + A 0 1*c 1 ^ 2 + A 0 2*c 2 ^ 2) - c 0 ^ 3 = 0
    simp [hc0,za,zb]
  have u0 := pure_moment ho 2 0 (by decide)
  have u1 := pure_moment ho 2 1 (by decide)
  change mass (fun i => b i * h i) c 0 = 0 at u0
  change mass (fun i => b i * h i) c 1 = 0 at u1
  simp only [mass, Fin.sum_univ_three, pow_zero, pow_one, mul_one, hh0, mul_zero, zero_mul, zero_add] at u0 u1
  have t : b 1 * (c 2-c 1) * h 1 = 0 := by
    linear_combination c 2*u0-u1
  have hh1 := (mul_eq_zero.mp t).resolve_left (mul_ne_zero hb1 h21)
  simp only [g,h,scaledStageResidual,Tree.order_bush,Tree.density_bush,stageWeight_bush,Fin.sum_univ_three] at hg1 hh1
  change (2:K) * (A 1 0*c 0 ^ 1 + A 1 1*c 1 ^ 1 + A 1 2*c 2 ^ 1) - c 1 ^ 2 = 0 at hg1
  change (3:K) * (A 1 0*c 0 ^ 2 + A 1 1*c 1 ^ 2 + A 1 2*c 2 ^ 2) - c 1 ^ 3 = 0 at hh1
  simp only [hc0,zd,zero_pow (by decide : 1 ≠ 0),zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,zero_add,add_zero,pow_one] at hg1 hh1
  have finish : c 1 ^ 3 = 0 := by linear_combination 2*hh1-3*c 1*hg1
  exact pow_ne_zero 3 hc1 finish

universe u

/-- Conservation of the one-vertex tree rules out an empty tableau, already in a semiring. -/
theorem positive_stages {R : Type u} [CommSemiring R] [Nontrivial R] {s p : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ho : HasTreeOrderAtLeast A b p) (hp : 1 ≤ p) : 1 ≤ s := by
  by_contra hn
  have he : s = 0 := by omega
  subst s
  have hr := ho Tree.leaf hp
  simp [weight, Tree.density, Tree.order, Tree.childDensityProduct] at hr

/-- Order three for DIRK, in every nonzero coefficient ring. -/
theorem order_three_ring {R : Type u} [CommRing R] [Nontrivial R] {A : Fin s → Fin s → R}
    {b : Fin s → R} (ltA : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b 3) : 2 ≤ s :=
  lowerTriangular_of_all_fields (fun _ _ _ _ _ ho' => order_three ho') ltA ho

/-- The original full RKOC over any nontrivial commutative ring imply the order-four DIRK floor. -/
theorem order_four_ring {R : Type u} [CommRing R] [Nontrivial R] {A : Fin s → Fin s → R}
    {b : Fin s → R} (ltA : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b 4) : 3 ≤ s :=
  lowerTriangular_of_all_fields (fun _ _ _ _ ltA' ho' => order_four ltA' ho') ltA ho

/-- The original full RKOC over any nontrivial commutative ring imply the order-five DIRK floor.
No reducedness is required. All denominators through p are provided by the RKOC themselves. -/
theorem order_five_ring {R : Type u} [CommRing R] [Nontrivial R] {A : Fin s → Fin s → R}
    {b : Fin s → R} (ltA : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b 5) : 4 ≤ s :=
  lowerTriangular_of_all_fields (fun _ _ _ _ ltA' ho' => order_five ltA' ho') ltA ho

end RKCert.DIRKFinite


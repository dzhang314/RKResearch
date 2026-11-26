module

public import RKCert.ReviewedNative.AbstractContextModel
public import RKCert.ReviewedNative.FiniteRootedSeriesCertificate
public import RKCert.ReviewedNative.GradedPrimitives
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The scalar moment test of the polynomial projection suffices for all
literal tree shapes. Only the denominators within the paid order are used. -/
namespace RKResearch.ContextCompletion

open RKResearch Polynomial FiniteRootedTree RKResearch.FiniteSeries
open RKResearch.Certified.Graded (primitive primitive_monomial primitive_natDegree_le
  primitive_coeff_zero primitive_coeff_succ)
open scoped Polynomial FiniteRootedTree

noncomputable section

variable {K : Type*} [Field K]

def PaidUnits (K : Type*) [Field K] (p : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j ≤ p → (j : K) ≠ 0

theorem PaidUnits.of_tableau {ι : Type*} [Fintype ι] {p : ℕ}
    {A : Matrix ι ι K} {b : ι → K} (h : RKResearch.HasOrder p A b) : PaidUnits K p :=
  fun j pos pay => (h.hasQuadratureOrder.isUnit pos pay).ne_zero

/-- Formal evaluation of the existing native primitive at one. -/
def unitMoment : Polynomial K →ₗ[K] K := (Polynomial.leval 1).comp primitive

theorem unitMoment_monomial (j : ℕ) (a : K) :
    unitMoment (monomial j a) = a / ((j + 1 : ℕ) : K) := by
  change (primitive (monomial j a)).eval 1 = _
  rw [primitive_monomial, eval_monomial, one_pow, mul_one]

theorem unitMoment_power (j : ℕ) : unitMoment ((X : K[X]) ^ j) = ((j + 1 : ℕ) : K)⁻¹ := by
  rw [← monomial_one_right_eq_X_pow, unitMoment_monomial, one_div]

private theorem primitive_power (j : ℕ) :
    primitive ((X : K[X]) ^ j) = ((j + 1 : ℕ) : K)⁻¹ • (X ^ (j + 1) : K[X]) := by
  calc
    primitive ((X : K[X]) ^ j) = primitive (monomial j 1) := by
      rw [monomial_one_right_eq_X_pow]
    _ = monomial (j + 1) (1 / ((j + 1 : ℕ) : K)) := primitive_monomial _ _
    _ = _ := by rw [Polynomial.smul_eq_C_mul, C_mul_X_pow_eq_monomial, one_div]

private theorem derivative_primitive_paid {p : ℕ} (units : PaidUnits K p)
    (f : K[X]) (paid : f.natDegree + 1 ≤ p) : (primitive f).derivative = f := by
  ext j
  rw [Polynomial.coeff_derivative, primitive_coeff_succ]
  by_cases h : j ≤ f.natDegree
  · have nz := units (j + 1) (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using div_mul_cancel₀ (f.coeff j) nz
  · have e : f.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [e, zero_div, zero_mul]

private theorem primitive_derivative_paid {p : ℕ} (units : PaidUnits K p)
    (f : K[X]) (origin : f.coeff 0 = 0) (paid : f.natDegree ≤ p) :
    primitive f.derivative = f := by
  ext j
  cases j with
  | zero => rw [primitive_coeff_zero, origin]
  | succ j =>
    rw [primitive_coeff_succ, Polynomial.coeff_derivative]
    by_cases h : j + 1 ≤ f.natDegree
    · have nz := units (j + 1) (by omega) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using mul_div_cancel_right₀ (f.coeff (j + 1)) nz
    · have e : f.coeff (j + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [e, zero_mul, zero_div]

/-- Integration by parts with just the finite paid characteristic condition. -/
theorem unitMoment_byParts {p : ℕ} (units : PaidUnits K p)
    (f g : K[X]) (paid : f.natDegree + g.natDegree + 1 < p) :
    unitMoment (f * primitive g) =
      unitMoment ((C (unitMoment f) - primitive f) * g) := by
  have df := derivative_primitive_paid units f (by omega)
  have dg := derivative_primitive_paid units g (by omega)
  have f0 : (primitive f).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, primitive_coeff_zero]
  have origin : (primitive f * primitive g).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_mul, f0, zero_mul]
  have degree : (primitive f * primitive g).natDegree ≤ p :=
    (natDegree_mul_le_of_le (primitive_natDegree_le (le_refl f.natDegree))
      (primitive_natDegree_le (le_refl g.natDegree))).trans (by omega)
  have e := primitive_derivative_paid units _ origin degree
  rw [derivative_mul, df, dg, map_add] at e
  have h : unitMoment (f * primitive g) + unitMoment (primitive f * g) =
      unitMoment f * unitMoment g := by
    simpa only [unitMoment, LinearMap.comp_apply, Polynomial.leval_apply, eval_add, eval_mul]
      using congrArg (fun a : K[X] => a.eval 1) e
  have q : unitMoment ((C (unitMoment f) - primitive f) * g) =
      unitMoment f * unitMoment g - unitMoment (primitive f * g) := by
    rw [sub_mul, ← Polynomial.smul_eq_C_mul, map_sub, map_smul, smul_eq_mul]
  exact (eq_sub_iff_add_eq.mpr h).trans q.symm

/-- A polynomial quotient or other algebra carrying normal representatives.
The moment law compares scalar polynomial readouts, not tree outputs. -/
structure MomentProjection (K V : Type*) [Field K] [CommRing V] [Algebra K V] (p : ℕ) where
  project : Polynomial K →ₐ[K] V
  normal : V →ₗ[K] Polynomial K
  retract : ∀ v, project (normal v) = v
  reduce_degree : ∀ f, (normal (project f)).natDegree ≤ f.natDegree
  paid_reduction : ∀ f, f.natDegree < p → unitMoment (normal (project f)) = unitMoment f

namespace MomentProjection

variable {V : Type*} [CommRing V] [Algebra K V] {p : ℕ}
variable (P : MomentProjection K V p)

def model : Model K V where
  act := P.project.toLinearMap.comp (primitive.comp P.normal)
  readout := unitMoment.comp P.normal

private def rep (t : FiniteRootedTree) : K[X] := P.normal (P.model.column t)

private theorem rep_leaf : P.rep .leaf = P.normal (P.project 1) := by
  change P.normal 1 = P.normal (P.project 1)
  exact congrArg (fun v : V => P.normal v) (map_one P.project).symm

private theorem rep_join (t u : FiniteRootedTree) :
    P.rep (t # u) = P.normal (P.project (P.rep t * P.rep u)) := by
  unfold rep
  simp only [Model.column_rootedSum, map_mul, P.retract]

private theorem rep_unary (t : FiniteRootedTree) :
    P.rep (.leaf ◂ t) = P.normal (P.project (primitive (P.rep t))) := by
  unfold rep
  rw [Model.column_unary]
  rfl

private theorem rep_degree (t : FiniteRootedTree) : (P.rep t).natDegree ≤ treeGrade t := by
  induction t with
  | leaf =>
    rw [P.rep_leaf, treeGrade_leaf]
    exact (P.reduce_degree (1 : K[X])).trans (by simp)
  | butcherProduct t u iht ihu =>
    change (P.rep (t # (.leaf ◂ u))).natDegree ≤ treeGrade (t # (.leaf ◂ u))
    rw [P.rep_join, treeGrade_rootedSum, treeGrade_unary]
    have udeg : (P.rep (.leaf ◂ u)).natDegree ≤ treeGrade u + 1 := by
      rw [P.rep_unary]
      exact (P.reduce_degree _).trans (primitive_natDegree_le ihu)
    exact (P.reduce_degree _).trans (natDegree_mul_le_of_le iht udeg)

private theorem weighted_reduction (w f : K[X]) (paid : w.natDegree + f.natDegree < p) :
    unitMoment (w * P.normal (P.project f)) = unitMoment (w * f) := by
  have left : (w * P.normal (P.project f)).natDegree < p :=
    (natDegree_mul_le_of_le (le_refl _) (P.reduce_degree f)).trans_lt paid
  calc
    unitMoment (w * P.normal (P.project f)) =
        unitMoment (P.normal (P.project (w * P.normal (P.project f)))) :=
      (P.paid_reduction _ left).symm
    _ = unitMoment (P.normal (P.project (w * f))) := by
      simp only [map_mul, P.retract]
    _ = unitMoment (w * f) := P.paid_reduction _ (natDegree_mul_le.trans_lt paid)

private def Ref (t : FiniteRootedTree) : Prop :=
  ∀ w : K[X], w.natDegree + treeGrade t < p →
    ((t.forestFactorial : ℕ) : K) * unitMoment (w * P.rep t) =
      unitMoment (w * X ^ treeGrade t)

private theorem ref_join (t u : FiniteRootedTree) (ht : P.Ref t) (hu : P.Ref u) :
    P.Ref (t # u) := by
  intro w paid
  simp only [treeGrade_rootedSum] at paid ⊢
  have td := P.rep_degree t
  have ud := P.rep_degree u
  have prodBound : (P.rep t * P.rep u).natDegree ≤ treeGrade t + treeGrade u :=
    natDegree_mul_le_of_le td ud
  have b₁ : (w * P.rep u).natDegree + treeGrade t < p := by
    have h := natDegree_mul_le_of_le (le_refl w.natDegree) ud
    omega
  have b₂ : (w * X ^ treeGrade t).natDegree + treeGrade u < p := by
    have h := natDegree_mul_le_of_le (le_refl w.natDegree)
      (natDegree_X_pow_le (R := K) (treeGrade t))
    omega
  rw [forestFactorial_rootedSum, PNat.mul_coe, Nat.cast_mul, P.rep_join,
    P.weighted_reduction _ _ (by omega : w.natDegree + (P.rep t * P.rep u).natDegree < p),
    pow_add]
  calc
    _ = ((u.forestFactorial : ℕ) : K) *
        (((t.forestFactorial : ℕ) : K) * unitMoment ((w * P.rep u) * P.rep t)) := by
      rw [show w * (P.rep t * P.rep u) = (w * P.rep u) * P.rep t by ac_rfl]
      ac_rfl
    _ = ((u.forestFactorial : ℕ) : K) * unitMoment ((w * P.rep u) * X ^ treeGrade t) := by
      rw [ht _ b₁]
    _ = ((u.forestFactorial : ℕ) : K) * unitMoment ((w * X ^ treeGrade t) * P.rep u) := by
      rw [show (w * P.rep u) * X ^ treeGrade t = (w * X ^ treeGrade t) * P.rep u by ac_rfl]
    _ = unitMoment ((w * X ^ treeGrade t) * X ^ treeGrade u) := hu _ b₂
    _ = _ := by rw [mul_assoc]

private theorem ref_unary (units : PaidUnits K p) (t : FiniteRootedTree) (ht : P.Ref t) :
    P.Ref (.leaf ◂ t) := by
  intro w paid
  simp only [treeGrade_unary] at paid ⊢
  let test : K[X] := C (unitMoment w) - primitive w
  have degT : test.natDegree ≤ w.natDegree + 1 := by
    have hc : (C (unitMoment w)).natDegree ≤ w.natDegree + 1 := by
      simpa only [Polynomial.natDegree_C] using Nat.zero_le (w.natDegree + 1)
    exact (natDegree_sub_le (C (unitMoment w)) (primitive w)).trans
      (max_le hc (primitive_natDegree_le (le_refl w.natDegree)))
  have degree := P.rep_degree t
  have primDegree := primitive_natDegree_le degree
  have exactRep := unitMoment_byParts units w (P.rep t) (by omega)
  have exactPower := unitMoment_byParts units w (X ^ treeGrade t)
    (by rw [natDegree_X_pow]; omega)
  have tested := ht test (by omega)
  have orderEq := treeGrade_succ t
  have nz := units (t.order : ℕ) t.order.pos (by omega)
  have cancel : ((t.order : ℕ) : K) * ((treeGrade t + 1 : ℕ) : K)⁻¹ = 1 := by
    rw [orderEq, mul_inv_cancel₀ nz]
  simp only [forestFactorial, one_mul, PNat.mul_coe, Nat.cast_mul, P.rep_unary]
  rw [P.weighted_reduction _ _ (by omega : w.natDegree + (primitive (P.rep t)).natDegree < p)]
  calc
    _ = ((t.order : ℕ) : K) *
        (((t.forestFactorial : ℕ) : K) * unitMoment (test * P.rep t)) := by
      rw [mul_assoc, exactRep]
    _ = ((t.order : ℕ) : K) * unitMoment (test * X ^ treeGrade t) := by rw [tested]
    _ = ((t.order : ℕ) : K) * unitMoment (w * primitive (X ^ treeGrade t)) := by
      rw [exactPower]
    _ = unitMoment (w * X ^ (treeGrade t + 1)) := by
      rw [primitive_power, mul_smul_comm, map_smul, smul_eq_mul, ← mul_assoc, cancel, one_mul]

private theorem reference (units : PaidUnits K p) (t : FiniteRootedTree) : P.Ref t := by
  induction t with
  | leaf =>
    intro w paid
    have h := P.weighted_reduction w (1 : K[X]) (by
      simpa only [treeGrade_leaf, natDegree_one] using paid)
    simpa only [P.rep_leaf, forestFactorial, PNat.one_coe, Nat.cast_one, one_mul,
      treeGrade_leaf, pow_zero] using h
  | butcherProduct t u ht hu =>
    change P.Ref (t # (.leaf ◂ u))
    exact P.ref_join t (.leaf ◂ u) ht (P.ref_unary units u hu)

/-- One model pays every order-prescribed literal output and, by insertion,
every cell of the whole nonrectangular order-paid context board. -/
theorem hasOrder (units : PaidUnits K p) : P.model.HasOrder p := by
  intro t paid
  have ord := treeGrade_succ t
  have budget : treeGrade t < p := by omega
  have h := P.reference units t 1 (by simpa only [natDegree_one, zero_add] using budget)
  simp only [one_mul, unitMoment_power, treeGrade_succ] at h
  change ((t.factorial : ℕ) : K) * unitMoment (P.rep t) = 1
  rw [factorial, PNat.mul_coe, Nat.cast_mul, mul_assoc, h]
  exact mul_inv_cancel₀ (units (t.order : ℕ) t.order.pos paid)

end MomentProjection
end
end RKResearch.ContextCompletion

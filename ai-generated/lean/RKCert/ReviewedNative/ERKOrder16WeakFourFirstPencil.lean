module

public import RKCert.ReviewedNative.ERKOrder16WeakFourPorts
public import RKCert.ReviewedNative.OrderedNodalGain
public import RKCert.ReviewedNative.PositiveIntervalGrid19
public import RKCert.ReviewedNative.OrderedPolynomialSignStrips
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The reviewed weak-four first pair forces a two-dimensional pencil

No new order predicate or tableau is introduced. The weak-four chronological
port, already earned from the reviewed rooted-sum conditions, is weakened to
the two first primitive zeros and the seven exact global moments. The polynomial
kernel is the existing native Cauchy moment lemma.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial RKCert.Endpoint
open RKResearch.Certified.Graded
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.OrderedPolynomialSignStrips

universe u
noncomputable section
variable {K : Type u} [Field K] [CharZero K]

def WeightedSix (F : K[X]) : Prop :=
  ∀ i : Fin 7, (primitive (X^i.val*(X*F))).eval 1 = 0

/-- All actual hypotheses needed by the first-only argument, even when the
hull is arbitrary and it has a root at the right endpoint. -/
structure FirstStopPacket (Q Z : K[X]) (a : K) : Prop where
  fitNonzero : Q ≠ 0
  fitDegree : Q.natDegree ≤ 4
  hullMonic : Z.Monic
  hullDegree : Z.natDegree = 4
  stopRoot : Z.IsRoot a
  stopNonzero : a ≠ 0
  first : integral 0 a (X*Q) = 0
  second : integral 0 a (X^2*Q) = 0
  weighted : WeightedSix (Q*Z)

theorem firstStopPacket_of_ports {Q Z : K[X]} {a c : K}
    (H : RKResearch.Certified.ERK16.WeakFourChronologicalPorts Q Z a c) :
    FirstStopPacket Q Z a := by
  refine ⟨H.Q_ne,H.Q_deg,H.Z_monic,H.Z_deg,H.firstRoot,H.firstNonzero,?_,?_,?_⟩
  · simpa only [integral_zero_left,formalPrimitive_eq_native] using H.firstConstant
  · rw [integral_zero_left,formalPrimitive_eq_native,pow_two,mul_assoc]
    exact H.firstLinear
  · intro i
    apply H.weighted
    rw [natDegree_X_pow]
    exact Nat.le_of_lt_succ i.isLt

theorem WeightedSix.detect {F : K[X]} (deg : F.natDegree ≤ 6)
    (H : WeightedSix F) : F = 0 :=
  NativeMoments.x_moments_detect deg H

private theorem primitive_C_mul (k : K) (F : K[X]) :
    primitive (C k * F) = C k * primitive F := by
  simpa only [Polynomial.smul_eq_C_mul] using primitive.map_smul k F

theorem WeightedSix.sub_C_mul {F P : K[X]} (H : WeightedSix F) (R : WeightedSix P) (k : K) :
    WeightedSix (F-C k*P) := by
  intro i
  have eq : X^i.val*(X*(F-C k*P)) = X^i.val*(X*F) - C k*(X^i.val*(X*P)) := by ring
  rw [eq,map_sub,eval_sub,primitive_C_mul,eval_mul,eval_C,H i,R i,mul_zero,sub_zero]

theorem FirstStopPacket.fitDegree_ge_three {Q Z : K[X]} {a : K}
    (H : FirstStopPacket Q Z a) : 3 ≤ Q.natDegree := by
  by_contra h
  have deg := natDegree_mul H.fitNonzero H.hullMonic.ne_zero
  rw [H.hullDegree] at deg
  exact (mul_ne_zero H.fitNonzero H.hullMonic.ne_zero) (H.weighted.detect (by omega))

/-- The three reference lists are independent of all tableau coordinates.
Their exact rational coefficient/moment receipts are a separate finite leaf. -/
def firstReferenceJ (K : Type u) [Field K] : K[X] :=
  @ofFn K _ (Classical.decEq K) 8 ![-8,252,-2520,11550,-27720,36036,-24024,6435]

def firstReferenceK (K : Type u) [Field K] : K[X] :=
  @ofFn K _ (Classical.decEq K) 8 ![-36,840,-6930,27720,-60060,72072,-45045,11440]

def firstReferenceL (K : Type u) [Field K] : K[X] :=
  @ofFn K _ (Classical.decEq K) 8 ![-8,280,-3080,15400,-40040,56056,-40040,11440]

def firstReferenceP₀ (K : Type u) [Field K] : K[X] :=
  X*firstReferenceK K

def firstReferenceP₁ (K : Type u) [Field K] : K[X] :=
  (X-1)*firstReferenceL K

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Exactly the finite reference equalities/signs used in the structural
reduction. The root strips and stopped sign boxes are not fields here. -/
structure FirstPencilReferences (J P₀ P₁ : K[X]) : Prop where
  jDegree : J.natDegree = 7
  pDegree : P₀.natDegree = 8
  jWeighted : WeightedSix J
  pWeighted : WeightedSix P₀
  identity : P₁ = P₀-J
  lead : 0 < P₀.leadingCoeff
  jAtZero : J.eval 0 < 0
  jAtOne : 0 < J.eval 1
  pAtZero : P₀.eval 0 = 0
  pAtOne : P₀.eval 1 = J.eval 1

private theorem remove_top {F P : K[X]} {n : ℕ}
    (f : F.natDegree ≤ n+1) (p : P.natDegree = n+1) (lc : P.leadingCoeff ≠ 0) :
    (F-C (F.coeff (n+1)/P.leadingCoeff)*P).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  simp only [coeff_sub,coeff_C_mul]
  by_cases ei : i=n+1
  · subst i
    rw [← p,coeff_natDegree]
    rw [p]
    rw [div_mul_cancel₀ _ lc,sub_self]
  · have a : F.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have b : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [a,b,mul_zero,sub_zero]

theorem FirstPencilReferences.cubic_kernel {J P₀ P₁ F : K[X]}
    (R : FirstPencilReferences J P₀ P₁) (d : F.natDegree = 7)
    (H : WeightedSix F) :
    ∃ c : K, c ≠ 0 ∧ F = C c*J := by
  let c := F.coeff 7/J.leadingCoeff
  have fj : J ≠ 0 := by
    have hd := R.jDegree
    intro e
    simp [e] at hd
  have lc := leadingCoeff_ne_zero.mpr fj
  have dz : (F-C c*J).natDegree ≤ 6 := remove_top d.le R.jDegree lc
  have top : F.coeff 7 ≠ 0 := by
    rw [← d,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by intro e; simp [e] at d)
  exact ⟨c,div_ne_zero top lc,sub_eq_zero.mp ((H.sub_C_mul R.jWeighted c).detect dz)⟩

theorem FirstPencilReferences.quartic_kernel {J P₀ P₁ F : K[X]}
    (R : FirstPencilReferences J P₀ P₁) (d : F.natDegree = 8)
    (H : WeightedSix F) :
    ∃ (c u : K), c ≠ 0 ∧ F = C c*(P₀+C u*J) := by
  let c := F.coeff 8/P₀.leadingCoeff
  let G := F-C c*P₀
  have cd : c ≠ 0 := by
    apply div_ne_zero _ (ne_of_gt R.lead)
    rw [← d,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by intro e; simp [e] at d)
  have gd : G.natDegree ≤ 7 := remove_top d.le R.pDegree (ne_of_gt R.lead)
  have jn : J ≠ 0 := by
    have hd := R.jDegree
    intro e
    simp [e] at hd
  let b := G.coeff 7/J.leadingCoeff
  have bd : (G-C b*J).natDegree ≤ 6 :=
    remove_top gd R.jDegree (leadingCoeff_ne_zero.mpr jn)
  have z := (((H.sub_C_mul R.pWeighted c).sub_C_mul R.jWeighted b).detect bd)
  have hF : F = C c*P₀+C b*J := by
    change (F-C c*P₀)-C b*J = 0 at z
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp z)).trans (add_comm _ _)
  refine ⟨c,b/c,cd,?_⟩
  have cb : c*(b/c)=b := by field_simp
  rw [hF,mul_add,←mul_assoc,←C_mul,cb]

/-- The given first-only packet is exactly cubic or quartic. Both
representations retain the original Q, Z and stopped point. -/
theorem FirstStopPacket.represent {Q Z J P₀ P₁ : K[X]} {a : K}
    (H : FirstStopPacket Q Z a) (R : FirstPencilReferences J P₀ P₁) :
    (Q.natDegree = 3 ∧ ∃ c : K, c ≠ 0 ∧ Q*Z = C c*J) ∨
    (Q.natDegree = 4 ∧ ∃ (c u : K), c ≠ 0 ∧ Q*Z = C c*(P₀+C u*J)) := by
  have ge := H.fitDegree_ge_three
  have le := H.fitDegree
  have d := natDegree_mul H.fitNonzero H.hullMonic.ne_zero
  rw [H.hullDegree] at d
  by_cases h : Q.natDegree = 3
  · exact Or.inl ⟨h,R.cubic_kernel (by omega) H.weighted⟩
  · exact Or.inr ⟨by omega,R.quartic_kernel (by omega) H.weighted⟩

end
end RKCert.ReviewedNative.WeakFourFirstOnly

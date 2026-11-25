module

public import RKCert.ReviewedNative.WeakFiveSoleInnerExteriorMean
public import RKCert.ReviewedNative.WeakFivePrimitiveBalance
public import RKCert.ReviewedNative.CrossedGaussianSignedAdapter

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Positive ordinary degree-twelve rule with the true exterior mark

The sole exterior inner clock is retained as a real Radau node. No
reference clocks, profile coefficient tables, or resultants are used. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInner

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells (PaidSix rawFourHull)
open scoped Polynomial BigOperators Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1600000

def profile (e r₀ r₁ r₂ : K) : K[X] := (X-C e)*cubic r₀ r₁ r₂

def inside (u h z r₀ r₁ r₂ : K) : Finset K := ({z,h,u} : Finset K) ∪ {r₀,r₁,r₂}
def radauSites (a u h z r₀ r₁ r₂ : K) : Finset K := insert a (inside u h z r₀ r₁ r₂)

def baseMoment (e : K) : K[X] →ₗ[K] K := unitMoment (X-C e)

structure OrientedPorts (a e u h z r₀ r₁ r₂ : K) : Prop where
  ae : a < e
  eNeg : e < 0
  zUnit : z ∈ Set.Ioo 0 1
  uUnit : u ∈ Set.Ioo 0 1
  hUnit : h ∈ Set.Ioo 0 1
  zu : z < u
  hz : h ≠ z
  hu : h ≠ u
  roots0 : r₀ ∈ Set.Ioo 0 1
  roots1 : r₁ ∈ Set.Ioo 0 1
  roots2 : r₂ ∈ Set.Ioo 0 1
  roots01 : r₀ < r₁
  roots12 : r₁ < r₂
  marksLive : ∀ x ∈ ({z,h,u} : Finset K), (profile e r₀ r₁ r₂).eval x ≠ 0
  forwardFirst : integral 0 u (X*profile e r₀ r₁ r₂)=0
  forwardSecond : integral 0 u (X^2*profile e r₀ r₁ r₂)=0
  forwardInner : integral 0 a (X*(X-C u)*profile e r₀ r₁ r₂)=0
  reverseFirst : integral z 1 ((1-X)*profile e r₀ r₁ r₂)=0
  reverseSecond : integral z 1 ((1-X)^2*profile e r₀ r₁ r₂)=0
  reverseInner : integral h 1 ((1-X)*(C z-X)*profile e r₀ r₁ r₂)=0
  global : PaidSix (profile e r₀ r₁ r₂) u a h z

/-- The six literal linear tests on the interior-root cubic. This is one
finite kernel on polynomials of degree at most three, not a rank assertion
on a sample-dependent subset. -/
def localProbe (a e u h z : K) : K[X] →ₗ[K] (Fin 6 → K) :=
  LinearMap.pi ![weighted (integral 0 u) (X*(X-C e)),
    weighted (integral 0 u) (X^2*(X-C e)),
    weighted (integral 0 a) (X*(X-C u)*(X-C e)),
    weighted (integral z 1) ((1-X)*(X-C e)),
    weighted (integral z 1) ((1-X)^2*(X-C e)),
    weighted (integral h 1) ((1-X)*(C z-X)*(X-C e))]

theorem OrientedPorts.local_kernel {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) :
    localProbe a e u h z (cubic r₀ r₁ r₂) = 0 := by
  funext i
  fin_cases i
  · change integral 0 u ((X*(X-C e))*cubic r₀ r₁ r₂)=0
    simpa only [profile,mul_assoc] using B.forwardFirst
  · change integral 0 u ((X^2*(X-C e))*cubic r₀ r₁ r₂)=0
    simpa only [profile,mul_assoc] using B.forwardSecond
  · change integral 0 a ((X*(X-C u)*(X-C e))*cubic r₀ r₁ r₂)=0
    simpa only [profile,mul_assoc] using B.forwardInner
  · change integral z 1 (((1-X)*(X-C e))*cubic r₀ r₁ r₂)=0
    simpa only [profile,mul_assoc] using B.reverseFirst
  · change integral z 1 (((1-X)^2*(X-C e))*cubic r₀ r₁ r₂)=0
    simpa only [profile,mul_assoc] using B.reverseSecond
  · change integral h 1 (((1-X)*(C z-X)*(X-C e))*cubic r₀ r₁ r₂)=0
    simpa only [profile,mul_assoc] using B.reverseInner

private theorem cubic_monic (r₀ r₁ r₂ : K) : (cubic r₀ r₁ r₂).Monic :=
  ((monic_X_sub_C r₀).mul (monic_X_sub_C r₁)).mul (monic_X_sub_C r₂)

theorem cubic_degree (r₀ r₁ r₂ : K) : (cubic r₀ r₁ r₂).natDegree = 3 := by
  unfold cubic
  rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _),
    natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)]
  simp only [natDegree_X_sub_C]

/-- The six functionals on the four ordinary monomials. -/
def windowMatrix (a e u h z : K) : Matrix (Fin 6) (Fin 4) K :=
  fun i j => localProbe a e u h z (X^j.val) i

/-- The explicit coefficient kernel is nonzero, with no linear
independence assumption on the moment probes. -/
theorem OrientedPorts.matrix_kernel {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) :
    ∃ v : Fin 4 → K, v 3 = 1 ∧ windowMatrix a e u h z *ᵥ v = 0 := by
  let R := cubic r₀ r₁ r₂
  let v := toFn 4 R
  have degree : R.natDegree = 3 := cubic_degree _ _ _
  have rep : (∑ j : Fin 4, monomial j.val (v j))=R :=
    (ofFn_eq_sum_monomial v).symm.trans (ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega))
  have pivot : v 3 = 1 := by
    change R.coeff 3 = 1
    rw [← degree, coeff_natDegree]
    exact (cubic_monic r₀ r₁ r₂).leadingCoeff
  refine ⟨v,pivot,?_⟩
  funext i
  have vanish : localProbe a e u h z R=0 := B.local_kernel
  have rep' : (∑ j : Fin 4, v j • (X : K[X]) ^ j.val) = R := by
    simpa only [Polynomial.smul_eq_C_mul,C_mul_X_pow_eq_monomial] using rep
  rw [←rep',map_sum] at vanish
  have hi : (∑ j : Fin 4, v j * localProbe a e u h z (X^j.val) i) = 0 := by
    simpa only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      using congrFun vanish i
  change (∑ j : Fin 4, localProbe a e u h z (X^j.val) i * v j) = 0
  calc
    _ = (∑ j : Fin 4, v j * localProbe a e u h z (X^j.val) i) :=
      Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    _ = 0 := hi

private theorem inside_unit {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) {x : K}
    (hx : x ∈ inside u h z r₀ r₁ r₂) : x ∈ Set.Ioo 0 1 := by
  simp only [inside,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact B.zUnit
  · exact B.hUnit
  · exact B.uUnit
  · exact B.roots0
  · exact B.roots1
  · exact B.roots2

private theorem six_data {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) :
    (inside u h z r₀ r₁ r₂).card = 6 ∧
      Lagrange.nodal (inside u h z r₀ r₁ r₂) id =
        ((X-C u)*(X-C z)*(X-C h))*cubic r₀ r₁ r₂ := by
  let marks : Finset K := {z,h,u}
  let roots : Finset K := {r₀,r₁,r₂}
  have hU : h ∉ ({u}:Finset K) := by simp [B.hu]
  have zH : z ∉ ({h,u}:Finset K) := by simp [B.hz.symm,B.zu.ne]
  have r₁₂ : r₁ ∉ ({r₂}:Finset K) := by simp [B.roots12.ne]
  have r₀₁₂ : r₀ ∉ ({r₁,r₂}:Finset K) := by
    simp [B.roots01.ne,(B.roots01.trans B.roots12).ne]
  have cm : marks.card = 3 := by
    unfold marks
    rw [Finset.card_insert_of_notMem zH,Finset.card_insert_of_notMem hU,Finset.card_singleton]
  have cr : roots.card = 3 := by
    unfold roots
    rw [Finset.card_insert_of_notMem r₀₁₂,Finset.card_insert_of_notMem r₁₂,Finset.card_singleton]
  have dis : Disjoint marks roots := Finset.disjoint_left.mpr (by
    intro x m r
    have neq := B.marksLive x m
    apply neq
    simp only [roots,Finset.mem_insert,Finset.mem_singleton] at r
    rcases r with rfl | rfl | rfl <;> simp [profile,cubic])
  have pm : Lagrange.nodal marks id = (X-C u)*(X-C z)*(X-C h) := by
    unfold marks
    rw [Lagrange.nodal_insert_eq_nodal zH,Lagrange.nodal_insert_eq_nodal hU,
      Lagrange.nodal_eq,Finset.prod_singleton]
    simp only [id_eq]
    ring
  have pr : Lagrange.nodal roots id = cubic r₀ r₁ r₂ := by
    unfold roots
    rw [Lagrange.nodal_insert_eq_nodal r₀₁₂,Lagrange.nodal_insert_eq_nodal r₁₂,
      Lagrange.nodal_eq,Finset.prod_singleton]
    simp only [cubic,id_eq]
    ring
  refine ⟨?_,?_⟩
  · change (marks ∪ roots).card = 6
    rw [Finset.card_union_of_disjoint dis,cm,cr]
  · change Lagrange.nodal (marks∪roots) id = _
    calc
      _ = Lagrange.nodal marks id*Lagrange.nodal roots id := by
        simp only [Lagrange.nodal_eq,Finset.prod_union dis]
      _ = _ := by rw [pm,pr]

private theorem add_exterior_node
    {a : K} {s : Finset K} {μ : K → K} (J : K[X] →ₗ[K] K)
    (fresh : a ∉ s) (law : ExactRule (weighted J (X-C a)) s id μ 11) :
    ExactRule J (insert a s) id
      (fun x=>if x=a then J 1-∑ y ∈ s, μ y/(y-a) else μ x/(x-a)) 12 := by
  intro P pd
  let D : K[X] := X-C a
  have mon : D.Monic := monic_X_sub_C a
  let Q := P /ₘ D
  have qd : Q.natDegree ≤ 11 := by
    change (P /ₘ D).natDegree ≤ 11
    rw [natDegree_divByMonic P mon,show D.natDegree=1 from natDegree_X_sub_C a]
    omega
  have e : P=C (P.eval a)+D*Q := by
    have shape := modByMonic_add_div P D
    simpa only [D,Q,modByMonic_X_sub_C_eq_C_eval] using shape.symm
  have v (x : K) (hx : x ∈ s) : μ x*(Q.eval x) =
      (μ x/(x-a))*P.eval x-(μ x/(x-a))*P.eval a := by
    have nz : x-a ≠ 0 := sub_ne_zero.mpr (fun eq=>fresh (eq ▸ hx))
    have val : P.eval x=P.eval a+(x-a)*Q.eval x := by
      conv_lhs => rw [e]
      simp only [D,eval_add,eval_mul,eval_C,eval_sub,eval_X]
    rw [val]
    field_simp [nz] <;> ring
  have j : J P = (P.eval a)*J 1+weighted J D Q := by
    rw [weighted_apply]
    conv_lhs => rw [e]
    rw [map_add, show C (P.eval a)=P.eval a • (1:K[X]) by rw [Polynomial.smul_eq_C_mul,mul_one],
      map_smul,smul_eq_mul]
  rw [j,law Q qd,Finset.sum_insert fresh]
  simp only [id_eq,eq_self,ite_true]
  have right : (∑ x ∈ s, (if x=a then J 1-∑ y ∈ s, μ y/(y-a) else μ x/(x-a))*P.eval x) =
      ∑ x ∈ s, (μ x/(x-a))*P.eval x := by
    apply Finset.sum_congr rfl
    intro x hx
    have xna : x ≠ a := fun eq => fresh (eq ▸ hx)
    rw [ite_eq_right xna]
  rw [right]
  have plus : (∑ x ∈ s, μ x*Q.eval x) =
      (∑ x ∈ s, (μ x/(x-a))*P.eval x) - (∑ x ∈ s, μ x/(x-a))*P.eval a := by
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl v
  rw [plus]
  ring

/-- The three actual unit zeros and three unit marks pay the six-node
Gauss rule. Exact division by the true exterior mark earns a positive
seventh mass at that mark, and exactness through degree twelve. -/
theorem OrientedPorts.radau {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) :
    ∃ μ : K → K, ExactRule (baseMoment e) (radauSites a u h z r₀ r₁ r₂) id μ 12 ∧
      ∀ x ∈ radauSites a u h z r₀ r₁ r₂, 0 < μ x := by
  let s := inside u h z r₀ r₁ r₂
  let D : K[X] := (X-C e)*(X-C a)
  let J := baseMoment e
  obtain ⟨count,nodal⟩ := six_data B
  have aNeg := B.ae.trans B.eNeg
  have fresh : a ∉ s := fun hx => (not_lt_of_ge aNeg.le) (inside_unit B hx).1
  have orth (P : K[X]) (pd : P.natDegree ≤ s.card-1) :
      unitMoment D (Lagrange.nodal s id*P)=0 := by
    have p₅ : P.natDegree ≤ 5 := pd.trans (by change (inside u h z r₀ r₁ r₂).card-1≤5; rw [count])
    have pay := B.global P p₅
    rw [unitMoment_apply,show Lagrange.nodal s id =
      ((X-C u)*(X-C z)*(X-C h))*cubic r₀ r₁ r₂ from nodal]
    change integral 0 1 (X*(1-X)*(profile e r₀ r₁ r₂*rawFourHull u a h z)*P) = 0 at pay
    refine (congrArg (fun F : K[X]=>integral 0 1 F) ?_).trans pay
    simp only [unitWeight,D,profile,rawFourHull]
    ring
  let μ := cardinalMass (unitMoment D) s id
  have law₆ : ExactRule (unitMoment D) s id μ 11 := by
    have pay := gaussian_exact_of_annihilates (unitMoment D) s id Function.injective_id.injOn orth
    have n : s.card=6 := count
    rwa [n] at pay
  have dpos {x : K} (x₀ : 0<x) : 0 < D.eval x := by
    simp only [D,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (sub_pos.mpr (B.eNeg.trans x₀)) (sub_pos.mpr (aNeg.trans x₀))
  have bd : D.natDegree ≤ 2 :=
    natDegree_mul_le_of_le (m:=1) (n:=1) (by simp) (by simp)
  have mass₆ (x : K) (hx : x ∈ s) : 0 < μ x := by
    refine unit_gaussian_mass_pos D (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
      bd ?_ count Function.injective_id.injOn law₆ hx
    intro j
    exact (dpos (intervalPoint_mem zero_lt_one j).1).le
  have lawD : ExactRule (weighted J (X-C a)) s id μ 11 := by
    intro P pd
    have eq : weighted J (X-C a) P = unitMoment D P := by
      simp only [J,baseMoment,weighted_apply,unitMoment_apply,D]
      congr 1
      ring
    rw [eq,law₆ P pd]
  let ν (x : K) := if x=a then J 1-∑ y ∈ s, μ y/(y-a) else μ x/(x-a)
  have law₇ : ExactRule J (insert a s) id ν 12 := add_exterior_node J fresh lawD
  refine ⟨ν, law₇,?_⟩
  intro x hx
  by_cases xa : x=a
  · subst x
    let N := Lagrange.nodal s id
    have nz : N.eval a ≠ 0 := by
      apply Lagrange.eval_nodal_not_at_node
      intro y hy e
      change a=y at e
      exact fresh (e.symm ▸ hy)
    have Nd : N.natDegree = 6 := Lagrange.natDegree_nodal.trans count
    have d : (N^2).natDegree ≤ 12 := natDegree_pow_le_of_le 2 Nd.le
    have pos : 0 < J (N^2) := by
      change 0 < integral 0 1 ((unitWeight K*(X-C e))*N^2)
      have cap : (unitWeight K*(X-C e)).natDegree ≤ 3 :=
        natDegree_mul_le_of_le (m:=2) (n:=1) unitWeight_degree (natDegree_X_sub_C e).le
      apply integral_pos_of_grid_nonneg zero_lt_one _
        (mul_ne_zero (mul_ne_zero unitWeight_nonzero (X_sub_C_ne_zero _))
          (pow_ne_zero _ (fun zero=>nz (by rw [zero,eval_zero]))))
        ((natDegree_mul_le_of_le cap d).trans_lt (by decide))
      intro i
      let x := intervalPoint (0:K) 1 i
      have hx : x ∈ Set.Ioo (0 : K) 1 := intervalPoint_mem (zero_lt_one : (0 : K) < 1) i
      change 0 ≤ ((unitWeight K*(X-C e))*N^2).eval x
      simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]
      exact mul_nonneg (mul_nonneg (unitWeight_eval_pos hx.1 hx.2).le
        (sub_nonneg.mpr (B.eNeg.trans hx.1).le)) (sq_nonneg _)
    rw [law₇ _ d,Finset.sum_insert fresh] at pos
    have rest : (∑ x ∈ s, ν x*(N^2).eval (id x))=0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have no : N.eval (id y)=0 := Lagrange.eval_nodal_at_node hy
      simp only [eval_pow,no,zero_pow (by decide : (2:ℕ)≠0),mul_zero]
    rw [rest,add_zero] at pos
    have nn : 0 ≤ (N^2).eval (id a) := by rw [eval_pow]; exact sq_nonneg _
    exact pos_of_mul_pos_left pos nn
  · have h : x ∈ s := (Finset.mem_insert.mp hx).resolve_left xa
    rw [show ν x=μ x/(x-a) from if_neg xa]
    exact div_pos (mass₆ x h) (sub_pos.mpr (aNeg.trans (inside_unit B h).1))

/-- All remaining local rank conditions on the same positive Radau layout.
A genuine scalar exclusion needs only rule out this joint packet. -/
structure RankedPacket (a e u h z r₀ r₁ r₂ : K) : Prop where
  ports : OrientedPorts a e u h z r₀ r₁ r₂
  exteriorScale : (2:K)/3*(-a) < -e ∧ -e < (6:K)/7*(-a)
  rule : ∃ μ : K → K, ExactRule (baseMoment e) (radauSites a u h z r₀ r₁ r₂) id μ 12 ∧
    ∀ x ∈ radauSites a u h z r₀ r₁ r₂, 0 < μ x
  kernel : localProbe a e u h z (cubic r₀ r₁ r₂) = 0

theorem OrientedPorts.ranked {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) :
    RankedPacket a e u h z r₀ r₁ r₂ :=
  ⟨B, exterior_mean_bounds (B.ae.trans B.eNeg) B.uUnit.1 B.roots0.1 B.roots1.1 B.roots2.1
    B.forwardInner, B.radau, B.local_kernel⟩

end
end RKCert.ReviewedNative.WeakFiveSoleInner

module

public import RKCert.ReviewedNative.SDIRKSixFourScalar
public import RKCert.ReviewedNative.SDIRKSixSupport
public import RKCert.ReviewedNative.SDIRKSixAlgebra
public import RKCert.ReviewedNative.SDIRKSixWeighted
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid coefficient arithmetic in the actual SDIRK6 physical proof

This module reuses the reviewed order, physical front/terminal producers,
tree-space rank, and support. It weakens only the explicit coefficient
hypotheses in the old character-zero wrappers. All inverses that occur
in the operator expectations are fixed tree factorials at order ≤ 6. -/
namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix
open RKCert.Paired.SDIRK.P6
open RKCert.ReviewedNative.SDIRKSixReceipts (isUnit_of_dvd_paid_power fourExceptionProduct)

variable {K : Type*} [Field K] {s : ℕ}

set_option maxRecDepth 12000

/-- Reviewed order-six quadrature already pays for the scalar chart. -/
private theorem paid_thirty {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder 6 A b) : IsUnit (30 : K) := by
  have h₂ : IsUnit (2 : K) := ho.natCast_isUnit (n := 2) (by decide) (by decide)
  have h₃ : IsUnit (3 : K) := ho.natCast_isUnit (n := 3) (by decide) (by decide)
  have h₅ : IsUnit (5 : K) := ho.natCast_isUnit (n := 5) (by decide) (by decide)
  have h : (2 : K) * 3 * 5 = 30 := by norm_num
  rw [← h]
  exact (h₂.mul h₃).mul h₅

private theorem leg3c_silent_paid {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder 6 A b) (h30 : IsUnit (30 : K)) : leg3c A ∈ silent A b 3 2 := by
  have hn2 : (2 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 2) (by decide)).ne_zero
  have hn3 : (3 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 3) (by decide)).ne_zero
  have hn4 : (4 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 4) (by decide)).ne_zero
  have hn5 : (5 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 5) (by decide)).ne_zero
  have hn6 : (6 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 6) (by decide)).ne_zero
  have hn8 : (8 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 8) (by decide)).ne_zero
  have hn10 : (10 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 10) (by decide)).ne_zero
  have hn12 : (12 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 12) (by decide)).ne_zero
  have hn15 : (15 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 15) (by decide)).ne_zero
  have hn18 : (18 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 18) (by decide)).ne_zero
  have hn24 : (24 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 24) (by decide)).ne_zero
  have hn30 : (30 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 30) (by decide)).ne_zero
  have hn36 : (36 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 36) (by decide)).ne_zero
  have hn60 : (60 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 60) (by decide)).ne_zero
  have hn120 : (120 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 120) (by decide)).ne_zero
  have hn360 : (360 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 360) (by decide)).ne_zero
  have hn720 : (720 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 720) (by decide)).ne_zero
  apply silent_mem.mpr ⟨coeffEval_mem_treeSpace A 3 _, ?_⟩
  intro k
  rw [probe_coeffEval ho (by omega)]
  fin_cases k <;> norm_num [Fin.sum_univ_succ] <;>
    field_simp [hn2, hn3, hn4, hn5, hn6, hn8, hn10, hn12, hn15, hn18, hn24, hn30, hn36, hn60, hn120, hn360, hn720] <;> ring

namespace Op

set_option maxHeartbeats 8000000 in
theorem zero_word_paid {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} (ho : HasOrder 6 A b) (h30 : IsUnit (30 : K))
    (z u v : K) : 720 * row b (eval A (first z (J2 z)) 1) = -zeroLaguerre z u v := by
  have hn2 : (2 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 2) (by decide)).ne_zero
  have hn3 : (3 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 3) (by decide)).ne_zero
  have hn4 : (4 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 4) (by decide)).ne_zero
  have hn5 : (5 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 5) (by decide)).ne_zero
  have hn6 : (6 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 6) (by decide)).ne_zero
  have hn8 : (8 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 8) (by decide)).ne_zero
  have hn10 : (10 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 10) (by decide)).ne_zero
  have hn12 : (12 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 12) (by decide)).ne_zero
  have hn15 : (15 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 15) (by decide)).ne_zero
  have hn18 : (18 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 18) (by decide)).ne_zero
  have hn24 : (24 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 24) (by decide)).ne_zero
  have hn30 : (30 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 30) (by decide)).ne_zero
  have hn36 : (36 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 36) (by decide)).ne_zero
  have hn60 : (60 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 60) (by decide)).ne_zero
  have hn120 : (120 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 120) (by decide)).ne_zero
  have hn360 : (360 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 360) (by decide)).ne_zero
  have hn720 : (720 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 720) (by decide)).ne_zero
  rw [expectation_eq ho _ (by simp [height,first,J2,N])]
  norm_num [expectation,foldTree,first,J2,N,zeroLaguerre,factorial,order,forestFactorial,PNat.mul_coe,PNat.add_coe,PNat.one_coe] <;>
  field_simp [hn2, hn3, hn4, hn5, hn6, hn8, hn10, hn12, hn15, hn18, hn24, hn30, hn36, hn60, hn120, hn360, hn720] <;> ring

set_option maxHeartbeats 8000000 in
theorem first_word_paid {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} (ho : HasOrder 6 A b) (h30 : IsUnit (30 : K))
    (z u v : K) : 720 * row b (eval A (first z (H z u)) 1) = bridge1 z u v := by
  have hn2 : (2 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 2) (by decide)).ne_zero
  have hn3 : (3 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 3) (by decide)).ne_zero
  have hn4 : (4 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 4) (by decide)).ne_zero
  have hn5 : (5 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 5) (by decide)).ne_zero
  have hn6 : (6 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 6) (by decide)).ne_zero
  have hn8 : (8 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 8) (by decide)).ne_zero
  have hn10 : (10 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 10) (by decide)).ne_zero
  have hn12 : (12 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 12) (by decide)).ne_zero
  have hn15 : (15 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 15) (by decide)).ne_zero
  have hn18 : (18 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 18) (by decide)).ne_zero
  have hn24 : (24 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 24) (by decide)).ne_zero
  have hn30 : (30 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 30) (by decide)).ne_zero
  have hn36 : (36 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 36) (by decide)).ne_zero
  have hn60 : (60 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 60) (by decide)).ne_zero
  have hn120 : (120 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 120) (by decide)).ne_zero
  have hn360 : (360 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 360) (by decide)).ne_zero
  have hn720 : (720 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 720) (by decide)).ne_zero
  rw [expectation_eq ho _ (by simp [height,first,J2,N,H,Q,X])]
  norm_num [expectation,foldTree,first,J2,N,H,Q,X,D,bridge1,factorial,order,forestFactorial,PNat.mul_coe,PNat.add_coe,PNat.one_coe] <;>
  field_simp [hn2, hn3, hn4, hn5, hn6, hn8, hn10, hn12, hn15, hn18, hn24, hn30, hn36, hn60, hn120, hn360, hn720] <;> ring

set_option maxHeartbeats 8000000 in
theorem second_word_paid {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} (ho : HasOrder 6 A b) (h30 : IsUnit (30 : K))
    (z u v : K) : 120 * row b (eval A (second z v (H z u)) 1) = bridge2 z u v := by
  have hn2 : (2 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 2) (by decide)).ne_zero
  have hn3 : (3 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 3) (by decide)).ne_zero
  have hn4 : (4 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 4) (by decide)).ne_zero
  have hn5 : (5 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 5) (by decide)).ne_zero
  have hn6 : (6 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 6) (by decide)).ne_zero
  have hn8 : (8 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 8) (by decide)).ne_zero
  have hn10 : (10 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 10) (by decide)).ne_zero
  have hn12 : (12 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 12) (by decide)).ne_zero
  have hn15 : (15 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 15) (by decide)).ne_zero
  have hn18 : (18 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 18) (by decide)).ne_zero
  have hn24 : (24 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 24) (by decide)).ne_zero
  have hn30 : (30 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 30) (by decide)).ne_zero
  have hn36 : (36 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 36) (by decide)).ne_zero
  have hn60 : (60 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 60) (by decide)).ne_zero
  have hn120 : (120 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 120) (by decide)).ne_zero
  have hn360 : (360 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 360) (by decide)).ne_zero
  have hn720 : (720 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 720) (by decide)).ne_zero
  rw [expectation_eq ho _ (by simp [height,second,J2,N,H,Q,X,Y])]
  norm_num [expectation,foldTree,second,J2,N,H,Q,X,Y,D,bridge2,factorial,order,forestFactorial,PNat.mul_coe,PNat.add_coe,PNat.one_coe] <;>
  field_simp [hn2, hn3, hn4, hn5, hn6, hn8, hn10, hn12, hn15, hn18, hn24, hn30, hn36, hn60, hn120, hn360, hn720] <;> ring

end Op

private theorem normal_front_paid {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)} {γ : K}
    (ho : HasOrder 6 A b) (h30 : IsUnit (30 : K)) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) : Front (scaleTable γ⁻¹ A) γ⁻¹ := by
  let z := γ⁻¹
  let B := scaleTable z A
  change Front B z
  have hz : z*γ=1 := inv_mul_cancel₀ hγ
  have hl : B.IsLowerTriangular := by intro i j hij;change z*A i j=0;rw [@ha i j hij,mul_zero]
  have hd (i) : B i i=1 := by change z*A i i=1;rw [he,hz]
  have ht := first_tap_nonzero ho ha he hγ
  have h₀ : nodes B 0=1 := by rw [node_mat_one,at0 hl hd];simp
  have h₁ : nodes B 1=1+B 1 0 := by rw [node_mat_one,at1 hl hd];simp [add_comm]
  have hs : kap (B 1 0)=z^2*seed A 1 := by
    rw [seed1 ha he];change 1+2*(γ⁻¹*A 1 0)-(γ⁻¹*A 1 0)^2=_
    dsimp [z];field_simp
  have hq (i) : tapMap B 1 (seed B) i=z^3*tapMap A γ (seed A) i := by
    simp only [B,seed_scaleTable,map_smul,tap_scaleTable z γ A hz,Pi.smul_apply,smul_eq_mul];ring
  refine ⟨hl,hd,mul_ne_zero (inv_ne_zero hγ) ht,?_,?_,?_⟩
  · simp only [B,volterra_scaleTable,mat_scaleTable,map_smul,front_commutator ho ha he hγ,smul_smul]
    rw [mul_comm z (z^2)]
  · intro i
    have h := congrFun (front_clock_seed ho ha he hγ) i
    change γ^2*(nodes A i*seed A i-γ*seed A i)=seed A 1*tapMap A γ (seed A) i at h
    rw [hs,hq]
    simp only [B,nodes_scaleTable,seed_scaleTable,Pi.smul_apply,smul_eq_mul]
    dsimp [z];field_simp;linear_combination h
  · intro i
    have h := congrFun (cubic_reconstruction ho ha he hγ (leg3c A) (leg3c_silent_paid ho h30)) i
    change leg3c A i=(leg3c A 0/γ^2)*seed A i+
      ((leg3c A 1-(leg3c A 0/γ^2)*seed A 1)/(A 1 0*γ^2))*tapMap A γ (seed A) i at h
    rw [hs,hq,← h₁,← h₀]
    simp only [B,leg_scale,seed_scaleTable,scaleTable,Pi.smul_apply,smul_eq_mul]
    dsimp [z];field_simp at h ⊢;linear_combination h

private theorem zero_algebra_paid {z u w r : K} (v:K) (h2 : (2 : K) ≠ 0) (h : Third z u w r) (hu:u≠0)
    (hr:r=0) (hw:w≠0) (hwu:w≠u) : zeroCubic z u v=0 := by
  subst r
  have hc:=h.clock
  have hp : w*(w-u)*(2-w-u)=0 := by unfold kap at hc;linear_combination hc
  have hw' : w=2-u := by
    have hh := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero hw (sub_ne_zero.mpr hwu))
    linear_combination -hh
  subst w
  have hu1 : u-1≠0 := by intro hz;apply hwu;linear_combination -2*hz
  have hu2 : u-2≠0 := by intro hz;apply hw;linear_combination -hz
  have H:=h.leg3
  have hprod : ((-2:K)*u*(u-2)*(u-1))*zeroCubic z u v=0 := by
    unfold leg kap at H;unfold zeroCubic;linear_combination H
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hu) hu2) hu1)

private theorem nonzero_algebra_paid {z u w r : K} (v:K) (h2 : (2 : K) ≠ 0) (h : Third z u w r) (hu:u≠0) (hr:r≠0) :
    w=2*u ∧ Op.D u*r=2*u*(3*u-2) ∧ front z u v=0 := by
  have hw : w=2*u := by
    have hh := (mul_eq_zero.mp h.comm).resolve_left (mul_ne_zero hr hu)
    linear_combination -hh
  subst w
  have hc:=h.clock
  have hb : u*(Op.D u*r-2*u*(3*u-2))=0 := by unfold Op.D;unfold kap at hc;linear_combination hc
  have hd := sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hu)
  have hh:=h.leg3
  have ht : (-2*u^3)*front z u v=0 := by
    unfold leg kap at hh
    unfold front
    unfold Op.D at hd
    linear_combination (norm := ring_nf)
      (-2+u+4*u^2-u^3)*hh -
        (-2*u^2*(20-30*z+12*z^2-z^3)-
        ((20*(1+u)^3-30*z*(1+u)^2+12*z^2*(1+u)-z^3)-
         (1+2*u-u^2)*(20-30*z+12*z^2-z^3))*((1+2*u-u^2)-1))*hd
  exact ⟨rfl,hd,(mul_eq_zero.mp ht).resolve_left (mul_ne_zero (neg_ne_zero.mpr h2) (pow_ne_zero _ hu))⟩

/-- Necessary physical chart for an order-six, six-stage common-diagonal
tableau. The clocks are those of the normalized actual matrix; the chart
does not assert that an arbitrary scalar solution lifts to a tableau. -/
structure SixStageChart (A : Matrix (Fin 6) (Fin 6) K) (γ z u v : K) : Prop where
  paid : IsUnit (30 : K)
  z_ne : z ≠ 0
  z_eq : z = γ⁻¹
  u_eq : u = scaleTable z A 1 0
  v_eq : v = (nodes A 5 - nodes A 4) / γ
  front_data : Front (scaleTable z A) z
  seed_ratio : seed (scaleTable z A) 4 = kap v * seed (scaleTable z A) 5
  clock₀ : nodes (scaleTable z A) 0 = 1
  clock₁ : nodes (scaleTable z A) 1 = 1 + u
  clock₂ : nodes (scaleTable z A) 2 = 1 + 2*u
  clock₄ : nodes (scaleTable z A) 4 = z - 1 - v
  clock₅ : nodes (scaleTable z A) 5 = z - 1
  front_zero : front z u v = 0
  bridge1_zero : bridge1 z u v = 0
  bridge2_zero : bridge2 z u v = 0
  last_zero : kappa z u v = 0 ∨ terminal z u v = 0

/-- Recover scalar chart constraints and the five forced clocks.
The zero-tap branch is impossible in every characteristic allowed by the
order conditions. No exception integer is canceled by this theorem. -/
theorem order_six_six_stage_chart {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (hγ : γ ≠ 0) :
    ∃ z u v, SixStageChart A γ z u v := by
  have h30 := paid_thirty ho
  have hn2 : (2 : K) ≠ 0 := (isUnit_of_dvd_paid_power h30 (n := 2) (by decide)).ne_zero
  let z:=γ⁻¹
  let B:=scaleTable z A
  let u:=B 1 0
  let v:=(nodes A 5-nodes A 4)/γ
  have hz : z≠0 := inv_ne_zero hγ
  have hf : Front B z := normal_front_paid ho h30 ha he hγ
  have ht : treeSpace B 4=⊤ := by
    rw [scale_treeSpace z hz A];exact order_six_grade_four_top ho ha (fun i=>he i ▸ hγ)
  have hT := third_data hf
  obtain ⟨_,_,hc5,_,_⟩:=order_six_terminal_chronology ho ha he hγ
  have h5 : nodes B 5=z-1 := by
    change nodes (scaleTable z A) 5=z-1
    rw [nodes_scaleTable]
    change γ⁻¹*nodes A 5=γ⁻¹-1
    rw [hc5];field_simp
  have h4 : nodes B 4=z-1-v := by
    change nodes (scaleTable z A) 4=z-1-v
    rw [nodes_scaleTable]
    change γ⁻¹*nodes A 4=γ⁻¹-1-(nodes A 5-nodes A 4)/γ
    rw [hc5];field_simp;ring
  have hg : seed B 4=kap v*seed B 5 := by
    change seed (scaleTable z A) 4=kap v*seed (scaleTable z A) 5
    rw [seed_scaleTable]
    change z^2*seed A 4=kap v*(z^2*seed A 5)
    have hh:=order_six_weighted_terminal_seed ho ha he hγ
    change seed A 4=kap v*seed A 5 at hh
    rw [hh];ring
  by_cases hr : B 2 1=0
  · obtain ⟨hw,hwu⟩:=zero_tap_distinct hf ht hr
    have hc := zero_algebra_paid v hn2 hT hf.tap_ne hr hw hwu
    have hs:=first_clear hf _ (J2_clear hf hr)
    have hl:=Op.zero_word_paid ho h30 z u v
    rw [hs,map_zero,mul_zero] at hl
    exact False.elim <| RKCert.ReviewedNative.SDIRKSixReceipts.zero_chart_excluded_paid h30
      (z := z) (u := u) (v := v)
      (by change zeroCubic z u v = 0; exact hc)
      (by change zeroLaguerre z u v = 0; linear_combination hl)
  · obtain ⟨hw,hd,hfront⟩:=nonzero_algebra_paid v hn2 hT hf.tap_ne hr
    have hs:=H_clear hf hw hd
    have h₁:=Op.first_word_paid ho h30 z u v
    have h₂:=Op.second_word_paid ho h30 z u v
    rw [first_clear hf _ hs,map_zero,mul_zero] at h₁
    rw [second_clear hf h4 h5 _ hs,map_zero,mul_zero] at h₂
    have h₀ : nodes B 0 = 1 := by rw [node_mat_one, at0 hf.tri hf.single]; simp
    have hc₁ : nodes B 1 = 1 + u := by
      rw [node_mat_one, at1 hf.tri hf.single]
      simp [u, add_comm]
    have hc₂ : nodes B 2 = 1 + 2*u := by
      change w3 B = 2*u at hw
      rw [← hw, node_mat_one, at2 hf.tri hf.single]
      simp [w3]
      ring
    exact ⟨z, u, v, ⟨h30, hz, rfl, rfl, rfl, hf, hg, h₀, hc₁, hc₂, h4, h5, hfront, h₁.symm, h₂.symm,
      terminal_algebra hf h4 h5 hg⟩⟩

/-- The original away-four theorem, now using the separately exposed chart. -/
theorem order_six_six_stages_impossible_away_four {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K} {γ : K}
    (hD : (fourExceptionProduct : K) ≠ 0) (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i = γ) (hγ : γ ≠ 0) : False := by
  obtain ⟨z, u, v, h⟩ := order_six_six_stage_chart ho ha he hγ
  exact RKCert.ReviewedNative.SDIRKSixReceipts.nonzero_chart_excluded_away_four h.paid hD
    h.z_ne h.front_zero h.bridge1_zero h.bridge2_zero h.last_zero

/-- The strict order-six lower bound over a field in which the four-factor product survives. -/
theorem seven_le_of_strict_order_six_away_four {s:ℕ} {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {γ:K}
    (hD : (fourExceptionProduct : K) ≠ 0) (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0) : 7≤s := by
  have h₆:=nonsingular_stageFloor_field ho ha (fun i=>he i ▸ hγ) (by decide)
  change 6≤s at h₆
  by_contra h
  have hs:s=6 := by omega
  subst s
  exact order_six_six_stages_impossible_away_four hD ho ha he hγ

end RKResearch.Certified.Graded.SDIRKSix

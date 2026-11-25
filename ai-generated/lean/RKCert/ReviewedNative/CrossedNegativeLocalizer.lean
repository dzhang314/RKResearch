module

public import RKCert.ReviewedNative.CrossedNegativeRationalWitness
public import RKCert.ReviewedNative.CrossedGaussianSignedAdapter

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Uniform finite localizers for the negative-tail endpoint

No Gaussian nodes of a reference density are chosen. The two lower
directions and one upper direction are fixed rational polynomials. -/
namespace RKCert.ReviewedNative.CrossedNegativeLocalizer

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.CrossedNegativeReference
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1200000

def density (b₀ b₁ : K) : K[X] := w K+C b₀*(1-X)+C b₁*X

theorem density_degree (b₀ b₁ : K) : (density b₀ b₁).natDegree ≤ 2 := by
  have lin : (1-X:K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  unfold density
  have left : (C b₀ * (1-X : K[X])).natDegree ≤ 2 :=
    (natDegree_C_mul_le b₀ _).trans (lin.trans (show 1 ≤ 2 by decide))
  have right : (C b₁ * (X : K[X])).natDegree ≤ 2 :=
    (natDegree_C_mul_le b₁ _).trans (show (X : K[X]).natDegree ≤ 2 by simp)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le deg_w left) right

theorem density_eval_pos {b₀ b₁ x : K} (l : 0 ≤ b₀) (r : 0 ≤ b₁)
    (x₀ : 0 < x) (x₁ : x < 1) : 0 < (density b₀ b₁).eval x := by
  simp only [density,w,eval_add,eval_mul,eval_C,eval_one,eval_sub,eval_X]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos x₀ (sub_pos.mpr x₁)) (mul_nonneg l (sub_nonneg.mpr x₁.le)))
    (mul_nonneg r x₀.le)

theorem density_ne_zero {b₀ b₁ : K} (l : 0 ≤ b₀) (r : 0 ≤ b₁) :
    density b₀ b₁ ≠ 0 := by
  intro zero
  have e := density_eval_pos l r (x:=1/2) (by norm_num) (by norm_num)
  rw [zero,eval_zero] at e
  exact (lt_irrefl 0) e

private theorem split_density (b₀ b₁ : K) (F : K[X]) :
    unitMoment (density b₀ b₁) F =
      integral 0 1 ((w K*w K)*F)+
        b₀*integral 0 1 ((w K*(1-X))*F)+b₁*integral 0 1 ((w K*X)*F) := by
  rw [unitMoment_apply]
  change integral 0 1 ((w K*density b₀ b₁)*F)=_
  have e : (w K*density b₀ b₁)*F =
      (w K*w K)*F+C b₀*((w K*(1-X))*F)+C b₁*((w K*X)*F) := by
    unfold density
    ring
  rw [e]
  simp only [map_add,moment_C_mul]

private theorem split_left_density (b₀ b₁ : K) (F : K[X]) :
    unitMoment (density b₀ b₁) F =
      integral 0 1 ((w K*w K)*F)+
        b₁*integral 0 1 (w K*F)+(b₀-b₁)*integral 0 1 ((w K*(1-X))*F) := by
  rw [unitMoment_apply]
  change integral 0 1 ((w K*density b₀ b₁)*F)=_
  have e : (w K*density b₀ b₁)*F =
      (w K*w K)*F+C b₁*(w K*F)+C (b₀-b₁)*((w K*(1-X))*F) := by
    simp only [density,map_sub]
    ring
  rw [e]
  simp only [map_add,moment_C_mul]

theorem two_below_quarter {t : Finset K} {μ : K → K} {b₀ b₁ : K}
    (b₁n : 0 ≤ b₁) (tilt : b₁ ≤ b₀) (mass : ∀ x ∈ t, 0 ≤ μ x)
    (law : ExactRule (unitMoment (density b₀ b₁)) t id μ 11) :
    2 ≤ (t.filter (fun x => x < (1:K)/4)).card := by
  have d := deg_loCut (K:=K)
  have cnt := card_pos_ge_two_of_exact_rank_two (s:=t) (μ:=μ) (B:=w K*density b₀ b₁)
    (g:=loCut K) (P₀:=lo₀ K) (P₁:=lo₁ K) (d:=5) (integral 0 1) mass
    (fun P pd => by simpa only [unitMoment_apply,unitWeight,w,id_eq] using law P (by omega))
    deg_lo₀ deg_lo₁ (by
      intro a b nz
      change 0 < unitMoment (density b₀ b₁) (loCut K*(C a*lo₀ K+C b*lo₁ K)^2)
      rw [split_left_density]
      exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (lo_ww_pos nz) (mul_nonneg b₁n (lo_w_pos nz).le))
        (mul_nonneg (sub_nonneg.mpr tilt) (lo_left_pos nz).le))
  have test (x : K) : 0 < (loCut K).eval x ↔ x < (1:K)/4 := by
    simp only [loCut,eval_sub,eval_one,eval_mul,eval_ofNat,eval_X]
    constructor <;> intro h <;> linarith only [h]
  simpa only [test] using cnt

theorem exists_above_seven_eighths {t : Finset K} {μ : K → K} {b₀ b₁ : K}
    (b₀n : 0 ≤ b₀) (b₁n : 0 ≤ b₁) (mass : ∀ x ∈ t, 0 ≤ μ x)
    (law : ExactRule (unitMoment (density b₀ b₁)) t id μ 11) :
    ∃ x ∈ t, (7:K)/8 < x := by
  let F : K[X] := hiCut K*(hi K)^2
  have deg : F.natDegree ≤ 11 := natDegree_mul_le_of_le deg_hiCut (natDegree_pow_le_of_le 2 deg_hi)
  have h : 0 < unitMoment (density b₀ b₁) F := by
    rw [split_density]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hi_ww_pos (mul_nonneg b₀n hi_left_pos.le))
      (mul_nonneg b₁n hi_right_pos.le)
  rw [law F deg] at h
  by_contra none
  apply (not_lt_of_ge ?_) h
  apply Finset.sum_nonpos
  intro x hx
  have up : x ≤ (7:K)/8 := le_of_not_gt fun lt => none ⟨x,hx,lt⟩
  have s : (hiCut K).eval x ≤ 0 := by
    simp only [hiCut,eval_sub,eval_mul,eval_ofNat,eval_X]
    linarith only [up]
  simp only [F,id_eq,eval_mul,eval_pow]
  exact mul_nonpos_of_nonneg_of_nonpos (mass x hx) (mul_nonpos_of_nonpos_of_nonneg s (sq_nonneg _))

private theorem integral_nonneg_on_interval {l r : K} (lr : l < r) (P : K[X])
    (degree : P.natDegree ≤ 19) (nonneg : ∀ x, l < x → x < r → 0 ≤ P.eval x) :
    0 ≤ integral l r P := by
  rw [interval_exact _ _ _ degree]
  apply Finset.sum_nonneg
  intro i _
  have px := intervalPoint_mem lr i
  exact mul_nonneg (intervalWeight_pos lr i).le (nonneg _ px.1 px.2)

private theorem integral_adjacent (l m r : K) (P : K[X]) :
    integral l m P+integral m r P=integral l r P := by
  simp only [integral_apply]
  ring

/-- The actual first two primitive ports, once u>7/8, force the first
root to lie *above* 1/4. The comparison is polynomial: the excess
density is X((1-X)+k)(X-1/4) with k=4b₁/3≥0. -/
theorem left_pair_forces_quarter {r s u b₀ b₁ : K} {q : K[X]}
    (b₀n : 0 ≤ b₀) (b₁n : 0 ≤ b₁) (large : (7:K)/8 < u) (u₁ : u < 1)
    (fact : q=density b₀ b₁*((X-C r)*(X-C s)))
    (end₀ : integral 0 u (X*q)=0) (end₁ : integral 0 u (X^2*q)=0) :
    (1:K)/4 < r := by
  let t := (1:K)/4
  let D : K[X] := X-C t
  let P : K[X] := X-C s
  let B := density b₀ b₁
  let J := integral (0:K) u
  let k := (4:K)/3*b₁
  let lref := t+b₀+k*t
  let G : K[X] := X*(1-X+C k)
  have kn : 0 ≤ k := mul_nonneg (by norm_num) b₁n
  have tn : 0 < t := by dsimp only [t]; norm_num
  have lref_pos : 0 < lref := add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg tn b₀n) (mul_nonneg kn tn.le)
  have u₀ : 0 < u := (by norm_num : (0:K) < 7/8).trans large
  have dD : D.natDegree ≤ 1 := by simp [D]
  have dP : P.natDegree ≤ 1 := by simp [P]
  have sqD : (D^2).natDegree ≤ 2 := natDegree_pow_le_of_le 2 dD
  have sqP : (P^2).natDegree ≤ 2 := natDegree_pow_le_of_le 2 dP
  have dB : B.natDegree ≤ 2 := density_degree _ _
  have dG : G.natDegree ≤ 2 := by
    unfold G
    have hX : (X : K[X]).natDegree ≤ 1 := by simp
    have hL : (1-X : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    have hC : (C k).natDegree ≤ 1 := by simp
    exact natDegree_mul_le_of_le hX (natDegree_add_le_of_degree_le hL hC)
  have refDegree : (w K*(D*P^2)).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le deg_w (natDegree_mul_le_of_le dD sqP)).trans (by decide)
  have refExtra : 0 ≤ integral ((7:K)/8) u (w K*(D*P^2)) := by
    apply integral_nonneg_on_interval large _ refDegree
    intro x lo hi
    have xp : 0 < x := (by norm_num : (0:K) < 7/8).trans lo
    have dt : 0 ≤ x-t := sub_nonneg.mpr ((by norm_num [t] : t < 7/8).trans lo).le
    simp only [w,D,P,eval_mul,eval_sub,eval_one,eval_X,eval_C,eval_pow]
    exact mul_nonneg (mul_nonneg xp.le (sub_nonneg.mpr (hi.trans u₁).le))
      (mul_nonneg dt (sq_nonneg _))
  have refPos : 0 < J (w K*(D*P^2)) := by
    change 0 < integral 0 u (w K*(D*P^2))
    rw [← integral_adjacent 0 (7/8) u]
    exact add_pos_of_pos_of_nonneg (cutoff_affine_pos s) refExtra
  have compDegree : (G*(D^2*P^2)).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le dG (natDegree_mul_le_of_le sqD sqP)).trans (by decide)
  have compNonneg : 0 ≤ J (G*(D^2*P^2)) := by
    apply integral_nonneg_on_interval u₀ _ compDegree
    intro x xl xr
    simp only [G,D,P,eval_mul,eval_add,eval_sub,eval_X,eval_one,eval_C,eval_pow]
    exact mul_nonneg (mul_nonneg xl.le (add_nonneg (sub_nonneg.mpr (xr.trans u₁).le) kn))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have kb : C b₁ = C k-C k*C t := by
    rw [← map_mul,← map_sub]
    congr 1
    dsimp only [k,t]
    ring
  have comp : (X*B)*(D*P^2) = C lref*(w K*(D*P^2))+G*(D^2*P^2) := by
    simp only [B,density,lref,G,D,w,map_add,map_mul,kb]
    ring
  have pos : 0 < J ((X*B)*(D*P^2)) := by
    rw [comp,map_add,moment_C_mul]
    exact add_pos_of_pos_of_nonneg (mul_pos lref_pos refPos) compNonneg
  have baseDegree : ((X*B)*P^2).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le (by simp : (X:K[X]).natDegree ≤ 1) dB) sqP).trans (by decide)
  have base : 0 ≤ J ((X*B)*P^2) := by
    apply integral_nonneg_on_interval u₀ _ baseDegree
    intro x xl xr
    simp only [P,eval_mul,eval_X,eval_C,eval_sub,eval_pow]
    exact mul_nonneg (mul_nonneg xl.le (density_eval_pos b₀n b₁n xl (xr.trans u₁)).le) (sq_nonneg _)
  have pay : J ((X*q)*P)=0 := by
    have pEq : (X*q)*P=X^2*q-C s*(X*q) := by unfold P; ring
    rw [pEq,map_sub,moment_C_mul]
    change integral 0 u (X^2*q)-s*integral 0 u (X*q)=0
    rw [end₀,end₁,mul_zero,sub_zero]
  have subEq : (X*B)*(D*P^2) = C (r-t)*((X*B)*P^2)+(X*q)*P := by
    rw [fact]
    simp only [B,P,D,map_sub]
    ring
  rw [subEq,map_add,moment_C_mul,pay,add_zero] at pos
  exact sub_pos.mp (pos_of_mul_pos_left pos base)

end
end RKCert.ReviewedNative.CrossedNegativeLocalizer

module

public import RKCert.ReviewedNative.SDIRK118ForwardLiftMoments

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardCubics

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.Graded (mat)
open RKResearch.Certified.PaidDefectBridge (forestNat treeSize treeGrade)
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation (t1 t2 t3a t3b)
open RKResearch.Certified.PaidDefectBridge.ForwardChart
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ConditionalFin11
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardLiftMoments
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (Geometry ideal)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature
open Polynomial
open scoped Matrix Polynomial BigOperators FiniteRootedTree

local notation "ℙ" => Polynomial ℝ

private theorem bd_sub {n : ℕ} {P Q : ℙ} (hP : PolyBound n P) (hQ : PolyBound n Q) :
    PolyBound n (P-Q) := by
  intro j hj
  rw [coeff_sub,hP j hj,hQ j hj,sub_self]

private theorem bd_smul {n : ℕ} {P : ℙ} (hP : PolyBound n P) (a : ℝ) : PolyBound n (a • P) := by
  intro j hj
  rw [Polynomial.coeff_smul,hP j hj,smul_zero]

private theorem bd_expand {n m : ℕ} {P : ℙ} (h : n ≤ m) (hp : PolyBound n P) :
    PolyBound m P := fun j hj => hp j (h.trans_lt hj)

private theorem degree_quad (c d v : V ℝ) : PolyBound 2 (polyProject c d v) := by
  intro j hj
  have j0 : j ≠ 0 := by omega
  have j1 : j ≠ 1 := by omega
  have j2 : j ≠ 2 := by omega
  change (toPoly (project c d v)).coeff j = 0
  simp [toPoly_apply,Polynomial.coeff_smul,coeff_one,coeff_X,coeff_X_pow,j0,j0.symm,j1,j1.symm,j2,j2.symm]

private theorem bd_mul {n m : ℕ} {P Q : ℙ} (hP : PolyBound n P) (hQ : PolyBound m Q) :
    PolyBound (n+m) (P*Q) :=
  natDegree_le_iff_coeff_eq_zero.mp
    (natDegree_mul_le.trans (Nat.add_le_add (natDegree_le_iff_coeff_eq_zero.mpr hP)
      (natDegree_le_iff_coeff_eq_zero.mpr hQ)))

private theorem bd_factor (x : ℝ) : PolyBound 1 (linearFactor x) :=
  natDegree_le_iff_coeff_eq_zero.mp (natDegree_X_sub_C x).le

private theorem cubic_bd (x1 x4 x5 : ℝ) : PolyBound 3 (cubic x1 x4 x5) :=
  bd_mul (bd_mul (bd_factor x1) (bd_factor x4)) (bd_factor x5)

/-- Subtract the cubic leading term and dispatch the residual at three
distinct nodes. The last covector kills the multiple of the monic cubic. -/
private theorem zero_by_cubic_nodes (rho : ℙ →ₗ[ℝ] ℝ) (x1 x4 x5 : ℝ)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hp : rho (cubic x1 x4 x5) ≠ 0)
    (P : ℙ) (hP : PolyBound 3 P) (hC : rho P = 0)
    (e1 : P.eval x1 = 0) (e4 : P.eval x4 = 0) (e5 : P.eval x5 = 0) : P = 0 := by
  let R := cubic x1 x4 x5
  let α := P.coeff 3
  let Q := P - α • R
  have hR : R.Monic := ((monic_X_sub_C x1).mul (monic_X_sub_C x4)).mul (monic_X_sub_C x5)
  have dR : R.natDegree = 3 := by
    change (linearFactor x1 * linearFactor x4 * linearFactor x5).natDegree = 3
    unfold linearFactor
    rw [((monic_X_sub_C x1).mul (monic_X_sub_C x4)).natDegree_mul (monic_X_sub_C x5),
      (monic_X_sub_C x1).natDegree_mul (monic_X_sub_C x4),natDegree_X_sub_C,
      natDegree_X_sub_C,natDegree_X_sub_C]
  have kR : R.coeff 3 = 1 := by simpa only [dR] using hR.coeff_natDegree
  have dQ : PolyBound 2 Q := by
    intro i hi
    by_cases he : i = 3
    · subst i
      simp only [Q,α,coeff_sub,Polynomial.coeff_smul,kR,smul_eq_mul,mul_one,sub_self]
    · have hig : 3 < i := by omega
      have hr : R.coeff i = 0 := cubic_bd x1 x4 x5 i hig
      simp only [Q,coeff_sub,Polynomial.coeff_smul,hP i hig,hr,smul_zero,sub_zero]
  let w : Fin 3 → ℝ := ![x1,x4,x5]
  have inj : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [w,h14,h15,h45,h14.symm,h15.symm,h45.symm] at hij ⊢
  have ev (i : Fin 3) : Q.eval (w i) = 0 := by
    fin_cases i <;> simp [Q,R,cubic,linearFactor,w,eval_sub,eval_mul,e1,e4,e5]
  have dq : Q.degree < ((Finset.univ : Finset (Fin 3)).card : WithBot ℕ) := by
    have h : Q.degree ≤ ((2 : ℕ) : WithBot ℕ) :=
      degree_le_of_natDegree_le (natDegree_le_iff_coeff_eq_zero.mpr dQ)
    exact h.trans_lt (by norm_num)
  have hz : Q = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ inj.injOn dq
      (fun i _ => ev i)
  have pe : P = α • R := sub_eq_zero.mp hz
  rw [pe,map_smul,smul_eq_mul] at hC
  rw [pe,(mul_eq_zero.mp hC).resolve_right hp,zero_smul]

private def corrected (rho : ℙ →ₗ[ℝ] ℝ) (R H : ℙ) : ℙ :=
  H - (rho H / rho R) • R

private theorem corrected_rho (rho : ℙ →ₗ[ℝ] ℝ) (R H : ℙ) (hr : rho R ≠ 0) :
    rho (corrected rho R H) = 0 := by
  rw [corrected,map_sub,map_smul,smul_eq_mul,div_mul_cancel₀ _ hr,sub_self]

/-- Exact identity on the two cubics emitted by the chart. The only
functional pivot below is the same literal residual pivot as calibration. -/
private theorem fit_corrected (rho : ℙ →ₗ[ℝ] ℝ) (x1 x4 x5 : ℝ)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hp : rho (cubic x1 x4 x5) ≠ 0)
    (P : ℙ) (hP : PolyBound 3 P) (hc : rho P = 0) (h1 : P.eval x1 = 0) :
    let R := cubic x1 x4 x5
    let p4 := linearFactor x1 * linearFactor x5
    let p5 := linearFactor x1 * linearFactor x4
    let H4 := corrected rho R ((p4.eval x4)⁻¹ • p4)
    let H5 := corrected rho R ((p5.eval x5)⁻¹ • p5)
    P = P.eval x4 • H4 + P.eval x5 • H5 := by
  let R := cubic x1 x4 x5
  let p4 := linearFactor x1 * linearFactor x5
  let p5 := linearFactor x1 * linearFactor x4
  let H4 := corrected rho R ((p4.eval x4)⁻¹ • p4)
  let H5 := corrected rho R ((p5.eval x5)⁻¹ • p5)
  have d4 : p4.eval x4 ≠ 0 := by
    simp only [p4,linearFactor,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr h14.symm) (sub_ne_zero.mpr h45)
  have d5 : p5.eval x5 ≠ 0 := by
    simp only [p5,linearFactor,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr h15.symm) (sub_ne_zero.mpr h45.symm)
  have R1 : R.eval x1=0 := by simp [R,cubic,linearFactor,eval_mul,eval_sub]
  have R4 : R.eval x4=0 := by simp [R,cubic,linearFactor,eval_mul,eval_sub]
  have R5 : R.eval x5=0 := by simp [R,cubic,linearFactor,eval_mul,eval_sub]
  have z4 : ∀ x, R.eval x=0 → H4.eval x=(p4.eval x4)⁻¹*p4.eval x := by
    intro x hx
    simp only [H4,corrected,eval_sub,Polynomial.eval_smul,smul_eq_mul,hx,mul_zero,sub_zero]
  have z5 : ∀ x, R.eval x=0 → H5.eval x=(p5.eval x5)⁻¹*p5.eval x := by
    intro x hx
    simp only [H5,corrected,eval_sub,Polynomial.eval_smul,smul_eq_mul,hx,mul_zero,sub_zero]
  have e41 : H4.eval x1=0 := by rw [z4 x1 R1]; simp [p4,linearFactor,eval_mul,eval_sub]
  have e51 : H5.eval x1=0 := by rw [z5 x1 R1]; simp [p5,linearFactor,eval_mul,eval_sub]
  have e44 : H4.eval x4=1 := by rw [z4 x4 R4,inv_mul_cancel₀ d4]
  have e55 : H5.eval x5=1 := by rw [z5 x5 R5,inv_mul_cancel₀ d5]
  have e45 : H4.eval x5=0 := by rw [z4 x5 R5]; simp [p4,linearFactor,eval_mul,eval_sub]
  have e54 : H5.eval x4=0 := by rw [z5 x4 R4]; simp [p5,linearFactor,eval_mul,eval_sub]
  have a4 : rho H4=0 := corrected_rho rho R _ hp
  have a5 : rho H5=0 := corrected_rho rho R _ hp
  have g4 : PolyBound 3 H4 :=
    bd_sub (bd_smul (bd_expand (by decide : 2≤3) (bd_mul (bd_factor x1) (bd_factor x5))) _)
      (bd_smul (cubic_bd x1 x4 x5) _)
  have g5 : PolyBound 3 H5 :=
    bd_sub (bd_smul (bd_expand (by decide : 2≤3) (bd_mul (bd_factor x1) (bd_factor x4))) _)
      (bd_smul (cubic_bd x1 x4 x5) _)
  let D := P - P.eval x4 • H4 - P.eval x5 • H5
  have dD : PolyBound 3 D := bd_sub (bd_sub hP (bd_smul g4 _)) (bd_smul g5 _)
  have hd : rho D = 0 := by simp [D,map_sub,map_smul,hc,a4,a5]
  have z1 : D.eval x1 = 0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,h1,e41,e51,mul_zero,sub_zero]
  have z4' : D.eval x4 = 0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,e44,e54,mul_zero,mul_one,sub_self,sub_zero]
  have z5' : D.eval x5 = 0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,e45,e55,mul_zero,mul_one,sub_self,sub_zero]
  have e := zero_by_cubic_nodes rho x1 x4 x5 h14 h15 h45 hp D dD hd z1 z4' z5'
  change P = P.eval x4 • H4 + P.eval x5 • H5
  have eq : P - P.eval x4 • H4 = P.eval x5 • H5 := sub_eq_zero.mp e
  calc
    P = (P - P.eval x4 • H4) + P.eval x4 • H4 := (sub_add_cancel _ _).symm
    _ = _ := by rw [eq,add_comm]

/-- Cubic condition in the actual raw reviewed stage vector: its two
defects are precisely g and c·g, not an assumed cubic polynomial gate. -/
private def rawCubic (G : Matrix (Fin 4) (Fin 4) ℝ) (c g : V ℝ) (t : FiniteRootedTree) : Prop :=
  ∃ (q α β : ℝ), ideal t = q • ((X : ℙ)^3) ∧
    Φ t G = q • c^3 + α • g + β • (c*g)

private theorem raw_five (G : Matrix (Fin 4) (Fin 4) ℝ) (c g : V ℝ) (γ η : ℝ)
    (h : Actions G c g γ η) :
    rawCubic G c g (t3a ◂ t1) ∧ rawCubic G c g (t3b ◂ t1) ∧
      rawCubic G c g (t2 ◂ t2) ∧ rawCubic G c g (t1 ◂ t3a) ∧ rawCubic G c g (t1 ◂ t3b) := by
  obtain ⟨a0,a1,a2,a3⟩ := reviewed_four_columns G c g h.sum h.clock
  let A := γ * (1 - η⁻¹)
  let B := η⁻¹
  have gAct : mat G g = A • g + B • (c*g) := h.defect
  have a00 : Φ t1 G = (1 : V ℝ) := a0
  have a11 : Φ t2 G = c := a1
  have a22 : Φ t3a G = c^2 := a2
  have a33 : Φ t3b G = (2 : ℝ)⁻¹ • c^2 + g := a3
  refine ⟨⟨1,0,0,?_,?_⟩,⟨(2:ℝ)⁻¹,0,1,?_,?_⟩,⟨(2:ℝ)⁻¹,0,1,?_,?_⟩,
    ⟨(3:ℝ)⁻¹,(2/3)*A,(2/3)*(B+1),?_,?_⟩,
    ⟨(6:ℝ)⁻¹,(4/3)*A,(4/3)*B+1/3,?_,?_⟩⟩
  · norm_num [ideal,t3a,t2,t1,forestNat,treeGrade,treeSize,FiniteRootedTree.order,
      FiniteRootedTree.forestFactorial,PNat.add_coe,PNat.mul_coe]
  · change Φ t3a G * mat G (Φ t1 G) = _
    rw [a00,a22,h.sum]
    funext i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  · norm_num [ideal,t3b,t2,t1,forestNat,treeGrade,treeSize,FiniteRootedTree.order,
      FiniteRootedTree.forestFactorial,PNat.add_coe,PNat.mul_coe]
  · change Φ t3b G * mat G (Φ t1 G) = _
    rw [a00,a33,h.sum]
    funext i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  · norm_num [ideal,t2,t1,forestNat,treeGrade,treeSize,FiniteRootedTree.order,
      FiniteRootedTree.forestFactorial,PNat.add_coe,PNat.mul_coe]
  · change Φ t2 G * mat G (Φ t2 G) = _
    rw [a11,h.clock]
    funext i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  · norm_num [ideal,t3a,t2,t1,forestNat,treeGrade,treeSize,FiniteRootedTree.order,
      FiniteRootedTree.forestFactorial,PNat.add_coe,PNat.mul_coe]
  · change Φ t1 G * mat G (Φ t3a G) = _
    rw [a00,a22,one_mul,h.square,gAct]
    funext i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  · norm_num [ideal,t3b,t2,t1,forestNat,treeGrade,treeSize,FiniteRootedTree.order,
      FiniteRootedTree.forestFactorial,PNat.add_coe,PNat.mul_coe]
  · change Φ t1 G * mat G (Φ t3b G) = _
    rw [a00,a33,one_mul,map_add,map_smul,h.square,gAct]
    funext i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
    ring

/-- Exactly the tilted covector used inside ScalarBindings.geometry.
The residual pivot is on its actual, emitted cubic, not a rank proposition. -/
def literalRho (M : MonomialBasis) (s t c : ℝ) : ℙ →ₗ[ℝ] ℝ :=
  let d := dAt M s t c
  let a := aAt s
  let γ := (zAt s)⁻¹
  let gd := gdAt s (etaAt s) d
  (tiltA a d (1/2) gd) • evalAt M γ + (tiltB a d (g1At s) gd) • evalAt M (γ*a) +
    evalAt M (γ*d)

def ResidualPivot (M : MonomialBasis) (s t c : ℝ) : Prop :=
  let x := xAt M s t c
  literalRho M s t c (cubic (x 1) (x 4) (x 5)) ≠ 0

theorem literal_x1_clock (M : MonomialBasis) (s t c : ℝ) (seed : ExactScalarSeed M s t c) :
    xAt M s t c 1 = forwardClock M s t c 2 := by
  let γ := (zAt s)⁻¹
  change 1 - aAt s / zAt s = γ*s
  have e : γ*(aAt s+s)=1 := inv_mul_cancel₀ (literal_z_pos M s t c seed).ne'
  rw [div_eq_mul_inv]
  change 1 - aAt s*γ = γ*s
  linear_combination -e

private theorem raw_implies_literal
    (M : MonomialBasis) (hm : standardPowers M) (s t c : ℝ) (seed : ExactScalarSeed M s t c)
    (frame : pivot (forwardClock M s t c) (forwardG M s t c) ≠ 0)
    (residual : ResidualPivot M s t c) (t0 : FiniteRootedTree)
    (raw : rawCubic (geometry M s t c).G (forwardClock M s t c) (forwardG M s t c) t0) :
    ForwardCubic (geometry M s t c) t0 := by
  let g := geometry M s t c
  let cc := forwardClock M s t c
  let gg := forwardG M s t c
  let a := aAt s
  let γ := (zAt s)⁻¹
  let d := dAt M s t c
  let g1 := g1At s
  let gd := gdAt s (etaAt s) d
  let A := tiltA a d (1/2) gd
  let B := tiltB a d g1 gd
  let rho := literalRho M s t c
  let x := xAt M s t c
  let R := cubic (x 1) (x 4) (x 5)
  let v := Φ t0 g.G
  let H := ideal (K := ℝ) t0
  let P := polyProject cc gg v
  let E : Fin 4 → ℙ →ₗ[ℝ] ℝ := fun i => Polynomial.leval (cc i)
  have h0 : cc 0 = γ := by change γ*1=γ; ring
  have h1 : cc 1 = γ*a := rfl
  have h3 : cc 3 = γ*d := rfl
  have hseedLo := seed.sLower
  have hseedHi := seed.sUpper
  have eta := eta_pos s (by linarith) (by linarith) seed.sRoot
  have hg1 : g1 ≠ 0 := by
    change 0 < 2*g1 at eta
    linarith
  have ha : a-1 ≠ 0 := by dsimp [a,aAt]; linarith
  have tilts := literal_tilt_annihilates γ a d (1/2) g1 gd ha (by norm_num) hg1
  have tG : A*gg 0+B*gg 1+gg 3=0 := tilts.1
  have tCG : A*cc 0*gg 0+B*cc 1*gg 1+cc 3*gg 3=0 := by
    calc
      _ = A*(γ^3*(1/2))+B*(γ^3*a*g1)+γ^3*d*gd := by
        change A*(γ*1)*(γ^2*(1/2))+B*(γ*a)*(γ^2*g1)+(γ*d)*(γ^2*gd)=_
        ring
      _ = 0 := tilts.2
  obtain ⟨h01,h02,h12⟩ := literal_old_distinct M s t c seed
  have g2 : gg 2 = 0 := (literal_actions M s t c seed).anchor.defectZero
  have eQ (i : Fin 4) : E i P = ev (cc i) (project cc gg v) := by
    apply evaluate_toPoly
    · exact eval_one
    · exact eval_X
    · simp [E,Polynomial.leval_apply,Polynomial.eval_pow,eval_X]
  have eAnchor : E 2 P = v 2 := by
    rw [eQ]
    exact clean_anchor_all_vectors cc gg v h01 h02 h12 frame g2
  have eTilt : A*E 0 P+B*E 1 P+E 3 P=A*v 0+B*v 1+v 3 := by
    simp only [eQ]
    exact clean_tilt_all_vectors cc gg v A B h01 h02 h12 frame tG
  obtain ⟨q,α,β,eqH,eqv⟩ := raw
  have eh : H = q • (X^3 : ℙ) := eqH
  have u (i : Fin 4) : v i = E i H + α*gg i + β*cc i*gg i := by
    have ee := congrArg (fun w : V ℝ => w i) eqv
    change v i = (q • cc^3+α • gg+β • (cc*gg)) i at ee
    rw [eh]
    simpa only [E,Polynomial.leval_apply,Polynomial.eval_smul,Polynomial.eval_pow,eval_X,
      Pi.smul_apply,Pi.pow_apply,Pi.add_apply,Pi.mul_apply,smul_eq_mul,mul_assoc] using ee
  obtain ⟨eClean1,eCleanTilt⟩ :=
    projected_defect_clean cc gg v A B α β E H P eAnchor eTilt g2 tG tCG u
  have rhoE (Q : ℙ) : rho Q = A*E 0 Q+B*E 1 Q+E 3 Q := by
    change ((A • evalAt M γ+B • evalAt M (γ*a)+evalAt M (γ*d)) Q) = _
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
      evalAt_eq_eval M hm,E,Polynomial.leval_apply,h0,h1,h3]
  have hF : g.F t0 = H-P := rfl
  have hR : rho (g.F t0) = 0 := by rw [hF,rhoE]; exact eCleanTilt
  have hX : (g.F t0).eval (x 1) = 0 := by
    rw [hF]
    change (H-P).eval (xAt M s t c 1) = 0
    rw [literal_x1_clock M s t c seed]
    exact eClean1
  have dH : PolyBound 3 H := by
    rw [eh]
    exact bd_smul (natDegree_le_iff_coeff_eq_zero.mp (natDegree_X_pow_le (R := ℝ) 3)) q
  have dF : PolyBound 3 (g.F t0) := by
    rw [hF]
    exact bd_sub dH (bd_expand (by decide : 2≤3) (degree_quad cc gg v))
  have hx : Function.Injective x := by
    intro i j e
    apply literal_nodes_injective M s t c seed
    change 1-yAt M s t c i=1-yAt M s t c j at e
    linarith only [e]
  have h14 : x 1 ≠ x 4 := hx.ne (by decide)
  have h15 : x 1 ≠ x 5 := hx.ne (by decide)
  have h45 : x 4 ≠ x 5 := hx.ne (by decide)
  have fit := fit_corrected rho (x 1) (x 4) (x 5) h14 h15 h45 residual (g.F t0) dF hR hX
  let p4 := linearFactor (x 1)*linearFactor (x 5)
  let p5 := linearFactor (x 1)*linearFactor (x 4)
  have I4 : g.HF 0 = corrected rho R ((p4.eval (x 4))⁻¹ • p4) := by
    change corrected rho R ((evalAt M (x 4) p4)⁻¹ • p4) = _
    rw [evalAt_eq_eval M hm]
  have I5 : g.HF 1 = corrected rho R ((p5.eval (x 5))⁻¹ • p5) := by
    change corrected rho R ((evalAt M (x 5) p5)⁻¹ • p5) = _
    rw [evalAt_eq_eval M hm]
  have ex (Q : ℙ) (i : Fin 6) : g.Ex Q i = Q.eval (x i) := evalAt_eq_eval M hm (x i) Q
  change g.F t0 = g.Ex (g.F t0) 4 • g.HF 0 + g.Ex (g.F t0) 5 • g.HF 1
  simpa only [I4,I5,ex] using fit

/-- All five actual order-four shape gates, proved from the literal emitted
moments. The remaining unbound scalar inequality is the same literal
residual pivot visible in calibration; the forward frame pivot is proved. -/
theorem literal_all_five_cubics (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (seed : ExactScalarSeed M s t c)
    (residual : ResidualPivot M s t c) :
    let g := geometry M s t c
    ForwardCubic g (t3a ◂ t1) ∧ ForwardCubic g (t3b ◂ t1) ∧ ForwardCubic g (t2 ◂ t2) ∧
    ForwardCubic g (t1 ◂ t3a) ∧ ForwardCubic g (t1 ◂ t3b) := by
  let g := geometry M s t c
  have frame := literal_frame_pivot M s t c seed
  obtain ⟨eA,eB,eC,eD,eE⟩ := raw_five g.G (forwardClock M s t c) (forwardG M s t c)
    g.γ (etaAt s) (literal_actions M s t c seed)
  exact ⟨raw_implies_literal M hm s t c seed frame residual _ eA,
    raw_implies_literal M hm s t c seed frame residual _ eB,
    raw_implies_literal M hm s t c seed frame residual _ eC,
    raw_implies_literal M hm s t c seed frame residual _ eD,
    raw_implies_literal M hm s t c seed frame residual _ eE⟩

/-- Direct fill of the preceding forward seam. Literal row shape and the
normalized row-2 anchor are proved separately in ForwardLiftMoments. -/
theorem literal_forward_leaves_of_guards (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (seed : ExactScalarSeed M s t c)
    (residual : ResidualPivot M s t c) :
    ForwardLeaves (geometry M s t c) (forwardClock M s t c) (forwardG M s t c) := by
  let g := geometry M s t c
  have acts := literal_actions M s t c seed
  obtain ⟨gl,gd⟩ := literal_forward_shape M s t c
  obtain ⟨h01,h02,h12⟩ := literal_old_distinct M s t c seed
  have frame := literal_frame_pivot M s t c seed
  obtain ⟨a,b,d,e,f⟩ := literal_all_five_cubics M hm s t c seed residual
  have hc : g.Ex X 1 = forwardClock M s t c 2 := by
    change evalAt M (xAt M s t c 1) X = _
    rw [evalAt_eq_eval M hm,eval_X,literal_x1_clock M s t c seed]
  exact ⟨h01,h02,h12,frame,gl,gd,acts.sum,acts.clock,acts.anchor,hc,a,b,d,e,f⟩

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardCubics

module

public import RKCert.ReviewedNative.SDIRK118ForwardLiftMoments

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralReverseProducer

open RKResearch
open RKResearch.Certified.Graded (mat)
open RKResearch.Certified.PaidDefectBridge.ForwardChart (V ev pivot interp)
open RKResearch.Certified.PaidDefectBridge.ReverseChart
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ConditionalFin11
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardLiftMoments
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (Geometry matrixOf matrixOf_mulVec delta site oldIx)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarAffineResponse (Ld_pos)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarMasses (oldSite raw_at_old)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature
open Polynomial
open scoped Matrix Polynomial BigOperators

local notation "ℙ" => Polynomial ℝ

/-- The two emitted donors have the same first three normalized rows.
Their actions there use only the first three coordinates, independently
of both appended rows. -/
theorem common_rows_action (h v : ℝ) (F R : V ℝ →ₗ[ℝ] ℝ)
    (x y : V ℝ) (same : ∀ j : Fin 4, j ≠ 3 → x j = y j)
    (i : Fin 4) (hi : i ≠ 3) :
    (mat (matrixOf (normalizedRows h v R)) x) i =
      (mat (matrixOf (normalizedRows h v F)) y) i := by
  change (matrixOf (normalizedRows h v R) *ᵥ x) i =
    (matrixOf (normalizedRows h v F) *ᵥ y) i
  rw [matrixOf_mulVec,matrixOf_mulVec]
  fin_cases i
  · change x 0 = y 0
    exact same 0 (by decide)
  · change h*x 0+x 1=h*y 0+y 1
    rw [same 0 (by decide),same 1 (by decide)]
  · change (2*h-v)*x 0+v*x 1+x 2=(2*h-v)*y 0+v*y 1+y 2
    rw [same 0 (by decide),same 1 (by decide),same 2 (by decide)]
  · exact (hi rfl).elim

theorem normalized_reverse_shape (s t : ℝ) :
    (reverseNormalized s t).IsLowerTriangular ∧ ∀ i, reverseNormalized s t i i = 1 := by
  let last := lastNormRow (uAt s t) t
  have self : last (delta (3 : Fin 4)) = 1 := by
    change lastNormRow (uAt s t) t (delta (3 : Fin 4)) = 1
    rw [lastNormRow_literal]
    simp [delta]
  exact normalized_rows_shape (hAt s) (2/(hAt s-2)) last self

theorem literal_reverse_shape (M : MonomialBasis) (s t c : ℝ) :
    let g := geometry M s t c
    g.R.IsLowerTriangular ∧ ∀ i, g.R i i = g.γ := by
  let g := geometry M s t c
  let γ := (zAt s)⁻¹
  obtain ⟨lower,diag⟩ := normalized_reverse_shape s t
  change g.R.IsLowerTriangular ∧ ∀ i, g.R i i = g.γ
  constructor
  · intro i j hij
    change γ * reverseNormalized s t i j = 0
    rw [lower hij,mul_zero]
  · intro i
    change γ * reverseNormalized s t i i = γ
    rw [diag,mul_one]

private theorem normalized_old_distinct (s t : ℝ) (hs : 0 < s) (hS : s < 1) :
    let u := uAt s t
    u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 := by
  change (1 : ℝ) ≠ (1+s)/2 ∧ (1 : ℝ) ≠ s ∧ (1+s)/2 ≠ s
  exact ⟨by linarith,by linarith,by linarith⟩

private theorem reverse_seed_interpolant (s t : ℝ) (hs : 0 < s) (hS : s < 1)
    (hroot : s^3-9*s^2+18*s-6=0) :
    interp (uAt s t) (gAt s 0) = seedQuad s (3/(2*Bs s)) := by
  obtain ⟨d01,d02,d12⟩ := normalized_old_distinct s t hs hS
  obtain ⟨e0,e1,e2⟩ := seedQuad_old_values (K := ℝ) s (by linarith) (by linarith) hroot
  exact interp_eq_seedQuad _ _ s _ d01 d02 d12 e0 e1 e2

structure ReverseActions (R : Matrix (Fin 4) (Fin 4) ℝ) (c g : V ℝ) : Prop where
  sum : mat R (1 : V ℝ) = c
  moment : mat R c = (2 : ℝ)⁻¹ • c ^ 2 + g
  anchor2 : LocalThree R c g 2
  anchor3 : LocalThree R c g 3

/-- First three rows transfer from the common normalized donor. The fourth
row is paid by the literal shifted cardinal row at the exact quadratic root. -/
theorem normalized_reverse_actions (M : MonomialBasis) (s t c : ℝ) (seed : ExactScalarSeed M s t c) :
    ReverseActions (reverseNormalized s t) (uAt s t) (gAt s 0) := by
  let d := dAt M s t c
  let η := etaAt s
  let gd := gdAt s η d
  let h := hAt s
  let v := 2/(h-2)
  let u := uAt s t
  let uF := uAt s d
  let g := gAt s 0
  let gF := gAt s gd
  let R := reverseNormalized s t
  let G := forwardNormalized s d
  let κ := 3/(2*Bs s)
  let rowR := lastNormRow u t
  let rowF := forwardLast uF (d-1) (Ud d gd) (Vd d η gd)
  have lo := seed.sLower
  have hi := seed.sUpper
  have hs : 0 < s := by linarith
  have hS : s < 1 := by linarith
  obtain ⟨hd,_,_⟩ := calibrated_real_bracket M s t c seed.affineLowerNeg seed.affineUpperPos
  have f := normalized_actions s d hs hS seed.sRoot (Ld_pos s d lo hi seed.sRoot hd).ne'
  change Actions G uF gF 1 η at f
  obtain ⟨d01,d02,d12⟩ := normalized_old_distinct s t hs hS
  have it : interp u g = seedQuad s κ := reverse_seed_interpolant s t hs hS seed.sRoot
  have root : t^2-(s+3)*t+s=0 := seed.tRoot
  obtain ⟨r0,r1,r2,rD⟩ := last_norm_anchor_on_four u g s κ t d01 d02 d12 rfl it rfl root
  have rLast (z : V ℝ) : (mat R z) 3 = rowR z := by
    change (matrixOf (normalizedRows h v rowR) *ᵥ z) 3 = rowR z
    rw [matrixOf_mulVec] <;> rfl
  have oldU (j : Fin 4) (hj : j ≠ 3) : u j = uF j := by
    fin_cases j <;> first | rfl | exact (hj rfl).elim
  have oldG (j : Fin 4) (hj : j ≠ 3) : g j = gF j := by
    fin_cases j <;> first | rfl | exact (hj rfl).elim
  have oldSq (j : Fin 4) (hj : j ≠ 3) : (u^2) j = (uF^2) j := by
    simp only [Pi.pow_apply,oldU j hj]
  have common (x y : V ℝ) (e : ∀ j : Fin 4, j ≠ 3 → x j = y j)
      (i : Fin 4) (hi : i ≠ 3) : (mat R x) i = (mat G y) i :=
    common_rows_action h v rowF rowR x y e i hi
  have rowSum : mat R (1 : V ℝ) = u := by
    funext i
    by_cases hi : i=3
    · subst i
      rw [rLast]
      exact r0
    · rw [common 1 1 (fun _ _ => rfl) i hi,f.sum]
      exact (oldU i hi).symm
  have rowMoment : mat R u = (2 : ℝ)⁻¹ • u^2 + g := by
    funext i
    by_cases hi : i=3
    · subst i
      rw [rLast]
      change lastNormRow u t u=(2 : ℝ)⁻¹*t^2+0
      rw [r1,add_zero,div_eq_mul_inv,mul_comm]
    · rw [common u uF oldU i hi,f.clock]
      simp only [Pi.add_apply,Pi.smul_apply,Pi.pow_apply,oldU i hi,oldG i hi]
  have a2 : LocalThree R u g 2 := by
    have h2 : (2 : Fin 4) ≠ 3 := by decide
    refine ⟨rfl,?_,?_,?_,?_⟩
    · rw [rowSum]
    · rw [common u uF oldU 2 h2,f.anchor.row1,oldU 2 h2]
    · rw [common (u^2) (uF^2) oldSq 2 h2,f.anchor.row2,oldU 2 h2]
    · rw [common g gF oldG 2 h2,f.anchor.rowDefect]
  have a3 : LocalThree R u g 3 := by
    refine ⟨rfl,?_,?_,?_,?_⟩
    · rw [rLast]
      exact r0
    · rw [rLast]
      exact r1
    · rw [rLast]
      exact r2
    · rw [rLast]
      exact rD
  exact ⟨rowSum,rowMoment,a2,a3⟩

/-- Row actions and both local-three anchors of the literal physical
reverse block, transported by the same common gamma. -/
theorem literal_reverse_actions (M : MonomialBasis) (s t c : ℝ)
    (seed : ExactScalarSeed M s t c) :
    ReverseActions (geometry M s t c).R (reverseClock s t) (reverseG s) := by
  let R := reverseNormalized s t
  let u := uAt s t
  let g := gAt s 0
  let γ := (zAt s)⁻¹
  have n := normalized_reverse_actions M s t c seed
  change ReverseActions R u g at n
  obtain ⟨h0,h1⟩ := rescale_global_moments R u g γ n.sum n.moment
  exact ⟨h0,h1,rescale_local_three R u g γ 2 n.anchor2,
    rescale_local_three R u g γ 3 n.anchor3⟩

/-- The old reverse clocks are the same three distinct physical clocks as
the forward common rows. This assertion says nothing about the appended t. -/
theorem literal_reverse_distinct (M : MonomialBasis) (s t c : ℝ)
    (seed : ExactScalarSeed M s t c) :
    let cr := reverseClock s t
    cr 0 ≠ cr 1 ∧ cr 0 ≠ cr 2 ∧ cr 1 ≠ cr 2 :=
  literal_old_distinct M s t c seed

/-- The actual physical projection pivot is gamma² times the normalized
reverse pivot. The latter is nonzero because t is strictly between 0
and s/3, hence not a root of the old quadratic defect. -/
theorem literal_reverse_pivot (M : MonomialBasis) (s t c : ℝ)
    (seed : ExactScalarSeed M s t c) : pivot (reverseClock s t) (reverseG s) ≠ 0 := by
  let γ := (zAt s)⁻¹
  let κ := 3/(2*Bs s)
  let u := uAt s t
  let gn := gAt s 0
  let cr := reverseClock s t
  let gr := reverseG s
  have lo := seed.sLower
  have hi := seed.sUpper
  have tl := seed.tLower
  have tu := seed.tUpper
  have hs : 0 < s := by linarith
  have hS : s < 1 := by linarith
  have ht : t < s/3 := by linarith
  have hγ : γ ≠ 0 := inv_ne_zero (literal_z_pos M s t c seed).ne'
  have hκ : κ ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (mul_ne_zero (by linarith) (by linarith)))
  have ip : interp u gn = seedQuad s κ := reverse_seed_interpolant s t hs hS seed.sRoot
  have hp : pivot u gn ≠ 0 :=
    normalized_reverse_pivot u gn s κ t ip rfl rfl hκ (by linarith) (by linarith)
  have rate (T : ℝ) :
      ev (γ*T) (seedQuad (γ*s) κ) = γ^2 * ev T (seedQuad s κ) := by
    rw [eval_seedQuad,eval_seedQuad]
    ring
  obtain ⟨z0,z1,z2⟩ := seedQuad_old_values (K := ℝ) s (by linarith) (by linarith) seed.sRoot
  have lift (i : Fin 4) (hz : ev (u i) (seedQuad s κ)=gn i) :
      ev (cr i) (seedQuad (γ*s) κ)=gr i := by
    change ev (γ*u i) (seedQuad (γ*s) κ)=γ^2*gn i
    rw [rate,hz]
  obtain ⟨h01,h02,h12⟩ := literal_reverse_distinct M s t c seed
  have iph : interp cr gr = seedQuad (γ*s) κ :=
    interp_eq_seedQuad cr gr (γ*s) κ h01 h02 h12 (lift 0 z0) (lift 1 z1) (lift 2 z2)
  have eq : pivot cr gr = γ^2 * pivot u gn := by
    unfold pivot
    rw [iph,ip]
    change γ^2*0-ev (γ*t) (seedQuad (γ*s) κ)=(γ^2)*(0-ev t (seedQuad s κ))
    rw [rate]
    ring
  rw [eq]
  exact mul_ne_zero (pow_ne_zero 2 hγ) hp

/-- The indices are physical old slots 7,6,5,4, in that order.
Their site labels are 0,1,2,3, respectively. -/
theorem old_site_literal (i : Fin 4) : site (oldIx i) = oldSite i := by
  fin_cases i <;> rfl

private theorem reverse_node (M : MonomialBasis) (s t c : ℝ) (i : Fin 4) :
    yAt M s t c (oldSite i) = reverseClock s t i := by
  rw [norm_nodes,raw_at_old,div_eq_mul_inv]
  change uAt s t i * (zAt s)⁻¹ = (zAt s)⁻¹ * uAt s t i
  exact mul_comm _ _

theorem literal_reflected_sites (M : MonomialBasis) (hm : standardPowers M) (s t c : ℝ) :
    (geometry M s t c).ξ ∘ oldIx = 1 - reverseClock s t := by
  have ex : (geometry M s t c).Ex X=xAt M s t c := evalSites_X M hm _
  change ((geometry M s t c).Ex X ∘ site) ∘ oldIx = 1 - reverseClock s t
  rw [ex]
  funext i
  change 1-yAt M s t c (site (oldIx i))=1-reverseClock s t i
  rw [old_site_literal,reverse_node M s t c i]

theorem literal_reverse_eval_clock (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (i : Fin 4) :
    (geometry M s t c).Ey X (oldSite i) = reverseClock s t i := by
  have ey : (geometry M s t c).Ey X=yAt M s t c := evalSites_X M hm _
  rw [ey,reverse_node M s t c i]

/-- The displayed cubic has its three stated zeros and unit value at
the fourth, distinct site. No reverse coefficients are chosen by fitting. -/
private theorem normalized_cubic_cardinal (M : MonomialBasis) (hm : standardPowers M)
    (x a b c : ℝ) (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    let K := atOne M x (cubic a b c)
    PolyBound 3 K ∧ K.eval a = 0 ∧ K.eval b = 0 ∧ K.eval c = 0 ∧ K.eval x = 1 := by
  let P := cubic a b c
  let K := atOne M x P
  have e (v : ℝ) : P.eval v=(v-a)*(v-b)*(v-c) := by
    simp only [P,cubic,linearFactor,eval_mul,eval_sub,eval_X,eval_C]
  have hP : P.eval x ≠ 0 := by
    rw [e]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)) (sub_ne_zero.mpr hc)
  have evK (v : ℝ) : K.eval v=(P.eval x)⁻¹*P.eval v := by
    simp only [K,atOne,evalAt_eq_eval M hm,Polynomial.eval_smul,smul_eq_mul]
  have dP : P.natDegree ≤ 3 := by
    change (linearFactor a * linearFactor b * linearFactor c).natDegree ≤ 3
    calc
      _ ≤ (linearFactor a * linearFactor b).natDegree + (linearFactor c).natDegree :=
        natDegree_mul_le
      _ ≤ (linearFactor a).natDegree + (linearFactor b).natDegree + (linearFactor c).natDegree :=
        Nat.add_le_add_right natDegree_mul_le _
      _ = 3 := by simp [linearFactor,natDegree_X_sub_C]
  have dK : PolyBound 3 K := by
    apply natDegree_le_iff_coeff_eq_zero.mp
    exact (natDegree_smul_le ((evalAt M x P)⁻¹) P).trans dP
  refine ⟨dK,?_,?_,?_,?_⟩
  · rw [evK a,e a]
    simp only [sub_self,zero_mul,mul_zero]
  · rw [evK b,e b]
    simp only [sub_self,mul_zero,zero_mul]
  · rw [evK c,e c]
    simp only [sub_self,mul_zero]
  · rw [evK,inv_mul_cancel₀ hP]

/-- Four-root unisolvence on the actual reverse sites 0,2,3,4.
In particular both basis polynomials are the literal geometry.KR members. -/
theorem literal_reverse_cubic_cardinal (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (seed : ExactScalarSeed M s t c) :
    let g := geometry M s t c
    ∀ P : ℙ, PolyBound 3 P → g.Ey P 2=0 → g.Ey P 3=0 →
      P = g.Ey P 0 • g.KR 0 + g.Ey P 4 • g.KR 1 := by
  let g := geometry M s t c
  let y := yAt M s t c
  let K0 := g.KR 0
  let K4 := g.KR 1
  have hy : Function.Injective y := literal_nodes_injective M s t c seed
  have eP (P : ℙ) (i : Fin 6) : g.Ey P i=P.eval (y i) := evalAt_eq_eval M hm (y i) P
  have card0 := normalized_cubic_cardinal M hm (y 0) (y 2) (y 3) (y 4)
    (hy.ne (by decide)) (hy.ne (by decide)) (hy.ne (by decide))
  have card4 := normalized_cubic_cardinal M hm (y 4) (y 2) (y 3) (y 0)
    (hy.ne (by decide)) (hy.ne (by decide)) (hy.ne (by decide))
  change PolyBound 3 K0 ∧ K0.eval (y 2)=0 ∧ K0.eval (y 3)=0 ∧
    K0.eval (y 4)=0 ∧ K0.eval (y 0)=1 at card0
  change PolyBound 3 K4 ∧ K4.eval (y 2)=0 ∧ K4.eval (y 3)=0 ∧
    K4.eval (y 0)=0 ∧ K4.eval (y 4)=1 at card4
  obtain ⟨d0,e02,e03,e04,e00⟩ := card0
  obtain ⟨d4,e42,e43,e40,e44⟩ := card4
  change ∀ P : ℙ, PolyBound 3 P → g.Ey P 2=0 → g.Ey P 3=0 →
    P = g.Ey P 0 • K0 + g.Ey P 4 • K4
  intro P hp h2 h3
  rw [eP] at h2 h3
  let D := P - P.eval (y 0) • K0 - P.eval (y 4) • K4
  have dD : PolyBound 3 D := by
    intro k hk
    simp only [D,coeff_sub,Polynomial.coeff_smul,hp k hk,d0 k hk,d4 k hk,smul_zero,sub_zero]
  have p0 : D.eval (y 0)=0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,e00,e40,mul_one,mul_zero,sub_self,sub_zero]
  have p2 : D.eval (y 2)=0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,e02,e42,mul_zero,sub_zero,h2]
  have p3 : D.eval (y 3)=0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,e03,e43,mul_zero,sub_zero,h3]
  have p4 : D.eval (y 4)=0 := by
    simp only [D,eval_sub,Polynomial.eval_smul,smul_eq_mul,e04,e44,mul_one,mul_zero,sub_self,sub_zero]
  let ids : Fin 4 → Fin 6 := ![0,2,3,4]
  have hids : Function.Injective ids := by
    intro i j e
    fin_cases i <;> fin_cases j <;> simp [ids] at e ⊢
  have hw : Function.Injective (y ∘ ids) := hy.comp hids
  have hdeg : D.degree < ((Finset.univ : Finset (Fin 4)).card : WithBot ℕ) := by
    have h : D.degree ≤ ((3 : ℕ) : WithBot ℕ) :=
      degree_le_of_natDegree_le (natDegree_le_iff_coeff_eq_zero.mpr dD)
    exact h.trans_lt (by norm_num)
  have ev (i : Fin 4) : D.eval ((y ∘ ids) i)=0 := by
    fin_cases i
    · exact p0
    · exact p2
    · exact p3
    · exact p4
  have z : D=0 := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
    hw.injOn hdeg (fun i _ => ev i)
  have e : P-P.eval (y 0) • K0=P.eval (y 4) • K4 := sub_eq_zero.mp z
  simp only [eP]
  calc
    P = (P - P.eval (y 0) • K0) + P.eval (y 0) • K0 := (sub_add_cancel _ _).symm
    _ = _ := by rw [e,add_comm]

/-- The literal reverse producer. The same standard monomials and exact
scalar seed as the forward and scalar producers suffice. -/
theorem literal_reverse_leaves (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (seed : ExactScalarSeed M s t c) :
    ReverseLeaves (geometry M s t c) (reverseClock s t) (reverseG s) := by
  obtain ⟨d01,d02,d12⟩ := literal_reverse_distinct M s t c seed
  obtain ⟨low,diag⟩ := literal_reverse_shape M s t c
  have actions := literal_reverse_actions M s t c seed
  exact ⟨d01,d02,d12,literal_reverse_pivot M s t c seed,low,diag,actions.sum,actions.moment,
    literal_reflected_sites M hm s t c,actions.anchor2,actions.anchor3,
    literal_reverse_eval_clock M hm s t c 2,literal_reverse_eval_clock M hm s t c 3,
    literal_reverse_cubic_cardinal M hm s t c seed⟩

end RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralReverseProducer

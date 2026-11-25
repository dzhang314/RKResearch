module

public import RKCert.ReviewedNative.SDIRK118ScalarAffineResponse
public import RKCert.ReviewedNative.SDIRK118ConditionalFin11

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardLiftMoments

open RKResearch
open RKResearch.Certified.Graded (mat)
open RKResearch.Certified.PaidDefectBridge.ForwardChart
open RKResearch.Certified.PaidDefectBridge.ReverseChart
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ConditionalFin11
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarAffineResponse
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature (literal_z_pos)
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation (coordinate)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (matrixOf matrixOf_mulVec rows delta)
open scoped Matrix BigOperators

/-- Four actual forward row moments. The third row additionally gives the
physical local-three anchor, independent of the last-stage projection. -/
structure Actions (G : Matrix (Fin 4) (Fin 4) ℝ) (c g : V ℝ) (γ η : ℝ) : Prop where
  sum : mat G (1 : V ℝ) = c
  clock : mat G c = (2 : ℝ)⁻¹ • c ^ 2 + g
  defect : mat G g = (γ * (1 - η⁻¹)) • g + η⁻¹ • (c * g)
  square : mat G (c ^ 2) = (1/3 : ℝ) • c ^ 3 + (2/3 : ℝ) • (mat G g + c * g)
  anchor : LocalThree G c g 2

theorem eta_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hseed : seedCubic s = 0) :
    0 < etaAt s := by
  have he := eta_clear s hseed
  have hp : 0 < (4 * (3 - s)) * etaAt s := by rw [he]; linarith
  exact pos_of_mul_pos_right hp (by linarith)

private theorem seed_interpolant (s d gd : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hr : seedCubic s = 0) :
    interp (uAt s d) (gAt s gd) = seedQuad s (3 / (2 * Bs s)) := by
  have h01 : uAt s d 0 ≠ uAt s d 1 := by
    change (1 : ℝ) ≠ aAt s
    unfold aAt
    linarith
  have h02 : uAt s d 0 ≠ uAt s d 2 := by change (1 : ℝ) ≠ s; linarith
  have h12 : uAt s d 1 ≠ uAt s d 2 := by
    change aAt s ≠ s
    unfold aAt
    linarith
  have hh := seedQuad_old_values (K := ℝ) s (by linarith) (by linarith) hr
  exact interp_eq_seedQuad (uAt s d) (gAt s gd) s _ h01 h02 h12 hh.1 hh.2.1 hh.2.2

/-- The actual last taps are the three evaluations of the original Cramer
moment functional, with self one. This binds them and the three fixed rows
to all four forward identities. No evaluated chart row is an input. -/
theorem normalized_actions (s d : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hseed : seedCubic s = 0)
    (hL : Ld s (etaAt s) d ≠ 0) :
    let gd := gdAt s (etaAt s) d
    Actions (forwardNormalized s d) (uAt s d) (gAt s gd) 1 (etaAt s) := by
  let a := aAt s
  let h := hAt s
  let v := 2 / (h - 2)
  let η := etaAt s
  let g1 := g1At s
  let gd := gdAt s η d
  let u := uAt s d
  let g := gAt s gd
  let G := forwardNormalized s d
  let f := forwardLast u (d-1) (Ud d gd) (Vd d η gd)
  have ha : 1 + h = a := by dsimp [h,hAt,a]; ring
  have hs : 1 + 2*h = s := by dsimp [h,hAt,aAt]; ring
  have hη : η ≠ 0 := (eta_pos s hs0 hs1 hseed).ne'
  have hB : Bs s ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have hh2 : h - 2 ≠ 0 := by dsimp [h,hAt,aAt]; linarith
  have h0 : 4*h^3-12*h^2+3*h+2=0 := by
    dsimp [h,hAt,aAt]
    unfold seedCubic at hseed
    linear_combination (1/2 : ℝ)*hseed
  have d01 : u 0 ≠ u 1 := by change (1 : ℝ) ≠ (1+s)/2; linarith
  have d02 : u 0 ≠ u 2 := by change (1 : ℝ) ≠ s; linarith
  have d12 : u 1 ≠ u 2 := by change (1+s)/2 ≠ s; linarith
  have he : Ld s η d * gd = (η / 2) * (d - s) * qSeed s d := by
    change Ld s η d * (((η / 2) * (d - s) * qSeed s d) / Ld s η d) = _
    rw [mul_comm (Ld s η d),div_mul_cancel₀ _ hL]
  have act (w : V ℝ) : mat G w = normalizedRows h v f w :=
    matrixOf_mulVec (normalizedRows h v f) w
  have r0 (w : V ℝ) : (mat G w) 0 = w 0 := by rw [act] <;> rfl
  have r1 (w : V ℝ) : (mat G w) 1 = h*w 0+w 1 := by rw [act] <;> rfl
  have r2 (w : V ℝ) : (mat G w) 2 = (2*h-v)*w 0+v*w 1+w 2 := by rw [act] <;> rfl
  have r3 (w : V ℝ) : (mat G w) 3 = f w := by rw [act] <;> rfl
  have seed2 := normalized_third_anchor h hh2 h0
  obtain ⟨u2,v2,w2,z2⟩ := seed2
  change (2*h-v)+v+1=1+2*h at u2
  change (2*h-v)+v*(1+h)+(1+2*h)=(1+2*h)^2/2 at v2
  change (2*h-v)+v*(1+h)^2+(1+2*h)^2=(1+2*h)^3/3 at w2
  change (2*h-v)/2+v*g1=0 at z2
  rw [hs] at u2
  rw [ha,hs] at v2 w2
  have seed1 := normalized_second_row (K := ℝ) h
  obtain ⟨u1,w1⟩ := seed1
  change h+(1+h)-(1+h)^2/2=g1 at u1
  change h+(1+h)^2-(1+h)^3/3=(2/3)*(h/2+(1+(1+h))*g1) at w1
  rw [ha] at u1 w1
  have rowLast := forward_last_frame u g s η d gd d01 d02 d12 rfl rfl
    (seed_interpolant s d gd hs0 hs1 hseed) hB hη he
  obtain ⟨u3,v3,w3,z3⟩ := rowLast
  change f 1=d at u3
  change f u=d^2/2+gd at v3
  change f (u^2)=d^3/3+(2/3)*(f g+d*gd) at w3
  change f g=gd+(d-1)*gd/η at z3
  have r2g : (mat G g) 2 = 0 := by
    rw [r2]
    change (2*h-v)*(1/2)+v*g1+0=0
    linear_combination z2
  have r1g : (mat G g) 1 = h/2+g1 := by
    rw [r1]
    change h*(1/2)+g1=h/2+g1
    ring
  have hη1 : η = 2 * g1 := rfl
  have rowOne : mat G (1 : V ℝ) = u := by
    funext i
    fin_cases i
    · exact r0 1
    · change (mat G (1 : V ℝ)) (1 : Fin 4) = u (1 : Fin 4)
      rw [r1]
      change h*1+1=a
      linear_combination ha
    · change (mat G (1 : V ℝ)) (2 : Fin 4) = u (2 : Fin 4)
      rw [r2]
      change (2*h-v)*1+v*1+1=s
      simpa only [mul_one] using u2
    · change (mat G (1 : V ℝ)) (3 : Fin 4) = u (3 : Fin 4)
      rw [r3]
      exact u3
  have rowCu : mat G u = (2 : ℝ)⁻¹ • u^2 + g := by
    funext i
    fin_cases i
    · change (mat G u) (0 : Fin 4) = ((2 : ℝ)⁻¹ • u^2 + g) (0 : Fin 4)
      rw [r0]
      change (1 : ℝ) = (2 : ℝ)⁻¹*1^2+1/2
      norm_num
    · change (mat G u) (1 : Fin 4) = ((2 : ℝ)⁻¹ • u^2 + g) (1 : Fin 4)
      rw [r1]
      change h*1+a=(2 : ℝ)⁻¹*a^2+g1
      linear_combination u1
    · change (mat G u) (2 : Fin 4) = ((2 : ℝ)⁻¹ • u^2 + g) (2 : Fin 4)
      rw [r2]
      change (2*h-v)*1+v*a+s=(2 : ℝ)⁻¹*s^2+0
      simp only [mul_one,add_zero]
      linear_combination v2
    · change (mat G u) (3 : Fin 4) = ((2 : ℝ)⁻¹ • u^2 + g) (3 : Fin 4)
      rw [r3]
      change f u=(2 : ℝ)⁻¹*d^2+gd
      linear_combination v3
  have rowG : mat G g = ((1 : ℝ)-η⁻¹) • g + η⁻¹ • (u*g) := by
    funext i
    fin_cases i
    · change (mat G g) (0 : Fin 4) = (((1 : ℝ)-η⁻¹) • g + η⁻¹ • (u*g)) (0 : Fin 4)
      rw [r0]
      change (1/2 : ℝ) = (1-η⁻¹)*(1/2)+η⁻¹*(1*(1/2))
      ring
    · change (mat G g) (1 : Fin 4) = (((1 : ℝ)-η⁻¹) • g + η⁻¹ • (u*g)) (1 : Fin 4)
      rw [r1g]
      change h/2+g1=(1-η⁻¹)*g1+η⁻¹*(a*g1)
      rw [← ha]
      field_simp [hη]
      rw [hη1]
      ring
    · change (mat G g) (2 : Fin 4) = (((1 : ℝ)-η⁻¹) • g + η⁻¹ • (u*g)) (2 : Fin 4)
      rw [r2g]
      change (0 : ℝ) = (1-η⁻¹)*0+η⁻¹*(s*0)
      ring
    · change (mat G g) (3 : Fin 4) = (((1 : ℝ)-η⁻¹) • g + η⁻¹ • (u*g)) (3 : Fin 4)
      rw [r3]
      change f g=(1-η⁻¹)*gd+η⁻¹*(d*gd)
      rw [z3]
      rw [div_eq_mul_inv]
      ring
  have rowSq : mat G (u^2) = (1/3 : ℝ) • u^3+(2/3 : ℝ) • (mat G g+u*g) := by
    funext i
    fin_cases i
    · change (mat G (u^2)) (0 : Fin 4) = ((1/3 : ℝ) • u^3+(2/3 : ℝ) • (mat G g+u*g)) (0 : Fin 4)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, r0]
      change (1 : ℝ)^2=(1/3 : ℝ)*1^3+(2/3 : ℝ)*(1/2+1*(1/2))
      norm_num
    · change (mat G (u^2)) (1 : Fin 4) = ((1/3 : ℝ) • u^3+(2/3 : ℝ) • (mat G g+u*g)) (1 : Fin 4)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, r1 (u^2), r1g]
      change h*1^2+a^2=(1/3 : ℝ)*a^3+(2/3 : ℝ)*(h/2+g1+a*g1)
      linear_combination w1
    · change (mat G (u^2)) (2 : Fin 4) = ((1/3 : ℝ) • u^3+(2/3 : ℝ) • (mat G g+u*g)) (2 : Fin 4)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, r2 (u^2), r2g]
      change (2*h-v)*1^2+v*a^2+s^2=(1/3 : ℝ)*s^3+(2/3 : ℝ)*(0+s*0)
      linear_combination w2
    · change (mat G (u^2)) (3 : Fin 4) = ((1/3 : ℝ) • u^3+(2/3 : ℝ) • (mat G g+u*g)) (3 : Fin 4)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, r3]
      change f (u^2)=(1/3 : ℝ)*d^3+(2/3 : ℝ)*(f g+d*gd)
      linear_combination w3
  have anchor : LocalThree G u g 2 := by
    refine ⟨rfl,?_,?_,?_,r2g⟩
    · rw [rowOne]
    · rw [r2]
      change (2*h-v)*1+v*a+s=s^2/2
      simpa only [mul_one] using v2
    · rw [r2]
      change (2*h-v)*1^2+v*a^2+s^2=s^3/3
      simpa only [one_pow,mul_one] using w2
  exact ⟨rowOne,rowCu,by simpa only [one_mul] using rowG,rowSq,anchor⟩

theorem rescale_actions (G : Matrix (Fin 4) (Fin 4) ℝ) (u g : V ℝ) (γ η : ℝ)
    (h : Actions G u g 1 η) :
    Actions (γ • G) (γ • u) ((γ^2) • g) γ η := by
  have hh := rescale_global_moments G u g γ h.sum h.clock
  have sq : ((γ • u)^2 : V ℝ) = (γ^2) • (u^2) := by
    funext i
    simp only [Pi.pow_apply,Pi.smul_apply,smul_eq_mul,mul_pow]
  refine ⟨hh.1,hh.2,?_,?_,rescale_local_three G u g γ 2 h.anchor⟩
  · rw [scale_matrix_action,h.defect]
    funext i
    simp only [Pi.smul_apply,Pi.mul_apply,Pi.add_apply,smul_eq_mul,one_mul]
    ring
  · rw [sq,scale_matrix_action,scale_matrix_action,h.square]
    funext i
    simp only [Pi.smul_apply,Pi.pow_apply,Pi.mul_apply,Pi.add_apply,smul_eq_mul]
    ring

/-- Physical moments of the literal emitted donor on the exact scalar seed.
The only division guard used internally is the already proved L(d)>0. -/
theorem literal_actions (M : MonomialBasis) (s t c : ℝ)
    (seed : ExactScalarSeed M s t c) :
    Actions (geometry M s t c).G (forwardClock M s t c) (forwardG M s t c)
      (geometry M s t c).γ (etaAt s) := by
  let d := dAt M s t c
  let γ := (zAt s)⁻¹
  let gd := gdAt s (etaAt s) d
  have lo := seed.sLower
  have hi := seed.sUpper
  obtain ⟨hd,_,_⟩ := calibrated_real_bracket M s t c seed.affineLowerNeg seed.affineUpperPos
  have hL := Ld_pos s d lo hi seed.sRoot hd
  exact rescale_actions (forwardNormalized s d) (uAt s d) (gAt s gd) γ (etaAt s)
    (normalized_actions s d (by linarith) (by linarith) seed.sRoot hL.ne')

theorem literal_old_distinct (M : MonomialBasis) (s t c : ℝ) (seed : ExactScalarSeed M s t c) :
    let cc := forwardClock M s t c
    cc 0 ≠ cc 1 ∧ cc 0 ≠ cc 2 ∧ cc 1 ≠ cc 2 := by
  let γ := (zAt s)⁻¹
  let a := aAt s
  have hγ : γ ≠ 0 := inv_ne_zero (literal_z_pos M s t c seed).ne'
  have hhi := seed.sUpper
  have ha : a < 1 := by dsimp [a,aAt]; linarith
  have hsa : s < a := by dsimp [a,aAt]; linarith
  change γ*1 ≠ γ*a ∧ γ*1 ≠ γ*s ∧ γ*a ≠ γ*s
  refine ⟨?_,?_,?_⟩
  · intro h
    have := mul_left_cancel₀ hγ h
    linarith
  · intro h
    have := mul_left_cancel₀ hγ h
    linarith
  · intro h
    have := mul_left_cancel₀ hγ h
    linarith

private def scaleQuad (γ : ℝ) (q : Quad ℝ) : Quad ℝ :=
  (γ^2*q.1,γ*q.2.1,q.2.2)

private theorem scaleQuad_eval (γ x : ℝ) (q : Quad ℝ) :
    ev (γ*x) (scaleQuad γ q) = γ^2*ev x q := by
  simp only [scaleQuad,ev_apply]
  ring

/-- The literal physical interpolation pivot is a nonzero scaled
difference between the appended defect and the old seed quadratic.
Its exact guard follows from the cleared factored response, not rank. -/
theorem literal_frame_pivot (M : MonomialBasis) (s t c : ℝ) (seed : ExactScalarSeed M s t c) :
    pivot (forwardClock M s t c) (forwardG M s t c) ≠ 0 := by
  let γ := (zAt s)⁻¹
  let d := dAt M s t c
  let η := etaAt s
  let B := Bs s
  let a := aAt s
  let gd := gdAt s η d
  let u := uAt s d
  let g := gAt s gd
  let q := seedQuad s (3/(2*B))
  let cc := forwardClock M s t c
  let gg := forwardG M s t c
  have hγ : γ ≠ 0 := inv_ne_zero (literal_z_pos M s t c seed).ne'
  have lo := seed.sLower
  have hi := seed.sUpper
  have hs0 : 0 < s := by linarith
  have hs1 : s < 1 := by linarith
  have hb : B ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have hs3 : 3-s ≠ 0 := by linarith
  obtain ⟨hd,_,_⟩ := calibrated_real_bracket M s t c seed.affineLowerNeg seed.affineUpperPos
  have hL := Ld_pos s d lo hi seed.sRoot hd
  have gdE : Ld s η d * gd=(η/2)*(d-s)*qSeed s d := by
    change Ld s η d * (((η/2)*(d-s)*qSeed s d)/Ld s η d) = _
    rw [mul_comm (Ld s η d),div_mul_cancel₀ _ hL.ne']
  have qval : ev d q = (3/(2*B))*(d-s)*(d-rAt s) :=
    eval_seedQuad s (3/(2*B)) d
  have e : Ld s η d * (gd-ev d q) = ((d-s)/(2*B))*leadAt s*(d-1)*(d-a) := by
    rw [qval]
    calc
      _ = (Ld s η d)*gd-Ld s η d*((3/(2*B))*(d-s)*(d-rAt s)) := by ring
      _ = ((d-s)/(2*B))*(η*B*qSeed s d-(3*d-s)*Ld s η d) := by
        rw [gdE]
        unfold rAt
        field_simp [hb] <;> ring
      _ = _ := by rw [seed_factor s d hs3 seed.sRoot]; ring
  have hda : d-a ≠ 0 := by dsimp [a,aAt]; linarith
  have he : ((d-s)/(2*B))*leadAt s*(d-1)*(d-a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (div_ne_zero (by linarith) (mul_ne_zero (by norm_num) hb))
      (lead_ne s hs0 hs1 seed.sRoot)) (by linarith)) hda
  have hdiff : gd-ev d q ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at e
    exact he e.symm
  obtain ⟨s0,s1,s2⟩ := seedQuad_old_values (K := ℝ) s (by linarith) hs3 seed.sRoot
  have test {i : Fin 4} (h : ev (u i) q = g i) :
      ev (cc i) (scaleQuad γ q) = gg i := by
    change ev (γ * u i) (scaleQuad γ q)=γ^2*g i
    rw [scaleQuad_eval,h]
  obtain ⟨h01,h02,h12⟩ := literal_old_distinct M s t c seed
  obtain ⟨e0,e1,e2⟩ := interp_old cc gg h01 h02 h12
  have eq : interp cc gg = scaleQuad γ q :=
    quad_eq_of_three h01 h02 h12 (e0.trans (test (i := 0) s0).symm)
      (e1.trans (test (i := 1) s1).symm) (e2.trans (test (i := 2) s2).symm)
  change gg 3-ev (cc 3) (interp cc gg)≠0
  rw [eq]
  change γ^2*gd-ev (γ*d) (scaleQuad γ q)≠0
  rw [scaleQuad_eval,←mul_sub]
  exact mul_ne_zero (pow_ne_zero 2 hγ) hdiff

/-- The stage shape is a literal property of the common normalized rows,
including the self entry of the last emitted row. It uses no root. -/
theorem normalized_rows_shape (h v : ℝ) (last : V ℝ →ₗ[ℝ] ℝ)
    (self : last (delta (3 : Fin 4)) = 1) :
    let N := matrixOf (normalizedRows h v last)
    N.IsLowerTriangular ∧ ∀ i, N i i = 1 := by
  dsimp only
  constructor
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;>
      simp [matrixOf,normalizedRows,rows,coordinate,delta] at hij ⊢
  · intro i
    fin_cases i
    · simp [matrixOf,normalizedRows,rows,coordinate,delta]
    · simp [matrixOf,normalizedRows,rows,coordinate,delta]
    · simp [matrixOf,normalizedRows,rows,coordinate,delta]
    · change last (delta (3 : Fin 4))=1
      exact self

theorem literal_forward_shape (M : MonomialBasis) (s t c : ℝ) :
    let g := geometry M s t c
    g.G.IsLowerTriangular ∧ ∀ i, g.G i i = g.γ := by
  let d := dAt M s t c
  let γ := (zAt s)⁻¹
  let h := hAt s
  let η := etaAt s
  let gd := gdAt s η d
  let last := forwardLast (uAt s d) (d-1) (Ud d gd) (Vd d η gd)
  have lastSelf : last (delta (3 : Fin 4))=1 := by
    change forwardLast (uAt s d) (d-1) (Ud d gd) (Vd d η gd) (delta (3 : Fin 4))=1
    rw [forwardLast_literal]
    simp [delta]
  have shape := normalized_rows_shape h (2/(h-2)) last lastSelf
  have hn : (forwardNormalized s d).IsLowerTriangular ∧
      ∀ i, forwardNormalized s d i i=1 := shape
  constructor
  · intro i j hij
    change γ * forwardNormalized s d i j = 0
    rw [hn.1 hij,mul_zero]
  · intro i
    change γ*forwardNormalized s d i i=γ
    rw [hn.2 i,mul_one]

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardLiftMoments

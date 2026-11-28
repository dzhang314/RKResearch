module

public import RKCert.ReviewedNative.DIRK12MidpointReverseGuards
public import RKCert.ReviewedNative.DIRK12MidpointReverseShape
public import RKCert.ReviewedNative.DIRK12MidpointReverseBary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Actual cardinal masses at the three grouped labels. Exact
comparison, not their approximate signs, connects the normalized
seed amplitude to the true nine-site barycentric vector. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open Polynomial DIRK12MidpointRealInterval DirectedRatBox
open scoped BigOperators Polynomial

private theorem qa_eq (n : Fin 6 → ℝ) : Shape.qa (n 0) (n 1) (n 2)=aa n := by
  unfold Shape.qa aa lab lbb
  ring

private theorem qb_eq (n : Fin 6 → ℝ) : Shape.qb (n 0) (n 1) (n 2)=bb n := by
  unfold Shape.qb bb lab lbb
  ring

private theorem qc_eq (n : Fin 6 → ℝ) : Shape.qc (n 0) (n 1) (n 2)=cc n := by
  unfold Shape.qc cc lab lbb
  ring

theorem v_norm {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    v x f=d x f*r x f := by
  rw [r,←mul_div_assoc,mul_div_cancel_left₀ _ (d_pos hx hf).ne']

theorem u_norm {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    u x f=d x f*t x f := by
  rw [t,←mul_div_assoc,mul_div_cancel_left₀ _ (d_pos hx hf).ne']

theorem normalized_moments {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    let n := moments x f
    t x f=Shape.tu (r x f) ∧
    n 1=d x f*n 0*Shape.nOne (r x f) ∧
    n 2=(d x f)^2*n 0*Shape.nTwo (r x f) := by
  dsimp only
  let n := moments x f
  have he := moments_enclosed hx hf
  obtain ⟨ha,hb,hc,_,hlab⟩ := all_pivots he
  have an : n 0≠0 := by
    intro e
    have z : lab n=0 := by simp [lab,e]
    exact hlab.ne' z
  have dn := (d_pos hx hf).ne'
  obtain ⟨r0,r1,_,_,bn,_,_,qn⟩ := ratio_guards hx hf
  have hs := div_mul_cancel₀ (6*ee n) ha.ne'
  change S n*aa n=6*ee n at hs
  rw [←orientation_sum x f] at hs
  change (d x f+v x f)*aa n=6*ee n at hs
  have hs' : d x f*(1+r x f)*Shape.qa (n 0) (n 1) (n 2)=6*(n 1*n 2) := by
    rw [qa_eq n]
    rw [v_norm hx hf] at hs
    change (d x f+d x f*r x f)*aa n=6*(n 1*n 2) at hs
    linear_combination hs
  have hp := div_mul_cancel₀ (3*(ee n)^2) (mul_ne_zero ha.ne' hb.ne')
  change P n*(aa n*bb n)=3*(ee n)^2 at hp
  rw [←orientation_prod x f hx hf] at hp
  change d x f*v x f*(aa n*bb n)=3*(n 1*n 2)^2 at hp
  have hp' : (d x f)^2*r x f*Shape.qa (n 0) (n 1) (n 2)*
      Shape.qb (n 0) (n 1) (n 2)=3*(n 1*n 2)^2 := by
    rw [qa_eq n,qb_eq n]
    rw [v_norm hx hf] at hp
    linear_combination hp
  have hu := div_mul_cancel₀ (ee n) hc.ne'
  change u x f*cc n=n 1*n 2 at hu
  have hu' : u x f*Shape.qc (n 0) (n 1) (n 2)=n 1*n 2 := by
    rw [qc_eq n]
    exact hu
  obtain ⟨eqT,eq1,eq2⟩ := Shape.geometry (n 0) (n 1) (n 2)
    (d x f) (r x f) (u x f) an dn r0 (by rw [qa_eq n]; exact ha.ne') hs' hp' hu'
  have bn' : Shape.D (r x f)≠0 := bn
  have qn' : Shape.Q (r x f)≠0 := qn
  have rn : r x f-1≠0 := sub_ne_zero.mpr r1
  change t x f=Shape.tu (r x f) ∧
    n 1=d x f*n 0*Shape.nOne (r x f) ∧ n 2=(d x f)^2*n 0*Shape.nTwo (r x f)
  refine ⟨?_,?_,?_⟩
  · unfold t Shape.tu
    field_simp [dn,bn']
    linear_combination eqT
  · unfold Shape.nOne
    field_simp [rn]
    linear_combination eq1
  · unfold Shape.nTwo
    field_simp [rn,qn']
    linear_combination eq2

noncomputable def cofactor2 (x f a b : ℝ) : ℝ :=
  let n := moments x f
  n 2-(a+b)*n 1+a*b*n 0

private theorem normalized_cofactor (n0 n1 n2 s base1 base2 a b : ℝ)
    (h1 : n1=s*n0*base1) (h2 : n2=s^2*n0*base2) :
    n2-(s*a+s*b)*n1+(s*a)*(s*b)*n0 =
      s^2*n0*(base2-(a+b)*base1+a*b) := by
  rw [h1,h2]
  ring

theorem cofactor_d (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    cofactor2 x f (v x f) (u x f)=
      (d x f)^2*moments x f 0*Shape.normD (r x f) (Shape.tu (r x f))
        (Shape.nOne (r x f)) (Shape.nTwo (r x f)) := by
  obtain ⟨ht,h1,h2⟩ := normalized_moments hx hf
  unfold cofactor2 Shape.normD
  rw [v_norm hx hf,u_norm hx hf,ht]
  exact normalized_cofactor _ _ _ _ _ _ _ _ h1 h2

theorem cofactor_v (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    cofactor2 x f (d x f) (u x f)=
      (d x f)^2*moments x f 0*Shape.normV (r x f) (Shape.tu (r x f))
        (Shape.nOne (r x f)) (Shape.nTwo (r x f)) := by
  obtain ⟨ht,h1,h2⟩ := normalized_moments hx hf
  have h := normalized_cofactor (moments x f 0) (moments x f 1) (moments x f 2)
    (d x f) (Shape.nOne (r x f)) (Shape.nTwo (r x f)) 1 (Shape.tu (r x f)) h1 h2
  unfold cofactor2 Shape.normV
  rw [u_norm hx hf,ht]
  simpa only [mul_one,one_mul] using h

theorem cofactor_u (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    cofactor2 x f (d x f) (v x f)=
      (d x f)^2*moments x f 0*Shape.normU (r x f) (Shape.tu (r x f))
        (Shape.nOne (r x f)) (Shape.nTwo (r x f)) := by
  obtain ⟨_,h1,h2⟩ := normalized_moments hx hf
  have h := normalized_cofactor (moments x f 0) (moments x f 1) (moments x f 2)
    (d x f) (Shape.nOne (r x f)) (Shape.nTwo (r x f)) 1 (r x f) h1 h2
  unfold cofactor2 Shape.normU
  rw [v_norm hx hf]
  simpa only [mul_one,one_mul] using h

noncomputable def rho (x f : ℝ) : ℝ :=
  (d x f)^4*(Seed.sigma*Seed.p (r x f))*(cofactor2 x f (d x f) (u x f)/v x f)

theorem rho_at_d (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    rho x f=(d x f)^4*(-Seed.k (r x f)*Seed.sigma)*
      (cofactor2 x f (v x f) (u x f)/d x f) := by
  have dn := (d_pos hx hf).ne'
  obtain ⟨r0,r1,r2,_,dr,_,_,qr⟩ := ratio_guards hx hf
  have he := Shape.cofactor_pair (r x f) r0 r1 r2 dr qr
  rw [rho,cofactor_d x f hx hf,cofactor_v x f hx hf]
  conv_lhs =>
    arg 2
    arg 2
    rw [v_norm hx hf]
  field_simp [dn,r0] at he ⊢
  linear_combination -(moments x f 0)*he

theorem rho_at_u (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    rho x f=(d x f)^4*Shape.uAmp (r x f)*
      (cofactor2 x f (d x f) (v x f)/u x f) := by
  have dn := (d_pos hx hf).ne'
  obtain ⟨r0,r1,_,_,dr,_,_,qr⟩ := ratio_guards hx hf
  have tn := (state_guards hx hf).1
  have ht := (normalized_moments hx hf).1
  have tt : Shape.tu (r x f)≠0 := ht ▸ tn
  have he := Shape.cofactor_u (r x f) r0 r1 dr qr tt
  rw [rho,cofactor_u x f hx hf,cofactor_v x f hx hf]
  conv_lhs =>
    arg 2
    arg 2
    rw [v_norm hx hf]
  conv_rhs =>
    arg 2
    arg 2
    rw [u_norm hx hf,ht]
  field_simp [dn,r0,tt] at he ⊢
  linear_combination -(moments x f 0)*he

noncomputable def liveNode (x f : ℝ) (i : Fin 9) : ℝ := site x f i.succ
noncomputable def liveWeight (x f : ℝ) (i : Fin 9) : ℝ :=
  Lagrange.nodalWeight Finset.univ (liveNode x f) i

theorem liveNode_distinct {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Function.Injective (liveNode x f) :=
  (site_distinct hx hf).comp (Fin.succ_injective _)

theorem liveWeight_nz {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) (j : Fin 9) :
    liveWeight x f j≠0 :=
  Lagrange.nodalWeight_ne_zero
    (Set.injOn_of_injective (liveNode_distinct hx hf)) (Finset.mem_univ j)

private theorem nodal_omitted (c : Fin 10 → ℝ) (j : Fin 10) :
    Lagrange.nodal (Finset.univ.erase j) c = hull (omitted c j) := by
  have e : (Finset.univ : Finset (Fin 10)).erase j = Finset.univ.map (Fin.succAboveEmb j) := by
    ext i
    simp [Fin.exists_succAbove_eq_iff]
  rw [e]
  unfold Lagrange.nodal
  rw [Finset.prod_map,← Fin.prod_ofFn,hull_as_product,omitted,List.map_ofFn]
  rfl

theorem mass_factor (x f : ℝ) (j : Fin 9) :
    cardinalWeight x f j.succ=liveWeight x f j*
      (integral (hull (omitted (site x f) j.succ))/site x f j.succ) := by
  rw [cardinalWeight,Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ j.succ),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ j.succ),nodal_omitted,
    ← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,Bary.split_zero _ (by rfl)]
  unfold liveWeight liveNode
  ring

theorem mass_d (x f : ℝ) :
    cardinalWeight x f 7=liveWeight x f 6*(cofactor2 x f (v x f) (u x f)/d x f) := by
  have e := mass_factor x f (6:Fin 9)
  change cardinalWeight x f 7=liveWeight x f 6*
    (integral (hull (fixed x f++[v x f,u x f]))/d x f) at e
  rw [Bary.integral_two] at e
  exact e

theorem mass_v (x f : ℝ) :
    cardinalWeight x f 8=liveWeight x f 7*(cofactor2 x f (d x f) (u x f)/v x f) := by
  have e := mass_factor x f (7:Fin 9)
  change cardinalWeight x f 8=liveWeight x f 7*
    (integral (hull (fixed x f++[d x f,u x f]))/v x f) at e
  rw [Bary.integral_two] at e
  exact e

theorem mass_u (x f : ℝ) :
    cardinalWeight x f 9=liveWeight x f 8*(cofactor2 x f (d x f) (v x f)/u x f) := by
  have e := mass_factor x f (8:Fin 9)
  change cardinalWeight x f 9=liveWeight x f 8*
    (integral (hull (fixed x f++[d x f,v x f]))/u x f) at e
  rw [Bary.integral_two] at e
  exact e

end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.normalized_moments
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.rho_at_d
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.rho_at_u
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.mass_d
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.mass_v
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.mass_u

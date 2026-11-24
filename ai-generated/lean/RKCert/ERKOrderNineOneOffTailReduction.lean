module

public import RKCert.ERKOrderNineOneOffTailStages
public import RKCert.ERKOrderNineOneOffTailProfiles
public import RKCert.ERKOrderNineStateSupport

@[expose] public section

/-! # Tail collapse by polynomial degree, even with repeated or ghost late rows -/
namespace RKCert.Paired.OneOff.Seven
open Polynomial Module RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

theorem tail_profile_reduction (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12))) {n : ℕ} (n3 : 3≤n) {v : Vec K 12}
    (profile : TailProfile A a n v) (start0 : ∀ r, r < (7:Fin 12) → v r=0) :
    ∃ P : K[X], P.natDegree≤n ∧
      (∀ r, r≠Fin.last 11 → g A r=0 → v r=P.eval (nodes A r)) ∧
      (∀ r, g A r≠0 → v r=0) := by
  let z := nodes A (5:Fin 12)
  let t := 2*d
  have sixth := order9_sixth_feature ha ho oneOff D F
  have C4 := order9_clean_four ha ho oneOff D F
  obtain ⟨L,Ld,ordinary⟩ := ordinary_curve D7 D.base.dn sixth.2.1 sixth.2.2.2.1
  obtain ⟨P,Q,β,Pd,Qd,p⟩ := profile
  have at_on (r : Fin 12) (lr : r < (7:Fin 12)) (g0 : g A r=0) :
      (0:K)+scaledH A a r*0=P.eval (nodes A r)+scaledH A a r*Q.eval (nodes A r) := by
    have e := p r
    rw [start0 r lr,g0,mul_zero,add_zero] at e
    simpa only [mul_zero,add_zero] using e
  have f3 := at_on (3:Fin 12) (by decide) C4.g3
  have f4 := at_on (4:Fin 12) (by decide) C4.g4
  have f5 := at_on (5:Fin 12) (by decide) C4.g5
  have f6 := at_on (6:Fin 12) (by decide) D7.g7
  rw [C4.node3] at f3
  rw [C4.node4] at f4
  rw [C4.node5] at f5
  rw [D7.node7] at f6
  obtain ⟨pt,qt⟩ := common_clock_affine_parameters C4.diff f3 f4
  obtain ⟨pz,qz⟩ := common_clock_affine_parameters D7.Hdiff f5 f6
  have dQL : (Q*L).natDegree≤n :=
    (natDegree_mul_le_of_le Qd Ld).trans (by omega)
  have dP : (P+Q*L).natDegree≤n := (natDegree_add_le_of_le Pd dQL).trans (max_self _).le
  refine ⟨P+Q*L,dP,?_,?_⟩
  · intro r rT gon
    simp only [eval_add,eval_mul,p r,gon,mul_zero,add_zero]
    by_cases tEq : nodes A r=t
    · rw [tEq,pt,qt]; simp
    by_cases zEq : nodes A r=z
    · rw [zEq,pz,qz]; simp
    rw [ordinary r rT gon tEq zEq]
    ring
  · intro r off
    have first : nodes A (1:Fin 12)=a ∧ g A (1:Fin 12)=baseAmp a ∧ h A (1:Fin 12)=0 := by
      simpa [chartNode,chartDefect,chartH] using F.features 1
    have en := p (1:Fin 12)
    rw [start0 _ (by decide),first.1,first.2.1,scaledH_eval,first.2.2,zero_div,zero_mul,add_zero] at en
    have pr := congrFun (order9_defects_separate ha ho oneOff D) r
    change g A r*h A r=0 at pr
    rw [p r,D.base.origin.off_support r off,amplitude_value D.base.amplitude off,
      scaledH_eval,(mul_eq_zero.mp pr).resolve_left off,zero_div,zero_mul,add_zero]
    exact en.symm

/-- A polynomial with exactly its paid number of distinct roots leaves
one scale and a single free terminal coordinate. -/
theorem assemble_tail_from_nodal_hull {v w : Vec K 12} {P : K[X]} {S : Finset K}
    (pd : P.natDegree≤S.card) (roots : ∀ x∈S, P.eval x=0)
    (vOn : ∀ r, r≠Fin.last 11 → g A r=0 → v r=P.eval (nodes A r))
    (vOff : ∀ r, g A r≠0 → v r=0)
    (wOn : ∀ r, g A r=0 → w r=(nodalHull S).eval (nodes A r))
    (wOff : ∀ r, g A r≠0 → w r=0) :
    ∃ k τ : K, v=k • w+τ • Pi.single (Fin.last 11) 1 := by
  obtain ⟨k,eq⟩ := polynomial_scalar_hull S P pd roots
  refine ⟨k,v (Fin.last 11)-k*w (Fin.last 11),?_⟩
  ext r
  by_cases hr : r=Fin.last 11
  · subst r
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one]
    ring
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_of_ne hr,mul_zero,add_zero]
  by_cases gr : g A r=0
  · rw [vOn r hr gr,wOn r gr,eq,eval_mul,eval_C]
  · rw [vOff r gr,wOff r gr,mul_zero]

end RKCert.Paired.OneOff.Seven

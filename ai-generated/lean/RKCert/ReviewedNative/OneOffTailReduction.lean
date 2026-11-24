module

public import RKCert.ReviewedNative.OneOffTailStages
public import RKCert.ReviewedNative.OneOffTailProfiles

@[expose] public section

/-! # Tail collapse by polynomial degree, even with repeated or ghost late rows -/
namespace RKResearch.Certified.Graded.OneOff.Seven
open RKResearch Polynomial Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

/-- The nodal product built with Mathlib's coprime linear factors. -/
noncomputable def nodalHull (S : Finset K) : K[X] := ∏ x ∈ S, (X-C x)

omit [CharZero K] in
theorem polynomial_scalar_hull (S : Finset K) (P : K[X]) (hd : P.natDegree≤S.card)
    (h : ∀ x∈S, P.eval x=0) : ∃ a : K, P=C a*nodalHull S := by
  have dvd : nodalHull S ∣ P := by
    unfold nodalHull
    apply Finset.prod_dvd_of_coprime
    · intro x hx y hy ne
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit
    · intro x hx
      exact dvd_iff_isRoot.mpr (h x hx)
  obtain ⟨R,he⟩ := dvd
  by_cases hR : R=0
  · exact ⟨0,by simp [he,hR]⟩
  · have mon : (nodalHull S).Monic := monic_prod_X_sub_C id S
    have hdH : (nodalHull S).natDegree=S.card := natDegree_finsetProd_X_sub_C_eq_card S id
    have hdeg := natDegree_mul mon.ne_zero hR
    rw [←he,hdH] at hdeg
    have hc : R=C (R.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    exact ⟨R.coeff 0,by rw [he,hc,mul_comm,coeff_C_zero]⟩

theorem tail_profile_reduction (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12))) {n : ℕ} (n3 : 3≤n) {v : Fin 12 → K}
    (profile : TailProfile A a n v) (start0 : ∀ r, r < (7:Fin 12) → v r=0) :
    ∃ P : K[X], P.natDegree≤n ∧
      (∀ r, r≠Fin.last 11 → g A r=0 → v r=P.eval (nodes A r)) ∧
      (∀ r, g A r≠0 → v r=0) := by
  let z := nodes A (5:Fin 12)
  let t := 2*d
  have sixth := order9_sixth_feature ha ho D F
  have C4 := order9_clean_four ha ho D F
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
    have pr := congrFun (order9_defects_separate ha ho D) r
    change g A r*h A r=0 at pr
    rw [p r,D.base.origin.off_support r off,amplitude_value D.base.amplitude off,
      scaledH_eval,(mul_eq_zero.mp pr).resolve_left off,zero_div,zero_mul,add_zero]
    exact en.symm

omit [CharZero K] in
/-- A polynomial with exactly its paid number of distinct roots leaves
one scale and a single free terminal coordinate. -/
theorem assemble_tail_from_nodal_hull {v w : Fin 12 → K} {P : K[X]} {S : Finset K}
    (pd : P.natDegree≤S.card) (roots : ∀ x∈S, P.eval x=0)
    (vOn : ∀ r, r≠Fin.last 11 → g A r=0 → v r=P.eval (nodes A r))
    (vOff : ∀ r, g A r≠0 → v r=0)
    (wOn : ∀ r, g A r=0 → w r=(nodalHull S).eval (nodes A r))
    (wOff : ∀ r, g A r≠0 → w r=0) :
    ∃ k τ : K, v=k • w+τ • Reverse.coordinate (Fin.last 11) := by
  obtain ⟨k,eq⟩ := polynomial_scalar_hull S P pd roots
  refine ⟨k,v (Fin.last 11)-k*w (Fin.last 11),?_⟩
  ext r
  by_cases hr : r=Fin.last 11
  · subst r
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Reverse.coordinate,Pi.single_eq_same,mul_one]
    ring
  have zr : Reverse.coordinate (K:=K) (Fin.last 11) r=0 := by
    have hr' : r ≠ (11 : Fin 12) := fun he => hr (he.trans (by decide))
    simp [Reverse.coordinate,hr']
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,zr,mul_zero,add_zero]
  by_cases gr : g A r=0
  · rw [vOn r hr gr,wOn r gr,eq,eval_mul,eval_C]
  · rw [vOff r gr,wOff r gr,mul_zero]

end RKResearch.Certified.Graded.OneOff.Seven

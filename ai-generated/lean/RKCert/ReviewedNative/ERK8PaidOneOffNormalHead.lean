module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffReceiverPrefix
public import RKCert.ReviewedNative.EndpointAdjoint

@[expose] public section

/-! # Shared physical head for both global normal-form branches -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

/-- From the three old features, the next off row has no Ag amplitude,
and an on row's Ag amplitude is fixed by its clock. No comparison
between a and d is needed, even if both stages share a clock. -/
theorem normal_head_row (ha : ∀ i j, i ≤ j → A i j = 0) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) (r : Fin s)
    (pre : ∀ l, l < r → ThreeFeatures a d (twoHd a d) (nodes A l) (g A l) (h A l)) :
    (a*d*M1 A r= -2*d*h A r-4*k A r) ∧
    (g A r≠0 → h A r=0) ∧
    (g A r=0 → 4*d*h A r= -a*(nodes A r)^2*(3*d-2*nodes A r)) := by
  have an := D.origin.a_ne
  have dn := D.dn
  have Hd : twoHd a d≠0 := div_ne_zero (mul_ne_zero
    (neg_ne_zero.mpr an) (pow_ne_zero 2 dn)) (by eight_num)
  obtain ⟨M₁,M₂,_⟩ := three_sources_actions ha r an Hd pre
  have e1 : a*d*M1 A r= -2*d*h A r-4*k A r := by
    rw [M₁]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn]
    eight_ring K
  have rel : a*(M2 A r-d*M1 A r)=2*(d-a)*h A r := by
    rw [M₁,M₂]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn]
    eight_ring K
  have q2 : 3*a*M2 A r=a*(nodes A r)^3+2*a^2*g A r+(4*d-6*a)*h A r := by
    rw [m2_relation D.q2]
    dsimp only [twoLam]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]
    eight_ring K
  refine ⟨e1,?_,?_⟩
  · intro ng
    have ga := amplitude_value D.amplitude ng
    have ca := D.origin.off_support r ng
    have m1 : M1 A r=0 := by rw [m1_relation,ca,ga]; eight_ring K
    rw [m1,mul_zero,sub_zero] at rel
    rw [ca,ga] at q2
    have e : 2*d*h A r=0 := by linear_combination (norm := eight_ring K) q2-3*rel
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by eight_num) dn)
  · intro g0
    have m1 : M1 A r=(nodes A r)^2/2 := by rw [m1_relation,g0,add_zero]
    rw [m1] at rel
    rw [g0,mul_zero,add_zero] at q2
    linear_combination (norm := eight_ring K) 2*q2-6*rel

theorem normal_three_features_before (ha : ∀ i j, i ≤ j → A i j = 0) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) (stop : Fin s) (before : ∀ r, r < stop → k A r=0) :
    ∀ r, r < stop → ThreeFeatures a d (twoHd a d) (nodes A r) (g A r) (h A r) := by
  intro r
  refine wellFounded_lt.induction (C:=fun r : Fin s=>r < stop →
    ThreeFeatures a d (twoHd a d) (nodes A r) (g A r) (h A r)) r ?_
  intro r ih rs
  obtain ⟨e,fo,fn⟩ := normal_head_row ha D r (fun l lr=>ih l lr (lr.trans rs))
  by_cases g0 : g A r=0
  · have sc := fn g0
    rw [before r rs,mul_zero,sub_zero,m1_relation,g0,add_zero] at e
    have hz : a*((nodes A r)^2*(nodes A r-d))=0 := by linear_combination (norm := eight_ring K) e-(1/2:K)*sc
    have prod := (mul_eq_zero.mp hz).resolve_left D.origin.a_ne
    by_cases x0 : nodes A r=0
    · have h0 : h A r=0 := by
        rw [x0] at sc
        have e : 4*d*h A r=0 := by linear_combination (norm := eight_ring K) sc
        exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by eight_num) D.dn)
      exact Or.inl ⟨x0,g0,h0⟩
    · have cd := sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left (pow_ne_zero 2 x0))
      have hd : h A r=twoHd a d := by
        rw [cd] at sc
        apply mul_left_cancel₀ (mul_ne_zero (by eight_num) D.dn : (4:K)*d≠0)
        linear_combination (norm := eight_ring K) sc
      exact Or.inr (Or.inr ⟨cd,g0,hd⟩)
  · exact Or.inr (Or.inl ⟨D.origin.off_support r g0,amplitude_value D.amplitude g0,fo g0⟩)

theorem normal_cubic_with_extra (ha : ∀ i j, i ≤ j → A i j = 0) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) {z : Fin s → K}
    (span : zeroSpace A 4=zeroSpace A 3⊔Submodule.span K {z})
    (zi : z i=0) (zj : z j=0) :
    ∃ v : K, mDef A 3=((a^2/2) • g A+twoMu a d • h A)+v • z := by
  obtain ⟨alpha,mu,nu,Q⟩ := rank_three_rep D.span_three span (mDef_mem A 3)
  have ae := coefficient_of_first_g ha D.origin zi Q
  subst alpha
  have pre (l : Fin s) (lj : l < j) : nodes A l=0 ∨ nodes A l=a := by
    rcases D.first_h.prefix_features l lj with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have c : M3 A j=a^2*M1 A j := clock_power_action ha 2 pre
  have e := m3_relation Q j
  rw [c,m1_relation,D.node,D.clean,zj,mul_zero,add_zero,mul_zero,add_zero] at e
  have mu' : mu=twoMu a d := by
    apply mul_right_cancel₀ D.first_h.nonzero
    calc
      mu*h A j=a^2*(d^2/2)-d^4/4 := by linear_combination (norm := eight_ring K) -e
      _ = twoMu a d*h A j := by
        rw [D.hj]
        field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne]
        eight_ring K
  exact ⟨nu,by simpa only [mu'] using Q⟩

end RKResearch.Certified.Graded.OneOff.PaidProof

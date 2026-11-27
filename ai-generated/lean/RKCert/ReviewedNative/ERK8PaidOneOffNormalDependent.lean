module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffNormalClock
public import RKCert.ReviewedNative.ERK8PaidOneOffNormalSources
public import RKCert.ReviewedNative.ERK8PaidOneOffResiduals

@[expose] public section

/-! # The constant-amplitude dependent clock forces too few nodes -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

def depRes (a d x G H : K) : K :=
  let y := 3*d/2
  let m1 := rowM1 x G
  let m2 := rowM2 a (twoLam a d) x G H
  normalCubSource a d y m1 m2 H-
    rowM3 a (twoMu a d) (d/(2*a)) x G H (normalHSource a d y (twoHd a d) 0 m1 m2 H)

theorem dep_res_factor (a d x G H : K) (an : a≠0) (dn : d≠0) :
    (16*a)*depRes a d x G H=
      -(a*x^2*(2*x-3*d)^2+2*a*G*(2*a-3*d)^2+4*d^2*H) := by
  have ny : 3*d/2≠0 := div_ne_zero (mul_ne_zero (by eight_num) dn) (by eight_num)
  have yd : 3*d/2-d≠0 := by intro e; exact dn (by linear_combination (norm := eight_ring K) 2*e)
  unfold depRes
  dsimp only [rowM1,rowM2,rowM3,normalCubSource,normalHSource,twoLam,twoMu,twoHd,baseAmp]
  simp only [zero_div,zero_mul,add_zero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn,ny,yd]
  eight_ring K

private theorem dependent_first_k (ha : ∀ i j, i ≤ j → A i j = 0) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) (zeroD : deltaH A d=0)
    {nu : K} (eq3 : mDef A 3=((a^2/2) • g A+twoMu a d • h A)+nu • k A)
    (kn : k A≠0) : nu=d/(2*a) := by
  obtain ⟨r,nr,kpre⟩ := exists_first_nonzero kn
  have pre := normal_three_features_before ha D r kpre
  obtain ⟨M,fo,on⟩ := normal_head_row ha D r pre
  have gr : g A r=0 := by
    by_contra ng
    have o := D.origin.off_support r ng
    have f := fo ng
    have p := amplitude_value D.amplitude ng
    rw [m1_relation,o,p,f] at M
    exact nr (by linear_combination (norm := eight_ring K) (1/4:K)*M)
  have sc := on gr
  have ne : nodes A r≠d := by
    intro same
    rw [same] at sc
    have hd : h A r=twoHd a d := by
      apply mul_left_cancel₀ (show (4:K)*d≠0 from mul_ne_zero (by eight_num) D.dn)
      linear_combination (norm := eight_ring K) sc
    rw [m1_relation,gr,add_zero,same,hd] at M
    exact nr (by linear_combination (norm := eight_ring K) (1/4:K)*M)
  have h0 : h A r=0 := by
    have z : (nodes A r-d)*h A r=0 := by
      rw [←deltaH_apply,zeroD]; rfl
    exact (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr ne)
  have nz : nodes A r≠0 := by
    intro e
    rw [m1_relation,gr,add_zero,e,h0] at M
    exact nr (by linear_combination (norm := eight_ring K) (1/4:K)*M)
  have cr : nodes A r=3*d/2 := by
    rw [h0,mul_zero] at sc
    have z := (mul_eq_zero.mp sc.symm).resolve_left
      (mul_ne_zero (neg_ne_zero.mpr D.origin.a_ne) (pow_ne_zero 2 nz))
    linear_combination (norm := eight_ring K) -(1/2:K)*z
  have kr : k A r= -(9*a*d^3)/32 := by
    rw [m1_relation,gr,add_zero,cr,h0] at M
    linear_combination (norm := eight_ring K) (1/4:K)*M
  have Hd : twoHd a d≠0 := div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr D.origin.a_ne) (pow_ne_zero 2 D.dn)) (by eight_num)
  obtain ⟨_,_,m3⟩ := three_sources_actions ha r D.origin.a_ne Hd pre
  have m3r : M3 A r=9*d^4/8 := by
    rw [m3,h0,kr]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne,D.dn]
    eight_ring K
  have qe := m3_relation eq3 r
  rw [m3r,cr,gr,h0,kr] at qe
  have kns : -(9*a*d^3)/32≠0 := div_ne_zero (neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by eight_num) D.origin.a_ne) (pow_ne_zero 3 D.dn))) (by eight_num)
  apply mul_right_cancel₀ kns
  calc
    nu*(-(9*a*d^3)/32)=9*d^4/8-(3*d/2)^4/4 := by linear_combination (norm := eight_ring K) -qe
    _ = (d/(2*a))*(-(9*a*d^3)/32) := by
      field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne]
      eight_ring K

/-- If the first clean clock eigenvector had no new clock feature at
grade four, an actual four-feature closure would contradict separation. -/
theorem deltaH_small_rank_impossible (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3)
    {a d : K} {i j : Fin s} (D : ConstantAmplitude A a d i j) :
    deltaH A d∉zeroSpace A 3 := by
  intro low
  have z0 := deltaH_zero_of_small_rank ha D low
  have k3 := k_out_of_grade_three_if_delta_zero ha sep D z0
  have km : k A∈zeroSpace A 4 := mat_zeroSpace_bounded A 3 (h_in_grade_three A)
  obtain ⟨ki,kj⟩ := k_calibration_zeros ha D
  obtain ⟨nu,eq3⟩ := normal_cubic_with_extra ha D (extra_rank_three_span rank3 rank4 km k3) ki kj
  have kn : k A≠0 := fun e=>k3 (e ▸ (zeroSpace A 3).zero_mem)
  have n := dependent_first_k ha D z0 eq3 kn
  subst nu
  let y := 3*d/2
  have yn : y≠0 := div_ne_zero (mul_ne_zero (by eight_num) D.dn) (by eight_num)
  have yd : y≠d := by intro e; apply D.dn; change 3*d/2=d at e; linear_combination (norm := eight_ring K) 2*e
  have all (r : Fin s) : NormalFour a d y (twoHd a d) 0 (nodes A r) (g A r) (h A r) := by
    refine wellFounded_lt.induction (C:=fun r=>
      NormalFour a d y (twoHd a d) 0 (nodes A r) (g A r) (h A r)) r ?_
    intro r ih
    have C := normal_four_cubic ha r D.origin.a_ne ih
    have H := normal_four_h ha r D.origin.a_ne D.dn yn yd ih
    have eq : depRes a d (nodes A r) (g A r) (h A r)=0 := by
      dsimp only [depRes,rowM1,rowM2,rowM3]
      rw [←m1_relation A r,←m2_relation D.q2 r,←H,←C,←m3_relation eq3 r,sub_self]
    have s := dep_res_factor a d (nodes A r) (g A r) (h A r) D.origin.a_ne D.dn
    rw [eq,mul_zero] at s
    have sc : a*(nodes A r)^2*(2*nodes A r-3*d)^2+2*a*g A r*(2*a-3*d)^2+
        4*d^2*h A r=0 := by linear_combination (norm := eight_ring K) s
    by_cases g0 : g A r=0
    · by_cases d0 : nodes A r=d
      · have hD : h A r=twoHd a d := by
          rw [d0,g0] at sc
          apply mul_left_cancel₀ (show (4:K)*d^2≠0 from
            mul_ne_zero (by eight_num) (pow_ne_zero 2 D.dn))
          linear_combination (norm := eight_ring K) sc
        exact Or.inl (Or.inr (Or.inr ⟨d0,g0,hD⟩))
      · have e : (nodes A r-d)*h A r=0 := by rw [←deltaH_apply,z0]; rfl
        have h0 := (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr d0)
        by_cases c0 : nodes A r=0
        · exact Or.inl (Or.inl ⟨c0,g0,h0⟩)
        · rw [g0,h0,mul_zero,mul_zero,zero_mul,add_zero,add_zero] at sc
          have sq := (mul_eq_zero.mp sc).resolve_left
            (mul_ne_zero D.origin.a_ne (pow_ne_zero 2 c0))
          have e : 2*nodes A r-3*d=0 := by by_contra h; exact pow_ne_zero 2 h sq
          have cy : nodes A r=y := by change nodes A r=3*d/2; linear_combination (norm := eight_ring K) (1/2:K)*e
          exact Or.inr ⟨cy,g0,h0⟩
    · have ca := D.origin.off_support r g0
      have ga := amplitude_value D.amplitude g0
      rw [ca,ga] at sc
      have h0 : h A r=0 := by
        have e : 4*d^2*h A r=0 := by linear_combination (norm := eight_ring K) sc
        exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by eight_num) (pow_ne_zero 2 D.dn))
      exact Or.inl (Or.inr (Or.inl ⟨ca,ga,h0⟩))
  apply sep.knots_not_cover ({0,a,d,y}:Finset K)
  · exact (Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Finset.card_insert_le ..).trans
      (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp)))))
  · intro r
    rcases all r with (e|e|e)|e <;> simp [e.1]

end RKResearch.Certified.Graded.OneOff.PaidProof

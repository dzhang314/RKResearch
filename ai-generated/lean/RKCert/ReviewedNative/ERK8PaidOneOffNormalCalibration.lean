module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffNormalDependent

@[expose] public section

/-! # Actual first new clean clock calibration -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open scoped Matrix
open Module

variable {K : Type*} [Field K] [EightUnits K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

abbrev normHe (a d e : K) := -a*e^2*(3*d-2*e)/(4*d)
abbrev normKap (d e : K) := d/(3*d-2*e)
abbrev normNu (a d e : K) := -d*(d-e)/(a*(3*d-2*e))

/-- A real chronological new clock of Ag in the constant-amplitude
case. The only normalizers are those proved at the selected row. -/
structure NormalCalibration (A : Matrix (Fin s) (Fin s) K) (a d e : K) : Prop where
  en : e≠0
  ed : e≠d
  dNorm : 3*d-2*e≠0
  k_eq : k A=normKap d e • deltaH A d
  q_eq : mDef A 3=((a^2/2) • g A+twoMu a d • h A)+normNu a d e • deltaH A d

theorem normal_clock_calibration (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3)
    {a d : K} {i j : Fin s} (D : ConstantAmplitude A a d i j) :
    ∃ e : K, NormalCalibration A a d e := by
  let Z := deltaH A d
  have zo : Z∉zeroSpace A 3 := deltaH_small_rank_impossible ha sep rank3 rank4 D
  have zm := deltaH_in_grade_four A d
  have nz : Z≠0 := fun e=>zo (e ▸ (zeroSpace A 3).zero_mem)
  have span := extra_rank_three_span rank3 rank4 zm zo
  obtain ⟨zi,zj⟩ := deltaH_calibration_zeros ha D
  obtain ⟨ki,kj⟩ := k_calibration_zeros ha D
  obtain ⟨kap,ke⟩ := vanish_at_two_implies_extra ha D.origin D.first_h D.span_three span
    zi zj (mat_zeroSpace_bounded A 3 (h_in_grade_three A)) ki kj
  obtain ⟨nu,qe⟩ := normal_cubic_with_extra ha D span zi zj
  obtain ⟨r,nr,pz⟩ := exists_first_nonzero nz
  have pr (l : Fin s) (lr : l < r) : k A l=0 := by
    have e : k A l=kap*Z l := by
      simpa only [Pi.smul_apply,smul_eq_mul] using congrFun ke l
    rw [e,pz l lr,mul_zero]
  have pre := normal_three_features_before ha D r pr
  obtain ⟨m1,off,clean⟩ := normal_head_row ha D r pre
  let e := nodes A r
  have zr : Z r=(e-d)*h A r := deltaH_apply A d r
  have prodN : (e-d)*h A r≠0 := by rwa [←zr]
  have hn := right_ne_zero_of_mul prodN
  have ed := sub_ne_zero.mp (left_ne_zero_of_mul prodN)
  have on : g A r=0 := by by_contra x; exact hn (off x)
  have H := clean on
  change 4*d*h A r= -a*e^2*(3*d-2*e) at H
  have denH : (4:K)*d≠0 := mul_ne_zero (by eight_num) D.dn
  have HN : -a*e^2*(3*d-2*e)≠0 := H ▸ mul_ne_zero denH hn
  have dm := right_ne_zero_of_mul HN
  have en : e≠0 := by intro q; exact HN (by simp [q])
  have az : (4*d)*Z r=a*e^2*(d-e)*(3*d-2*e) := by
    rw [zr]
    linear_combination (norm := eight_ring K) (e-d)*H
  rw [m1_relation,on,add_zero] at m1
  change a*d*(e^2/2)= -2*d*h A r-4*k A r at m1
  have kR : k A r=a*e^2*(d-e)/4 := by
    linear_combination (norm := eight_ring K) (1/4:K)*m1-(1/8:K)*H
  have dE := sub_ne_zero.mpr (Ne.symm ed)
  have kap' : kap=normKap d e := by
    have y : k A r=kap*Z r := by simpa only [Pi.smul_apply,smul_eq_mul] using congrFun ke r
    have ys := congrArg ((4*d) * ·) y
    rw [kR,mul_left_comm (4*d) kap,az] at ys
    apply (eq_div_iff dm).mpr
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero D.origin.a_ne (pow_ne_zero 2 en)) dE)
    linear_combination (norm := eight_ring K) -ys
  have nu' : nu=normNu a d e := by
    have H_dN : twoHd a d≠0 := div_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr D.origin.a_ne) (pow_ne_zero 2 D.dn)) (by eight_num)
    obtain ⟨_,_,m3⟩ := three_sources_actions ha r D.origin.a_ne H_dN pre
    have ml : a*M3 A r= -2*a^2*h A r-4*d*k A r := by
      rw [m3]
      field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne,D.dn]
      eight_ring K
    have mr : a*M3 A r=a*e^4/4+(d^2-2*a^2)*h A r+a*nu*Z r := by
      rw [m3_relation qe r,on]
      change a*(e^4/4+(a^2/2)*0+((d^2-2*a^2)/a)*h A r+nu*Z r)=_
      field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne]
      eight_ring K
    have q3 : a*e^4/4+d^2*h A r+4*d*k A r+a*nu*Z r=0 := by
      linear_combination (norm := eight_ring K) ml-mr
    have q : nu*Z r= -(e^2*(d-e)^2)/4 := by
      apply mul_left_cancel₀ D.origin.a_ne
      linear_combination (norm := eight_ring K) q3-(d/4)*H-4*d*kR
    have qs := congrArg ((4*d) * ·) q
    rw [mul_left_comm (4*d) nu,az] at qs
    apply (eq_div_iff (mul_ne_zero D.origin.a_ne dm)).mpr
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 en) dE)
    linear_combination (norm := eight_ring K) qs
  refine ⟨e,⟨en,ed,dm,?_,?_⟩⟩
  · simpa only [kap'] using ke
  · simpa only [nu'] using qe

end RKResearch.Certified.Graded.OneOff.PaidProof

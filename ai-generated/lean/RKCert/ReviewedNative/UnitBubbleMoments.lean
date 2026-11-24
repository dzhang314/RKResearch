module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Orthogonality for the positive unit bubble on an exact finite grid -/
namespace RKCert.ReviewedNative.UnitBubbleMoments

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns

noncomputable section

abbrev bubble (K : Type*) [Field K] : K[X] := X*(1-X)

def OrthogonalThrough {K : Type*} [Field K] [CharZero K] (J : K[X]) (d : ℕ) : Prop :=
  ∀ H : K[X], H.natDegree≤d → integral 0 1 (bubble K*J*H)=0

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reflect_as_neg : (1-X : K[X]) = -(X-C (1:K)) := by
  rw [map_one]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reflect_degree : (1-X : K[X]).natDegree=1 := by
  rw [reflect_as_neg,natDegree_neg,natDegree_X_sub_C]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reflect_leading : (1-X : K[X]).leadingCoeff=-1 := by
  rw [reflect_as_neg,leadingCoeff_neg,leadingCoeff_X_sub_C]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reflect_twice (S : K[X]) : (S.comp (1-X)).comp (1-X)=S := by
  rw [comp_assoc,show ((1-X : K[X]).comp (1-X))=X by
    simp only [sub_comp,one_comp,X_comp,sub_sub_cancel],comp_X]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem bubble_nonzero : bubble K≠0 := by
  apply mul_ne_zero X_ne_zero
  rw [reflect_as_neg,ne_eq,neg_eq_zero]
  exact (monic_X_sub_C (1:K)).ne_zero

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem bubble_degree : (bubble K).natDegree≤2 :=
  natDegree_mul_le_of_le natDegree_X.le (reflect_degree (K:=K)).le

private theorem bubble_pos {x : K} (hx : x∈Set.Ioo (0:K) 1) :
    0 < (bubble K).eval x := by
  simpa only [bubble,eval_mul,eval_sub,eval_one,eval_X] using
    mul_pos hx.1 (sub_pos.mpr hx.2)

private theorem integral_pos_of_nonnegative {l r : K} {G : K[X]}
    (lr : l<r) (gn : G≠0) (gd : G.natDegree<19)
    (gs : ∀ x∈Set.Ioo l r, 0≤G.eval x) :
    0 < integral l r G := by
  obtain ⟨i,hi⟩ := exists_nonzero_grid_sample lr gn gd
  exact integral_pos_of_grid_samples lr gd.le (fun j => gs _ (intervalPoint_mem lr j))
    ⟨i,lt_of_le_of_ne (gs _ (intervalPoint_mem lr i)) hi.symm⟩

private theorem square_pos {S : K[X]} {d : ℕ}
    (sn : S≠0) (sd : S.natDegree≤d) (pay : 2*d+2<19) :
    0 < integral 0 1 (bubble K*S^2) := by
  refine integral_pos_of_nonnegative zero_lt_one
    (mul_ne_zero (bubble_nonzero (K:=K)) (pow_ne_zero 2 sn)) ?_ ?_
  · exact (natDegree_mul_le_of_le (bubble_degree (K:=K))
      (natDegree_pow_le_of_le 2 sd)).trans_lt (by omega)
  · intro x hx
    simpa only [eval_mul,eval_pow] using
      mul_nonneg (bubble_pos hx).le (sq_nonneg (S.eval x))

/-- A polynomial orthogonal through its own degree vanishes. -/
theorem zero_of_orthogonalThrough {J : K[X]} {d : ℕ}
    (orth : OrthogonalThrough J d) (jd : J.natDegree≤d) (pay : 2*d+2<19) :
    J=0 := by
  by_contra jn
  have z : integral 0 1 (bubble K*J^2)=0 := by
    simpa only [pow_two,mul_assoc] using orth J jd
  exact (square_pos jn jd pay).ne' z

theorem degree_eq_succ {J : K[X]} {d : ℕ}
    (jn : J≠0) (jd : J.natDegree≤d+1) (orth : OrthogonalThrough J d)
    (pay : 2*d+2<19) : J.natDegree=d+1 := by
  by_contra ne
  exact jn (zero_of_orthogonalThrough orth (by omega) pay)

/-- A displayed linear factor must be strictly interior and simple. -/
theorem quotient_interior_simple {J U : K[X]} {r : K} {d : ℕ}
    (jn : J≠0) (jd : J.natDegree=d+1) (orth : OrthogonalThrough J d)
    (pay : 2*d+3<19) (eq : J=(X-C r)*U) :
    r∈Set.Ioo (0:K) 1 ∧ U.eval r≠0 := by
  have un : U≠0 := fun e => jn (by rw [eq,e,mul_zero])
  have ud : U.natDegree≤d := by
    rw [eq,natDegree_mul (monic_X_sub_C r).ne_zero un,natDegree_X_sub_C] at jd
    omega
  let G : K[X] := bubble K*(X-C r)*U^2
  have gz : integral 0 1 G=0 := by
    simpa only [G,eq,pow_two,mul_assoc] using orth U ud
  have gn : G≠0 := mul_ne_zero (mul_ne_zero (bubble_nonzero (K:=K)) (monic_X_sub_C r).ne_zero)
    (pow_ne_zero 2 un)
  have gd : G.natDegree<19 := by
    exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le (bubble_degree (K:=K))
      (natDegree_X_sub_C r).le) (natDegree_pow_le_of_le 2 ud)).trans_lt (by omega)
  have r0 : 0<r := by
    by_contra bad
    have pz : 0 < integral 0 1 G := by
      refine integral_pos_of_nonnegative zero_lt_one gn gd ?_
      intro x hx
      have hxr : 0≤x-r := sub_nonneg.mpr ((le_of_not_gt bad).trans hx.1.le)
      simpa only [G,eval_mul,eval_sub,eval_X,eval_C,eval_pow] using
        mul_nonneg (mul_nonneg (bubble_pos hx).le hxr) (sq_nonneg (U.eval x))
    exact pz.ne' gz
  have r1 : r<1 := by
    by_contra bad
    have pz : 0 < integral 0 1 (-G) := by
      refine integral_pos_of_nonnegative zero_lt_one (neg_ne_zero.mpr gn) ?_ ?_
      · simpa only [natDegree_neg] using gd
      · intro x hx
        have hxr : x-r≤0 := sub_nonpos.mpr (hx.2.le.trans (le_of_not_gt bad))
        have p : G.eval x≤0 := by
          simpa only [G,eval_mul,eval_sub,eval_X,eval_C,eval_pow] using
            mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (bubble_pos hx).le hxr)
              (sq_nonneg (U.eval x))
        simpa only [eval_neg] using neg_nonneg.mpr p
    have nz : integral 0 1 (-G)=0 := by rw [map_neg,gz,neg_zero]
    exact pz.ne' nz
  refine ⟨⟨r0,r1⟩,?_⟩
  intro hu
  obtain ⟨V,ve⟩ := dvd_iff_isRoot.mpr (show U.IsRoot r from hu)
  have vn : V≠0 := fun e => un (by rw [ve,e,mul_zero])
  have vd : V.natDegree≤d := by
    rw [ve,natDegree_mul (monic_X_sub_C r).ne_zero vn,natDegree_X_sub_C] at ud
    omega
  have e : bubble K*J*V=bubble K*U^2 := by
    simp only [eq,ve]
    ring
  have z := orth V vd
  rw [e] at z
  exact (square_pos un ud (by omega)).ne' z

/-- Symmetry of the positive weight forces the leading-sign reflection.
The proof uses only uniqueness from the exact weighted squares. -/
theorem signed_reflection {J : K[X]} {d : ℕ}
    (jn : J≠0) (jd : J.natDegree=d+1) (orth : OrthogonalThrough J d)
    (pay : 2*d+2<19) :
    J.comp (1-X)=C ((-1:K)^(d+1))*J := by
  let c : K := (-1)^(d+1)
  let T := C c*(J.comp (1-X))
  have cn : c≠0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have c2 : c*c=1 := by
    dsimp only [c]
    rw [←mul_pow]
    simp
  have td : T.natDegree=d+1 := by
    simp only [T,natDegree_C_mul cn,natDegree_comp,reflect_degree,mul_one,jd]
  have tn : T≠0 := by
    intro e
    rw [e,natDegree_zero] at td
    omega
  have tl : T.leadingCoeff=J.leadingCoeff := by
    have ld : (1-X : K[X]).natDegree≠0 := by rw [reflect_degree]; decide
    simp only [T,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_comp ld,reflect_leading,jd]
    change c*(J.leadingCoeff*c)=J.leadingCoeff
    calc
      _ = J.leadingCoeff*(c*c) := by ring
      _ = _ := by rw [c2,mul_one]
  have tOrth : OrthogonalThrough T d := by
    intro H hd
    have hrd : (H.comp (1-X)).natDegree≤d := by
      simpa only [natDegree_comp,reflect_degree,mul_one] using hd
    have e : (bubble K*J*(H.comp (1-X))).comp (1-X)=
        bubble K*(J.comp (1-X))*H := by
      simp only [bubble,mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel,reflect_twice]
      ring
    have h := integral_reflect (bubble K*J*(H.comp (1-X))) (0:K)
    rw [sub_zero,e,orth _ hrd] at h
    have eq : bubble K*T*H=c • (bubble K*(J.comp (1-X))*H) := by
      simp only [T,smul_eq_C_mul]
      ring
    rw [eq,map_smul,h,smul_zero]
  let D := J-T
  have dOrth : OrthogonalThrough D d := by
    intro H hd
    have e : bubble K*D*H=bubble K*J*H-bubble K*T*H := by dsimp only [D]; ring
    rw [e,map_sub,orth H hd,tOrth H hd,sub_zero]
  have dd : D.natDegree≤d := by
    by_cases dn : D=0
    · simp [dn]
    · have de : J.degree=T.degree := by rw [degree_eq_natDegree jn,degree_eq_natDegree tn,jd,td]
      have dl : D.degree<J.degree := degree_sub_lt_left de jn tl.symm
      rw [degree_eq_natDegree jn,jd] at dl
      exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt dn).mpr dl)
  have eq : J=T := sub_eq_zero.mp (zero_of_orthogonalThrough dOrth dd pay)
  have e := congrArg (fun F : K[X] => C c*F) eq
  simpa only [T,←mul_assoc,←map_mul,c2,map_one,one_mul] using e.symm

end
end RKCert.ReviewedNative.UnitBubbleMoments

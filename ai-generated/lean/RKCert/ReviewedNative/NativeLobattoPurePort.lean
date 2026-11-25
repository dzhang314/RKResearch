module

public import RKCert.ReviewedNative.NativeLobatto181
public import RKCert.ReviewedNative.GradedPrimitives

import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The genuine early Lobatto pure one-port

Use the literal X times the unnormalized integral Lobatto quintic.
Renormalizing the amplitude to monic and scaling clocks do not change
whether the primitive vanishes. The factor and target root are mapped
together to the finite complementary-factor certificate. The mapped
vanishing argument, residue gate, and original scaling have separate typed
interfaces. -/

namespace RKResearch.Certified.Graded.NativeLobatto

open Polynomial NativeModularRootLift
open scoped BigOperators

noncomputable section

def lobattoQuinticCoeffs : Fin 6 → ℤ := ![-1,20,-120,300,-330,132]

def lobattoQuintic : ℤ[X] := ofFn 6 lobattoQuinticCoeffs

def lobattoMesh : ℤ[X] := X * lobattoQuintic

private theorem quinticCoeff5 : lobattoQuintic.coeff 5 = 132 := by
  rw [lobattoQuintic, ofFn_coeff_eq_val_of_lt lobattoQuinticCoeffs (by decide : 5<6)]
  decide

private theorem quinticDegree : lobattoQuintic.natDegree = 5 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) lobattoQuinticCoeffs))
    (by rw [quinticCoeff5]; decide)

private theorem quinticLead : lobattoQuintic.leadingCoeff=132 := by
  rw [←coeff_natDegree,quinticDegree,quinticCoeff5]

theorem eval_map_lobattoQuintic {R : Type*} [CommRing R] (q : ℤ →+* R) (t : R) :
    (lobattoQuintic.map q).eval t = lobattoValue t := by
  simp only [lobattoQuintic,ofFn_eq_sum_monomial,Fin.sum_univ_succ]
  simp [lobattoQuinticCoeffs,lobattoValue]
  <;> ring

private theorem scale_integral_quintic :
    lobattoQuintic.scaleRoots 132 = C 132 * scaledLobatto := by
  ext i
  rw [coeff_scaleRoots,quinticDegree,coeff_C_mul]
  by_cases hi : i < 6
  · rw [lobattoQuintic,scaledLobatto,
      ofFn_coeff_eq_val_of_lt lobattoQuinticCoeffs hi,
      ofFn_coeff_eq_val_of_lt scaledCoefficients hi]
    have e (j : Fin 6) :
        lobattoQuinticCoeffs j * (132:ℤ)^(5-j.val)=132*scaledCoefficients j := by
      fin_cases j <;> decide
    exact e ⟨i,hi⟩
  · rw [lobattoQuintic,scaledLobatto,
      ofFn_coeff_eq_zero_of_ge lobattoQuinticCoeffs (by omega),
      ofFn_coeff_eq_zero_of_ge scaledCoefficients (by omega),zero_mul,mul_zero]

variable {K : Type*} [Field K] [CharZero K]

private theorem scale_mapped_mesh :
    (lobattoMesh.map (algebraMap ℤ K)).scaleRoots 132 =
      C (132:K) * scaledLobattoWithOrigin.map (algebraMap ℤ K) := by
  let f := algebraMap ℤ K
  have fc : f lobattoQuintic.leadingCoeff≠0 := by
    rw [quinticLead, map_ofNat]
    norm_num
  have e : (lobattoQuintic.map f).scaleRoots 132 = C (132:K)*scaledLobatto.map f := by
    have h := map_scaleRoots lobattoQuintic 132 f fc
    rw [scale_integral_quintic,Polynomial.map_mul,Polynomial.map_C,map_ofNat] at h
    simpa only [map_ofNat] using h.symm
  have xsc : (X:K[X]).scaleRoots 132 = X := by
    simpa using X_sub_C_scaleRoots (0:K) 132
  change (lobattoMesh.map f).scaleRoots 132 = C (132:K) * (scaledLobattoWithOrigin.map f)
  rw [lobattoMesh, Polynomial.map_mul, Polynomial.map_X, mul_scaleRoots_of_noZeroDivisors,
    xsc, e, scaledLobattoWithOrigin, Polynomial.map_mul, Polynomial.map_X]
  ring

private theorem weighted_primitive_sum_six (P : K[X]) (pd : P.natDegree≤5) (t : K) :
    (primitive (X*P)).eval t =
      ∑ i : Fin 6, (P.coeff i.val/((i.val+2:ℕ):K))*t^(i.val+2) := by
  classical
  let a : Fin 6 → K := toFn 6 P
  have ret : ofFn 6 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le pd)
  have e : (X:K[X])*P = X^1 * ofFn 6 a := by rw [ret,pow_one]
  rw [e,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [X_pow_mul_monomial,primitive_monomial,eval_monomial]
  have eq : a i = P.coeff i.val := rfl
  rw [eq]

theorem clearedLobattoFirst_eq_primitive (P : K[X]) (pd : P.natDegree≤5) (t : K) :
    clearedLobattoFirst P t = 420*(primitive (X*P)).eval t := by
  rw [weighted_primitive_sum_six P pd t, clearedLobattoFirst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have n0 : ((i.val+2:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have e : (firstPrimitiveRates i:K)*((i.val+2:ℕ):K)=420 := by
    have h := congrArg (fun n : ℕ => (n:K)) (firstPrimitiveRates_clear i)
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
  have rate : (420:K)/((i.val+2:ℕ):K) = (firstPrimitiveRates i:K) :=
    (div_eq_iff n0).mpr e.symm
  rw [←rate]
  ring

theorem clearedLobattoFirst_scaleRoots (P : K[X]) (l t : K) :
    clearedLobattoFirst (P.scaleRoots l) (l*t) =
      l^(P.natDegree+2)*clearedLobattoFirst P t := by
  unfold clearedLobattoFirst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val≤P.natDegree
  · rw [coeff_scaleRoots,mul_pow]
    calc
      _ = (l^(P.natDegree-i.val)*l^(i.val+2))*
          ((firstPrimitiveRates i:K)*P.coeff i.val*t^(i.val+2)) := by ring
      _ = _ := by rw [←pow_add,show P.natDegree-i.val+(i.val+2)=P.natDegree+2 by omega]
  · rw [coeff_scaleRoots,coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
    simp

-- The only potential coefficient transport is through the one integral
-- factor U. Treat both ring maps as opaque parameters: an equality in the
-- injected field comes back to U, then goes forward in the residue field.
private theorem cleared_zero_transport
    {R E F : Type*} [CommRing R] [CommRing E] [CommRing F]
    (e : R →+* E) (ei : Function.Injective e) (q : R →+* F)
    (U : R[X]) (a : R)
    (h : clearedLobattoFirst (U.map e) (e a) = 0) :
    clearedLobattoFirst (U.map q) (q a) = 0 := by
  have zeroSource : clearedLobattoFirst U a = 0 := ei
    (((map_clearedLobattoFirst e U a).trans h).trans (map_zero e).symm)
  exact (map_clearedLobattoFirst q U a).symm.trans
    ((congrArg q zeroSource).trans (map_zero q))

private theorem scaled_mesh_zero_isRoot :
    (scaledLobattoWithOrigin.map (algebraMap ℤ K)).IsRoot 0 := by
  change (scaledLobattoWithOrigin.map (algebraMap ℤ K)).eval 0 = 0
  rw [scaledLobattoWithOrigin, Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X,
    zero_mul]

private theorem scaled_mesh_degree :
    (scaledLobattoWithOrigin.map (algebraMap ℤ K)).natDegree = 6 :=
  (scaledLobattoWithOrigin_monic.natDegree_map (algebraMap ℤ K)).trans
    scaledLobattoWithOrigin_degree

-- No root replacement, polynomial rewrite, or coefficient computation
-- is required in the reduction eliminator's callback itself.
private theorem reduced_marked_factor_absurd {k : Type*} [Field k] [CharP k 181]
    (q : integralClosure ℤ K →+* k) (a o : integralClosure ℤ K)
    (U : (integralClosure ℤ K)[X]) (o0 : (o : K) = 0) (sep : q a ≠ q o)
    (aroot : (scaledLobattoWithOrigin.map (Int.castRingHom k)).IsRoot (q a))
    (um : U.Monic)
    (divisor : (X-C (q a)) * U.map q ∣ scaledLobattoWithOrigin.map (Int.castRingHom k))
    (notRoot : ¬ (U.map q).IsRoot (q a))
    (zero : clearedLobattoFirst (U.map (algebraMap (integralClosure ℤ K) K)) (a : K) = 0) :
    False := by
  have oZ : o = 0 := Subtype.ext o0
  have oImage : q o = 0 := (congrArg q oZ).trans (map_zero q)
  have q0 : q a ≠ 0 := fun h => sep (h.trans oImage.symm)
  have dv : U.map q ∣ scaledLobattoWithOrigin.map (Int.castRingHom k) :=
    (dvd_mul_left (U.map q) (X-C (q a))).trans divisor
  have bad : clearedLobattoFirst (U.map q) (q a) = 0 :=
    cleared_zero_transport (algebraMap (integralClosure ℤ K) K)
      (fun _ _ h=>Subtype.ext h) q U a zero
  exact clearedLobattoFirst_ne_zero_at_residue_factor
    (U.map q) (um.map q) dv (q a) q0 aroot notRoot bad

private theorem cleared_nonzero_of_scaled_monic_divisor
    (B : K[X]) (bm : B.Monic) (t : K) (tn : t ≠ 0)
    (dv : (X-C t) * B ∣ scaledLobattoWithOrigin.map (algebraMap ℤ K)) :
    clearedLobattoFirst B t ≠ 0 := by
  intro zero
  have rt : (scaledLobattoWithOrigin.map (algebraMap ℤ K)).IsRoot t :=
    dvd_iff_isRoot.mp ((dvd_mul_right (X-C t) B).trans dv)
  refine with_reduced_monic_factor_at_distinct_root 181 prime181
    scaledLobattoWithOrigin_monic scaledLobatto_mod181_separable rt
    (scaled_mesh_zero_isRoot (K:=K)) tn bm dv ?_
  intro k _ _ q a o U atA atO sep aroot uMap um divisor notRoot
  have liftedZero :
      clearedLobattoFirst (U.map (algebraMap (integralClosure ℤ K) K)) (a : K) = 0 := by
    rw [uMap, atA]
    exact zero
  exact reduced_marked_factor_absurd q a o U atO sep aroot um divisor notRoot liftedZero

private theorem scaled_lobatto_divisor (U : K[X]) (t : K)
    (du : (X-C t)*U ∣ lobattoMesh.map (algebraMap ℤ K)) :
    (X-C ((132:K)*t))*U.scaleRoots 132 ∣
      scaledLobattoWithOrigin.map (algebraMap ℤ K) := by
  have both := scaleRoots_dvd (((X:K[X])-C t)*U) (lobattoMesh.map (algebraMap ℤ K))
    (r:=(132:K)) du
  rw [mul_scaleRoots_of_noZeroDivisors, X_sub_C_scaleRoots, scale_mapped_mesh,
    mul_comm t (132:K)] at both
  have u : IsUnit (C (132:K)) := isUnit_C.mpr ((by norm_num : (132:K)≠0).isUnit)
  exact u.dvd_mul_left.mp both

private theorem monic_factor_degree_cap (U : K[X]) (um : U.Monic) (t : K)
    (dvd : (X-C t)*U.scaleRoots 132 ∣
      scaledLobattoWithOrigin.map (algebraMap ℤ K)) :
    U.natDegree ≤ 5 := by
  have Bm : (U.scaleRoots (132:K)).Monic := (monic_scaleRoots_iff _).mpr um
  have d := natDegree_le_of_dvd dvd (scaledLobattoWithOrigin_monic.map (algebraMap ℤ K)).ne_zero
  rw [natDegree_mul (X_sub_C_ne_zero t) Bm.ne_zero, natDegree_X_sub_C,
    natDegree_scaleRoots, scaled_mesh_degree] at d
  omega

private theorem primitive_X_ne_zero_of_monic_lobatto_divisor
    (U : K[X]) (um : U.Monic) (t : K) (tn : t≠0)
    (du : (X-C t)*U ∣ lobattoMesh.map (algebraMap ℤ K)) :
    (primitive (X*U)).eval t ≠ 0 := by
  intro zero
  have dv := scaled_lobatto_divisor U t du
  have bm : (U.scaleRoots (132:K)).Monic := (monic_scaleRoots_iff _).mpr um
  have deg : U.natDegree ≤ 5 := monic_factor_degree_cap U um ((132:K)*t) dv
  have tn' : (132:K)*t ≠ 0 := mul_ne_zero (by norm_num) tn
  apply cleared_nonzero_of_scaled_monic_divisor (U.scaleRoots 132) bm ((132:K)*t) tn' dv
  rw [clearedLobattoFirst_scaleRoots, clearedLobattoFirst_eq_primitive U deg t, zero,
    mul_zero, mul_zero]

private theorem original_mesh_map_ne_zero :
    lobattoMesh.map (algebraMap ℤ K) ≠ 0 := by
  have hl : lobattoQuintic.leadingCoeff ≠ 0 := by rw [quinticLead]; decide
  have p : lobattoQuintic ≠ 0 := leadingCoeff_ne_zero.mp hl
  have hi : Function.Injective (algebraMap ℤ K) := Int.cast_injective
  rw [lobattoMesh, Polynomial.map_mul, Polynomial.map_X]
  exact mul_ne_zero X_ne_zero
    ((Polynomial.map_ne_zero_iff hi).mpr p)

private theorem primitive_X_mul_C_zero (R : K[X]) (c t : K)
    (zero : (primitive (X*R)).eval t = 0) :
    (primitive (X*(R*C c))).eval t = 0 := by
  have rep : (X:K[X])*(R*C c) = c • (X*R) := by
    rw [smul_eq_C_mul]
    ring
  rw [rep, map_smul, eval_smul, zero, smul_zero]

/-- Literal one-port gate. The dividend witnessing the other factor
must pay the selected linear root; the factor itself need not be monic. -/
theorem primitive_X_ne_zero_of_lobatto_divisor (R : K[X]) (t : K) (tn : t≠0)
    (fac : (X-C t)*R ∣ lobattoMesh.map (algebraMap ℤ K)) :
    (primitive (X*R)).eval t≠0 := by
  intro zero
  have rn : R ≠ 0 := by
    intro rz
    rw [rz, mul_zero, zero_dvd_iff] at fac
    exact original_mesh_map_ne_zero (K:=K) fac
  let c : K := R.leadingCoeff⁻¹
  have c0 : c ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr rn)
  have u : IsUnit (C c) := isUnit_C.mpr c0.isUnit
  have d : (X-C t)*(R*C c) ∣ lobattoMesh.map (algebraMap ℤ K) := by
    rw [← mul_assoc, u.mul_right_dvd]
    exact fac
  have m : (R*C c).Monic := monic_mul_leadingCoeff_inv rn
  exact primitive_X_ne_zero_of_monic_lobatto_divisor (R*C c) m t tn d
    (primitive_X_mul_C_zero R c t zero)

/-- Version with the literal pure factor equation and the distinct
nonzero pivot supplied as a root of the complementary factor. -/
theorem primitive_X_ne_zero_of_lobatto_factor
    (R Q : K[X]) (g : K) (gn : g≠0)
    (shape : R*Q=C g * lobattoMesh.map (algebraMap ℤ K))
    (t : K) (tn : t≠0) (pivot : Q.IsRoot t) :
    (primitive (X*R)).eval t≠0 := by
  obtain ⟨S,e⟩ := (dvd_iff_isRoot (a:=t)).mpr pivot
  have d : (X-C t)*R ∣ C g*lobattoMesh.map (algebraMap ℤ K) := by
    refine ⟨S,?_⟩
    rw [←shape,e]
    ring
  have u : IsUnit (C g) := isUnit_C.mpr gn.isUnit
  exact primitive_X_ne_zero_of_lobatto_divisor R t tn (u.dvd_mul_left.mp d)

end
end RKResearch.Certified.Graded.NativeLobatto

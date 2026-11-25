module

public import RKCert.ReviewedNative.NativeReciprocalPrimitive

import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Multiset.Replicate
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A single residue root for a cleared first primitive

There is one reduction homomorphism, from the integral closure into a
chosen field above 11. The only shape needed of the integral scaled
reciprocal is X^7(X+3) modulo 11. No roots are numerically compared or
compared across conjugate places.
-/
namespace RKResearch.Certified.Graded.NativeReciprocal

open Polynomial
open scoped BigOperators

noncomputable section

private theorem eleven_not_unit (E : Type*) [Field E] [CharZero E] :
    ¬IsUnit (11:integralClosure ℤ E) := by
  intro unit
  let B := integralClosure ℤ E
  obtain ⟨z,hz⟩ := isUnit_iff_exists_inv.mp unit
  have ez : (11:E)*(z:E)=1 := by
    have h := congrArg (algebraMap B E) hz
    simpa only [map_mul,map_ofNat,map_one,Subalgebra.algebraMap_apply] using h
  have zn : (11:E)≠0 := by norm_num
  have asRat : (z:E)∈Set.range (Rat.cast : ℚ → E) := by
    refine ⟨(11:ℚ)⁻¹,?_⟩
    have eq : (((11:ℚ)⁻¹ : ℚ):E)=(11:E)⁻¹ := by
      rw [Rat.cast_inv, Rat.cast_ofNat]
    rw [eq]
    apply mul_left_cancel₀ zn
    rw [mul_inv_cancel₀ zn,ez]
  have iz : IsIntegral ℤ (z:E) := z.2
  obtain ⟨n,hn⟩ := iz.mem_range_ratCast_iff.mp asRat
  have int : (11:ℤ)*n=1 := by
    apply (Int.cast_injective : Function.Injective (fun i : ℤ => (i:E)))
    simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_one]
    rw [hn]
    exact ez
  exact (by decide : ¬(11:ℤ)∣1) ⟨n,int.symm⟩

private theorem monic_factor_of_X_pow {k : Type*} [Field k] {P : k[X]}
    (m : P.Monic) {d n : ℕ} (degree : P.natDegree=d) (dvd : P ∣ (X:k[X])^n) :
    P=X^d := by
  classical
  have split := (Splits.X_pow (R:=k) n).of_dvd (pow_ne_zero _ X_ne_zero) dvd
  have all (x : k) (hx : x∈P.roots) : x=0 := by
    have e := ((mem_roots m.ne_zero).mp hx).dvd dvd
    exact eq_zero_of_pow_eq_zero (by simpa only [IsRoot,eval_pow,eval_X] using e)
  have c : P.roots.card=d := split.natDegree_eq_card_roots.symm.trans degree
  have rs : P.roots=Multiset.replicate d 0 := by
    simpa only [c] using (Multiset.eq_replicate_of_mem all)
  rw [split.eq_prod_roots_of_monic m,rs,Multiset.map_replicate,Multiset.prod_replicate]
  simp

/-- A selected root of an integral scaled reciprocal discharges the
literal first primitive for every five-degree quotient of H whose
complementary factor vanishes at that selected clock. -/
theorem chosen_root_cut_of_integral_reciprocal {E : Type*} [Field E] [CharZero E]
    (H : E[X]) (h0 : H.coeff 0≠0) (F : ℤ[X]) (fm : F.Monic)
    (corr : F.map (algebraMap ℤ E)=scaledReciprocal H 9)
    (splitF : (F.map (algebraMap ℤ E)).Splits)
    (reduced : F.map (Int.castRingHom (ZMod 11)) =
      ((X:(ZMod 11)[X])^7)*(X+C 3)) :
    ∃ v : E, H.IsRoot v ∧
      ∀ Q N : E[X], Q.natDegree=5 → Q*N=H → N.IsRoot v →
        (primitive (X*Q)).eval v≠0 := by
  classical
  let B := integralClosure ℤ E
  let I : Ideal B := Ideal.span {(11:B)}
  have proper : I≠⊤ := fun top => eleven_not_unit E (Ideal.span_singleton_eq_top.mp top)
  obtain ⟨m,IsMax,inc⟩ := Ideal.exists_le_maximal I proper
  letI : m.IsMaximal := IsMax
  let k := B ⧸ m
  letI : Field k := Ideal.Quotient.field m
  let q : B →+* k := Ideal.Quotient.mk m
  have eq11 : (11:k)=0 := by
    have mem : (11:B)∈m := inc (Ideal.subset_span (by simp [I]))
    have h : q (11:B)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr mem
    simpa only [map_ofNat] using h
  letI : CharP k 11 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 11)).mpr eq11
  have three : (3:k)≠0 := fun h =>
    (by decide : ¬ (11:ℕ)∣3) ((CharP.cast_eq_zero_iff k 11 3).mp h)
  have rate : (210:k)≠0 := fun h =>
    (by decide : ¬ (11:ℕ)∣210) ((CharP.cast_eq_zero_iff k 11 210).mp h)
  let bE : B →+* E := algebraMap B E
  have inj : Function.Injective bE := fun _ _ h => Subtype.ext h
  let FB := F.map (algebraMap ℤ B)
  have fBM : FB.Monic := fm.map _
  have fMap : FB.map bE=F.map (algebraMap ℤ E) := by
    dsimp only [FB,bE]
    rw [map_map,←IsScalarTower.algebraMap_eq ℤ B E]
  have red : FB.map q=(X:k[X])^7*(X+C 3) := by
    let z := ZMod.castHom (dvd_refl (11:ℕ)) k
    have h : q.comp (algebraMap ℤ B)=z.comp (Int.castRingHom (ZMod 11)) :=
      RingHom.ext_int _ _
    dsimp only [FB]
    rw [map_map,h,←map_map,reduced]
    have h3 : z (3 : ZMod 11) = (3:k) := map_ofNat z 3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_add, Polynomial.map_C, h3]
  have splitB : FB.Splits := by
    refine Splits.of_splits_map_of_injective inj (fMap.symm ▸ splitF) ?_
    intro a ha
    rw [fMap] at ha
    have ev := (mem_roots (fm.map (algebraMap ℤ E)).ne_zero).mp ha
    have aint : IsIntegral ℤ a := ⟨F,fm,by
      change aeval a F = 0
      rw [←eval_map_algebraMap F a]
      exact ev⟩
    exact ⟨⟨a,aint⟩,rfl⟩
  have rb : (-3:k) ∈ (FB.map q).roots :=
    (mem_roots (fBM.map q).ne_zero).mpr (by rw [red]; simp [IsRoot])
  rw [splitB.roots_map_of_ne_zero (fBM.map q).ne_zero] at rb
  obtain ⟨t,ht,redt⟩ := Multiset.mem_map.mp rb
  have qtn : q t≠0 := by rw [redt]; exact neg_ne_zero.mpr three
  have t0 : bE t≠0 := by
    intro h
    have tb : t=0 := inj (by simpa only [map_zero] using h)
    exact qtn (by rw [tb,map_zero])
  have tE : (F.map (algebraMap ℤ E)).IsRoot (bE t) := by
    have root := (mem_roots fBM.ne_zero).mp ht
    rw [←fMap,IsRoot,eval_map_apply,root.eq_zero,map_zero]
  have a0 : (9:E)≠0 := by norm_num
  let v := (9:E)/bE t
  have vr : H.IsRoot v := (scaledReciprocal_isRoot_iff h0 a0 t0).mp (corr ▸ tE)
  refine ⟨v,vr,?_⟩
  intro Q N qd product nroot zero
  have no : Q.coeff 0*N.coeff 0≠0 := by
    have ce : (Q*N).coeff 0 = Q.coeff 0*N.coeff 0 := by
      simp only [coeff_zero_eq_eval_zero, eval_mul]
    rw [←ce,product]
    exact h0
  have q0 : Q.coeff 0≠0 := fun h => no (by rw [h,zero_mul])
  have n0 : N.coeff 0≠0 := fun h => no (by rw [h,mul_zero])
  let J := scaledReciprocal Q 9
  let U := scaledReciprocal N 9
  have jM : J.Monic := scaledReciprocal_monic q0 9
  have uM : U.Monic := scaledReciprocal_monic n0 9
  have prodE : J*U=F.map (algebraMap ℤ E) := by
    change scaledReciprocal Q 9*scaledReciprocal N 9=_
    rw [←scaledReciprocal_mul,product,←corr]
  have jLift : J∈Polynomial.lifts bE :=
    integralClosure.mem_lifts_of_monic_of_dvd_map E fm jM ⟨U,prodE.symm⟩
  have uLift : U∈Polynomial.lifts bE :=
    integralClosure.mem_lifts_of_monic_of_dvd_map E fm uM
      ⟨J,prodE.symm.trans (mul_comm J U)⟩
  obtain ⟨JB,jMap⟩ := (Polynomial.mem_lifts (f:=bE) J).mp jLift
  obtain ⟨UB,uMap⟩ := (Polynomial.mem_lifts (f:=bE) U).mp uLift
  have jbM : JB.Monic := inj.monic_map_iff.mpr (jMap.symm ▸ jM)
  have prodB : JB*UB=FB := by
    apply Polynomial.map_injective bE inj
    rw [Polynomial.map_mul,jMap,uMap,fMap,prodE]
  have prodR : JB.map q*UB.map q=(X:k[X])^7*(X+C 3) := by
    rw [←Polynomial.map_mul,prodB,red]
  have uRoot : U.IsRoot (bE t) :=
    (scaledReciprocal_isRoot_iff n0 a0 t0).mpr nroot
  have ubRoot : UB.IsRoot t := by
    change UB.eval t=0
    apply inj
    rw [←eval_map_apply,uMap,uRoot.eq_zero,map_zero]
  have urRoot : (UB.map q).IsRoot (-3:k) := by
    rw [←redt,IsRoot,eval_map_apply,ubRoot.eq_zero,map_zero]
  let L : k[X] := X+C 3
  have dU : L∣UB.map q := by
    change (X+C (3:k))∣UB.map q
    rw [show (X+C (3:k))=X-C (-3:k) by simp]
    exact dvd_iff_isRoot.mpr urRoot
  obtain ⟨U₁,uFactor⟩ := dU
  have dJ : JB.map q∣(X:k[X])^7 := by
    refine ⟨U₁,?_⟩
    apply mul_right_cancel₀ (show L≠0 from (monic_X_add_C (3:k)).ne_zero)
    calc
      _=JB.map q*UB.map q := prodR.symm
      _=_ := by rw [uFactor]; ring
  have jd : JB.natDegree=5 := by
    rw [←natDegree_map_eq_of_injective inj JB,jMap]
    exact (scaledReciprocal_degree q0 9).trans qd
  have jRed : JB.map q=(X:k[X])^5 :=
    monic_factor_of_X_pow (jbM.map q) ((jbM.natDegree_map q).trans jd) dJ
  have paidB : clearedFirst JB t=0 := by
    apply inj
    rw [map_clearedFirst,map_zero,jMap]
    exact clearedFirst_of_primitive_zero qd q0 t0 zero
  have paidR : clearedFirst (JB.map q) (q t)=0 := by
    rw [←map_clearedFirst,paidB,map_zero]
  rw [jRed,clearedFirst_X_five] at paidR
  exact mul_ne_zero rate (pow_ne_zero 5 qtn) paidR

end
end RKResearch.Certified.Graded.NativeReciprocal

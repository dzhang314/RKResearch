module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRatioReceipts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Projective Vieta and both exterior branches of the rational weak-four cover

The only additional receipt per exterior window is a rational band for the
four bilinear Vieta corners. This same schema handles an exterior fitting
root, an exterior first stop, or an exterior root in neither role.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial Set Function
open RKCert.ReviewedNative.PolynomialBracket (ofCoeffs coeff_ofCoeffs)
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.OrderedRootGapSaturation (OrderedExtension)
open RKCert.ReviewedNative.PolynomialCertificate
open scoped BigOperators

universe u

def RationalStripFrame.nodeSum {n : ℕ} (A : RationalStripFrame n) : RatBand :=
  ⟨∑ i,A.lower i,∑ i,A.upper i⟩

def outerSign (high : Bool) (K : Type*) [Field K] : K := if high then 1 else -1

def projectiveValue {K : Type*} [Field K] (high : Bool) (A B D : K)
    (v : Fin 2 → K) : K :=
  outerSign high K*(-((1-v 0)*A+v 0*B)/D-v 0*v 1)

def rawVietaOK (high : Bool) (P T : List ℚ) {n : ℕ} (A : RationalStripFrame n)
    (den : ℕ) (W : RatBand) : Prop :=
  let V := A.parameterBand den
  let S := A.nodeSum
  ∀ addr : Fin 2 → Bool,
    let value := projectiveValue high (listCoeff P 7) (listCoeff T 7) (listCoeff T 8)
      (vertex ![V.lo,S.lo] ![V.hi,S.hi] addr)
    W.lo≤value ∧ value≤W.hi

def capOuterBand (high : Bool) (V W : RatBand) : RatBand :=
  ⟨max W.lo (if high then V.lo else 0),W.hi⟩

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem projectiveValue_affine (high : Bool) (A B D : K) :
    SeparatelyAffine (projectiveValue high A B D) := by
  intro x i a b t
  have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by
    rw [Fin.forall_fin_two]
    exact ⟨Or.inl rfl,Or.inr rfl⟩
  rcases hcases i with rfl | rfl
  · simp only [projectiveValue,Function.update_self,Function.update_of_ne
      (by decide : (1:Fin 2)≠0),mix,div_eq_mul_inv]
    ring
  · simp only [projectiveValue,Function.update_self,Function.update_of_ne
      (by decide : (0:Fin 2)≠1),mix,div_eq_mul_inv]
    ring

private theorem projectiveValue_cast (high : Bool) (A B D : ℚ) (v : Fin 2 → ℚ) :
    ((projectiveValue (K:=ℚ) high A B D v:ℚ):K) =
      projectiveValue high (A:K) (B:K) (D:K) (fun i => (v i:K)) := by
  cases high <;> simp [projectiveValue,outerSign,Rat.cast_sub,Rat.cast_neg,Rat.cast_div,
    Rat.cast_mul]

theorem RationalStripFrame.sum_mem {n : ℕ} (A : RationalStripFrame n) {r : Fin n → K}
    (h : A.nodes r) : A.nodeSum.Mem (∑ i,r i) := by
  have lo := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (h i).1)
  have hi := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (h i).2)
  change ((Rat.castHom K) (∑ i,A.lower i))≤∑ i,r i ∧
    (∑ i,r i)≤((Rat.castHom K) (∑ i,A.upper i))
  simp only [map_sum]
  exact ⟨lo,hi⟩

theorem RationalStripFrame.ordered_param_extension (E : OrderedExtension K)
    {n den : ℕ} {A : RationalStripFrame n} {v : K} (h : A.param den v) :
    (A.parameterBand den).Mem (E.embed v) := by
  have h₀ := E.mono.monotone h.1
  have h₁ := E.mono.monotone h.2
  change E.embed (gridCoord den A.span.1)≤E.embed v at h₀
  change E.embed v≤E.embed (gridCoord den A.span.2) at h₁
  change ((gridCoord (K:=ℚ) den A.span.1:ℚ):E.carrier)≤E.embed v ∧
    E.embed v≤((gridCoord (K:=ℚ) den A.span.2:ℚ):E.carrier)
  simpa only [gridCoord,map_div₀,map_natCast,Rat.cast_div,Rat.cast_natCast] using
    And.intro h₀ h₁

theorem projectiveValue_mem_of_rawVietaOK {high : Bool} {P T : List ℚ} {n den : ℕ}
    {A : RationalStripFrame n} {W : RatBand} (ok : rawVietaOK high P T A den W)
    {v s : K} (hv : (A.parameterBand den).Mem v) (hs : A.nodeSum.Mem s) :
    W.Mem (projectiveValue high (listCoeff P 7:K) (listCoeff T 7:K) (listCoeff T 8:K) ![v,s]) := by
  let L : Fin 2 → ℚ := ![(A.parameterBand den).lo,A.nodeSum.lo]
  let U : Fin 2 → ℚ := ![(A.parameterBand den).hi,A.nodeSum.hi]
  have mem (i : Fin 2) : (![v,s] : Fin 2 → K) i∈Icc (L i:K) (U i:K) := by
    fin_cases i
    · exact hv
    · exact hs
  apply value_in_Icc_of_vertices (projectiveValue_affine high _ _ _) mem
  intro c
  have e : vertex (fun j => (L j:K)) (fun j => (U j:K)) c =
        (fun i => ((vertex (K:=ℚ) L U c i:ℚ):K)) := by
    funext i
    cases b : c i <;> simp [vertex,b]
  rw [e,←projectiveValue_cast]
  have h := ok c
  exact Set.mem_Icc.mpr ⟨Rat.cast_le.mpr h.1,Rat.cast_le.mpr h.2⟩

theorem scoped_vieta_projective (E : OrderedExtension K) {P T : List ℚ} {v : K}
    (vn : 0≤v) (p8 : listCoeff P 8=0) (p7 : listCoeff P 7≠0) (t8 : listCoeff T 8≠0)
    (e s : E.carrier)
    (H : let F := (pencil ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) v).map E.embed
      F.coeff 7 = -(F.coeff 8)*(e+s)) :
    0<E.embed v ∧ E.embed v*e =
      -((1-E.embed v)*(listCoeff P 7:E.carrier)+E.embed v*(listCoeff T 7:E.carrier))/
        (listCoeff T 8:E.carrier)-E.embed v*s := by
  let w := E.embed v
  let F := (pencil ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) v).map E.embed
  have c (k : ℕ) : F.coeff k =
      (1-w)*(listCoeff P k:E.carrier)+w*(listCoeff T k:E.carrier) := by
    simp only [F,w,coeff_map,pencil_coeff,coeff_ofCoeffs,listCoeff,map_sub,map_one,map_add,map_mul,
      Rat.coe_castHom,map_ratCast]
  change F.coeff 7 = -(F.coeff 8)*(e+s) at H
  rw [c 7,c 8,p8,Rat.cast_zero,mul_zero,zero_add] at H
  have wn : 0≤w := by simpa only [map_zero] using E.mono.monotone vn
  have wp : 0<w := by
    apply lt_of_le_of_ne wn
    intro eq
    rw [←eq] at H
    simp only [sub_zero,one_mul,zero_mul,add_zero,neg_zero] at H
    exact (Rat.cast_ne_zero.mpr p7) H
  exact ⟨wp,mul_outer_of_vieta (Rat.cast_ne_zero.mpr t8) H⟩

theorem signed_projective_mem {P T : List ℚ} {high : Bool} {n den : ℕ}
    {A : RationalStripFrame n} {W : RatBand} (ok : rawVietaOK high P T A den W)
    {r : Fin n → K} (hr : A.nodes r) {v e : K} (vp : 0<v)
    (hv : (A.parameterBand den).Mem v)
    (side : if high then 1≤e else e≤0)
    (eq : v*e = -((1-v)*(listCoeff P 7:K)+v*(listCoeff T 7:K))/(listCoeff T 8:K)-
      v*(∑ i,r i)) :
    (capOuterBand high (A.parameterBand den) W).Mem (if high then v*e else -v*e) := by
  have eq₁ : projectiveValue high (listCoeff P 7:K) (listCoeff T 7:K) (listCoeff T 8:K) ![v,∑ i,r i] =
      (if high then v*e else -v*e) := by
    simp only [projectiveValue,Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [←eq]
    cases high <;> simp [outerSign]
  have h := projectiveValue_mem_of_rawVietaOK ok hv (A.sum_mem hr)
  rw [eq₁] at h
  have hb : ((if high then (A.parameterBand den).lo else 0:ℚ):K)≤
      (if high then v*e else -v*e) := by
    cases high
    · change ((0:ℚ):K)≤ -v*e
      rw [Rat.cast_zero]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr vp.le) side
    · change ((A.parameterBand den).lo:K)≤v*e
      exact hv.1.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left side vp.le)
  refine ⟨?_,h.2⟩
  change ((max W.lo (if high then (A.parameterBand den).lo else 0):ℚ):K)≤_
  rw [(Rat.cast_strictMono (K:=K)).monotone.map_max]
  exact max_le h.1 hb

end

def exteriorCoordOK (high : Bool) {den : ℕ}
    (p : FitClaim (Option (Fin 7)) 7 4) (W : RatBand) (i : Fin 4) : Prop :=
  let V := p.source.parameterBand den
  let U := capOuterBand high V W
  match p.rank.1,p.order i with
  | some j,some k => ordinaryCoordOK p.box i (p.source.band j) (p.source.band k)
  | some j,none =>
    if high then highFitCoordOK p.box i V (p.source.band j) U
    else lowCoordOK p.box i V (p.source.band j) U
  | none,some k => if high then highStopCoordOK p.box i V (p.source.band k) U else False
  | none,none => False

instance exteriorCoordOK_decidable (high : Bool) {den : ℕ}
    (p : FitClaim (Option (Fin 7)) 7 4) (W : RatBand) (i : Fin 4) :
    Decidable (exteriorCoordOK (den:=den) high p W i) := by
  cases a : p.rank.1 <;> cases b : p.order i <;> cases high <;>
    simp only [exteriorCoordOK,a,b,if_true,if_false,Bool.false_eq_true] <;> infer_instance

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem FitClaim.coordinates_of_exterior_receipt {P T : List ℚ} {high : Bool} {den : ℕ}
    (p : FitClaim (Option (Fin 7)) 7 4) (W : RatBand)
    (raw : rawVietaOK high P T p.source den W)
    (boxes : ∀ i, exteriorCoordOK (den:=den) high p W i)
    (p8 : listCoeff P 8=0) (p7 : listCoeff P 7≠0) (t8 : listCoeff T 8≠0)
    (E : OrderedExtension K) {v : K} (v₀ : 0≤v)
    (param : p.source.param den v) {r : Fin 7 → E.carrier} {e : E.carrier}
    (cage : p.source.nodes r) (side : if high then 1≤e else e≤0)
    (H : let F := (pencil ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) v).map E.embed
      F.coeff 7 = -(F.coeff 8)*(e+∑ i,r i))
    (stop : 0<withExtra r e p.rank.1) :
    p.Coordinates (withExtra r e) := by
  have hv := p.source.ordered_param_extension E param
  obtain ⟨vp,ve⟩ := scoped_vieta_projective E v₀ p8 p7 t8 e (∑ i,r i) H
  have hw := signed_projective_mem raw cage vp hv side ve
  have h (i : Fin 4) : RealizableCoord p.box i
      (withExtra r e p.rank.1) (withExtra r e (p.order i)) := by
    have b := boxes i
    cases hj : p.rank.1 with
    | none =>
      cases hi : p.order i with
      | none => simp [exteriorCoordOK,hj,hi] at b
      | some k =>
        cases high
        · simp [exteriorCoordOK,hj,hi] at b
        · simp only [exteriorCoordOK,hj,hi,if_true] at b
          change RealizableCoord p.box i e (r k)
          exact highStopCoord_realizable b vp side hv (cage k) hw
    | some j =>
      cases hi : p.order i with
      | none =>
        cases high
        · simp only [exteriorCoordOK,hj,hi,Bool.false_eq_true,if_false] at b
          change RealizableCoord p.box i (r j) e
          have sp : 0<r j := by simpa only [hj,withExtra_some] using stop
          exact lowCoord_realizable b vp sp side hv (cage j) hw
        · simp only [exteriorCoordOK,hj,hi,if_true] at b
          change RealizableCoord p.box i (r j) e
          exact highFitCoord_realizable b vp side hv (cage j) hw
      | some k =>
        simp only [exteriorCoordOK,hj,hi] at b
        change RealizableCoord p.box i (r j) (r k)
        have sp : 0<r j := by simpa only [hj,withExtra_some] using stop
        exact ordinaryCoord_realizable b (cage j) (cage k) sp
  choose x s hx using h
  exact ⟨x,s,fun i => (hx i).1,fun i => (hx i).2.1,fun i => (hx i).2.2⟩

end

end RKCert.ReviewedNative.WeakFourFirstOnly

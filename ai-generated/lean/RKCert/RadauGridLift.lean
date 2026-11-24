module

public import RKCert.FixedRootSeparation
public import RKCert.RadauArithmetic77569
public import RKCert.Dirk15RadauPorts
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-! # Sound lift from the fixed pairwise distinct Radau grid
The residue map is only on integral numerical roots of one fixed
polynomial, never on the surrounding RK coefficient field. -/
namespace RKCert.FixedPolynomial.Radau77569

open Polynomial
open scoped Classical
universe u

def coeffInt : Fin 8 → ℤ := ![64,-2016,20160,-92400,221760,-288288,192192,-51480]
def reproducerInt : ℤ[X] := ofFn 8 coeffInt
noncomputable def gridInt : ℤ[X] := X*reproducerInt
noncomputable def gridNormalized : ℤ[X] := gridInt.integralNormalization

theorem degree_reproducer : reproducerInt.natDegree=7 := by
  have hem := ofFn_natDegree_lt (by decide : 1≤8) coeffInt
  have hlc : reproducerInt.coeff 7 ≠0 := by
    change (ofFn 8 coeffInt).coeff 7≠0
    rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
    decide
  exact natDegree_eq_of_le_of_coeff_ne_zero (by change (ofFn 8 coeffInt).natDegree≤7; omega) hlc

theorem leading_reproducer : reproducerInt.leadingCoeff=(-51480:ℤ) := by
  rw [←coeff_natDegree,degree_reproducer]
  change (ofFn 8 coeffInt).coeff 7=_
  rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
  decide

theorem grid_ne : gridInt≠0 := by
  unfold gridInt
  apply mul_ne_zero X_ne_zero
  intro e
  have d := degree_reproducer
  rw [e,natDegree_zero] at d
  omega

theorem grid_degree : gridInt.natDegree=8 := by
  have hn : reproducerInt≠0 := by
    intro e
    have d := degree_reproducer
    rw [e,natDegree_zero] at d
    omega
  rw [gridInt,natDegree_mul X_ne_zero hn,natDegree_X,degree_reproducer]

theorem grid_leading : gridInt.leadingCoeff=(-51480:ℤ) := by
  rw [gridInt,leadingCoeff_mul,leadingCoeff_X,one_mul,leading_reproducer]

theorem eval_reproducer_mod (x : F) :
    reproducerInt.eval₂ (Int.castRingHom F) x=reproducer x := by
  unfold reproducerInt
  rw [ofFn_eq_sum_monomial,Polynomial.eval₂_finsetSum]
  simp [reproducer,coeffInt,Fin.sum_univ_succ,Polynomial.eval₂_monomial]
  abel

theorem map_reproducer {K : Type u} [Field K] :
    reproducerInt.map (Int.castRingHom K)=(RKCert.Paired.radauLeft7 : K[X]) := by
  ext j
  rw [coeff_map]
  by_cases h : j<8
  · change (Int.castRingHom K) ((ofFn 8 coeffInt).coeff j)=
        (ofFn 8 (RKCert.Paired.radauLeft7_coeff (K:=K))).coeff j
    rw [ofFn_coeff_eq_val_of_lt _ h,ofFn_coeff_eq_val_of_lt _ h]
    have e (j : Fin 8) :
        (Int.castRingHom K) (coeffInt j) = RKCert.Paired.radauLeft7_coeff j := by
      fin_cases j <;> norm_num [coeffInt,RKCert.Paired.radauLeft7_coeff]
    exact e ⟨j,h⟩
  · change (Int.castRingHom K) ((ofFn 8 coeffInt).coeff j)=
        (ofFn 8 (RKCert.Paired.radauLeft7_coeff (K:=K))).coeff j
    rw [ofFn_coeff_eq_zero_of_ge _ (by omega),ofFn_coeff_eq_zero_of_ge _ (by omega),map_zero]

def scaledRoot (i : Fin 8) : F := ((-51480:ℤ):F)*leftGrid i

theorem leading_mod_ne : ((-51480:ℤ):F)≠0 := by decide

theorem scaledRoot_inj : Function.Injective scaledRoot :=
  fun _ _ e => root_table.2 (mul_left_cancel₀ leading_mod_ne e)

theorem eval_grid_mod (i : Fin 8) : gridInt.eval₂ (Int.castRingHom F) (leftGrid i)=0 := by
  rw [gridInt,eval₂_mul,eval₂_X,eval_reproducer_mod]
  refine Fin.cases ?_ (fun j => ?_) i
  · change (0:F)*reproducer (leftGrid 0)=0
    rw [zero_mul]
  · change leftRoots j*reproducer (leftRoots j)=0
    rw [(root_table.1 j).1,mul_zero]

theorem scaled_grid_factor :
    gridNormalized.map (Int.castRingHom F)=∏ i : Fin 8,(X-C (scaledRoot i)) := by
  let P := gridNormalized.map (Int.castRingHom F)
  have pm : P.Monic := (monic_integralNormalization grid_ne).map _
  have root (i : Fin 8) : P.IsRoot (scaledRoot i) := by
    change (gridNormalized.map (Int.castRingHom F)).eval (scaledRoot i)=0
    rw [Polynomial.eval_map]
    have e := integralNormalization_eval₂_leadingCoeff_mul
      (p:=gridInt) (by rw [grid_degree]; decide) (Int.castRingHom F) (leftGrid i)
    rw [grid_leading,eval_grid_mod,mul_zero] at e
    exact e
  let factors := fun i : Fin 8 => X-C (scaledRoot i)
  have hm := monic_prod_X_sub_C scaledRoot Finset.univ
  have hd : (∏ i : Fin 8,factors i).natDegree=8 := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (scaledRoot i))]
    simp
  have div : (∏ i : Fin 8,factors i)∣P := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr (fun e => hij (scaledRoot_inj e))).isUnit
    · exact fun i _ => dvd_iff_isRoot.mpr (root i)
  exact eq_of_monic_of_dvd_of_natDegree_le hm pm div (by
    rw [hd]
    exact natDegree_map_le.trans (by rw [gridNormalized,natDegree_integralNormalization,grid_degree]))

set_option maxHeartbeats 500000 in
theorem scaled_grid_good :
    IsCoprime (gridNormalized.map (Int.castRingHom F))
      (gridNormalized.derivative.map (Int.castRingHom F)) := by
  rw [←Polynomial.derivative_map]
  change (gridNormalized.map (Int.castRingHom F)).Separable
  rw [scaled_grid_factor]
  exact separable_prod_X_sub_C_iff.mpr scaledRoot_inj

variable {ι : Type*} {K : Type u} [Field K] [CharZero K]

def scaledInput (a : ι→K) (i : Option ι) : K := ((-51480:ℤ):K)*(i.elim 0 a)

structure GridLift (a : ι→K) where
  specialization : Specialization 77569 (scaledInput a)
  index : ι→Fin 8
  decoded : ∀ i, specialization.image (some i)=specialization.embed (scaledRoot (index i))
  distinct : ∀ i j,a i≠a j → index i≠index j
  nonorigin : ∀ i,a i≠0 → index i≠0

/-- A finite list of true fixed-grid roots can be represented by the
documented split-prime labels without merging distinct prescribed roots. -/
theorem exists_grid_lift (a : ι→K)
    (ha : ∀ i,a i=0 ∨ (RKCert.Paired.radauLeft7 : K[X]).eval (a i)=0) :
    Nonempty (GridLift a) := by
  have hroot (i : Option ι) : gridInt.eval₂ (Int.castRingHom K) (i.elim 0 a)=0 := by
    rw [gridInt,eval₂_mul,eval₂_X]
    cases i with
    | none => simp
    | some i =>
      rcases ha i with hi|hi
      · simp [hi]
      · rw [←Polynomial.eval_map,map_reproducer,Option.elim_some,hi,mul_zero]
  have hInt (i : Option ι) : IsIntegral ℤ (scaledInput a i) := by
    rw [scaledInput,←grid_leading]
    exact scaled_root_integral gridInt grid_ne (hroot i)
  obtain ⟨S⟩ := exists_specialization 77569 (scaledInput a) hInt
  have hNorm (i : Option ι) : gridNormalized.eval₂ (Int.castRingHom K) (scaledInput a i)=0 := by
    have h := integralNormalization_eval₂_leadingCoeff_mul (p:=gridInt)
      (by rw [grid_degree]; decide) (Int.castRingHom K) (i.elim 0 a)
    rw [hroot i,mul_zero,grid_leading] at h
    exact h
  have hS0 : S.image none=0 := by
    have htrue : (X:ℤ[X]).eval₂ (Int.castRingHom K) (scaledInput a none)=0 := by simp [scaledInput]
    have hh := S.root_preserved X none htrue
    simpa only [eval₂_X] using hh
  have roots (i : ι) : ∃ j : Fin 8,S.image (some i)=S.embed (scaledRoot j) := by
    have h := S.root_preserved gridNormalized (some i) (hNorm (some i))
    have e0 : S.embed.comp (Int.castRingHom F)=Int.castRingHom S.carrier := by ext z; simp
    have h' : ((gridNormalized.map (Int.castRingHom F)).map S.embed).eval (S.image (some i))=0 := by
      rwa [Polynomial.map_map,e0,Polynomial.eval_map]
    rw [scaled_grid_factor,Polynomial.map_prod,eval_prod] at h'
    obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp h'
    refine ⟨j,?_⟩
    simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,eval_sub,eval_X,eval_C,
      sub_eq_zero] using hj
  choose idx eq using roots
  have Kscale : ((-51480:ℤ):K)≠0 := by norm_num
  refine ⟨⟨S,idx,eq,?_,?_⟩⟩
  · intro i j hn E
    have hneq : scaledInput a (some i)≠scaledInput a (some j) :=
      fun h => hn (mul_left_cancel₀ Kscale h)
    exact S.distinct_roots_of_good_prime gridNormalized (hNorm _) (hNorm _) hneq scaled_grid_good
      (by rw [eq i,eq j,E])
  · intro i hn E
    have hneq : scaledInput a (some i)≠scaledInput a none := by
      intro h
      apply hn
      exact (mul_eq_zero.mp (by simpa [scaledInput] using h)).resolve_left Kscale
    exact S.distinct_roots_of_good_prime gridNormalized (hNorm _) (hNorm _) hneq scaled_grid_good
      (by rw [eq i,E,hS0]; simp [scaledRoot,leftGrid])

end RKCert.FixedPolynomial.Radau77569

module

public import RKCert.ReviewedNative.ERKEvenHorizon
public import RKCert.ReviewedNative.ForwardNodalGain
public import RKCert.ReviewedNative.OneOffAmplitudeTools
public import RKCert.ReviewedNative.ERKOrderEightLobattoScalar
public import RKCert.ReviewedNative.GradedProducts

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Order-independent tagged clock and profile lemmas

These are the needed published native proof slices, isolated from their
order-nine consumers; every order premise is parameterized by its actual
probe cost. The original quadratic defect and off knots are retained.
`cleanKnots` keeps the same actual-stage definition in a separate namespace
so that this additive extraction can coexist with the original census.
-/
namespace RKResearch.Certified.Graded.ERKTaggedHorizon

open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical

section Bands
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Off-supported polynomial columns in the actual quadratic defect. -/
noncomputable def bandMap (A : Matrix (Fin s) (Fin s) K) (q : ℕ) :
    (Fin (q+1)→K) →ₗ[K] (Fin s→K) := (diag (g A)).comp (coeffEval A q)

noncomputable abbrev band (A : Matrix (Fin s) (Fin s) K) (q : ℕ) := (bandMap A q).range

theorem ofFn_eval (A : Matrix (Fin s) (Fin s) K) (q : ℕ) (a : Fin (q+1)→K) :
    evalNodes A (ofFn (q+1) a) = coeffEval A q a := by
  have hd := ofFn_natDegree_lt (show 1≤q+1 by omega) a
  rw [evalNodes_eq_coeffEval A _ (Nat.le_of_lt_succ hd)]
  congr 1
  funext i
  exact ofFn_coeff_eq_val_of_lt a i.isLt

theorem band_iff {v : Fin s→K} {q : ℕ} :
    v ∈ band A q ↔ ∃ P : K[X], P.natDegree≤q ∧ v=diag (g A) (evalNodes A P) := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨ofFn _ a,Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a),
      congrArg (diag (g A)) (ofFn_eval A q a).symm⟩
  · rintro ⟨P,hd,rfl⟩
    exact ⟨fun i=>P.coeff i.val,congrArg (diag (g A)) (evalNodes_eq_coeffEval A P hd).symm⟩

theorem band_le (A : Matrix (Fin s) (Fin s) K) (q : ℕ) : band A q ≤ zeroSpace A (2+q) := by
  rintro _ ⟨a,rfl⟩
  change diag (g A) (coeffEval A q a) ∈ _
  rw [coeffEval_apply,map_sum]
  apply (zeroSpace A (2+q)).sum_mem
  intro i _
  rw [map_smul,normTree_clockTree]
  apply (zeroSpace A (2+q)).smul_mem
  have each (n : ℕ) : diag (g A) ((nodes A)^n)∈zeroSpace A (2+n) := by
    induction n with
    | zero => simpa [g] using mDef_mem A 1
    | succ n ih =>
      have h := diag_zeroSpace A (2+n) ih
      change diag (nodes A) (diag (g A) ((nodes A)^n))∈zeroSpace A (2+n+1) at h
      convert h using 1
      ext k
      simp [pow_succ,mul_comm,mul_left_comm]
  exact zeroSpace_mono A (by have := i.isLt; omega) (each i.val)

theorem band_rank {q : ℕ} (enough : q+1 ≤ (offKnots A).card) :
    finrank K (band A q) = q+1 := by
  have inj : Function.Injective (bandMap A q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a za
    let P := ofFn (q+1) a
    have hd : P.natDegree<q+1 := ofFn_natDegree_lt (by omega) a
    have zero : diag (g A) (evalNodes A P)=0 := by
      rw [ofFn_eval A q a]
      exact za
    have roots (x : K) (hx : x∈offKnots A) : P.eval x=0 := by
      obtain ⟨i,hi,rfl⟩ := mem_offKnots.mp hx
      exact (mul_eq_zero.mp (show g A i*P.eval (nodes A i)=0 from congrFun zero i)).resolve_left hi
    have zp := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P _ roots (hd.trans_le enough)
    exact injective_ofFn (q+1) (zp.trans (ofFn_zero _).symm)
  exact (LinearMap.finrank_range_of_inj inj).trans (Module.finrank_fin_fun K)

/-- Interpolation at clocks, not at physical rows. Repetition of an
abscissa causes no problem because the same input is fitted on every copy. -/
theorem band_stable {q : ℕ} (few : (offKnots A).card≤q+1) :
    (band A q).map (diag (nodes A)) ≤ band A q := by
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨P,_,rfl⟩ := band_iff.mp hv
  let f : K→K := fun x=>x*P.eval x
  let Q := Lagrange.interpolate (offKnots A) id f
  have hd : Q.natDegree≤q := by
    by_cases z : Q=0
    · simp [z]
    · have h := (natDegree_lt_iff_degree_lt z).mpr
          (Lagrange.degree_interpolate_lt f (Set.injOn_id _) (s:=offKnots A))
      omega
  apply band_iff.mpr ⟨Q,hd,?_⟩
  ext i
  change nodes A i * (g A i * P.eval (nodes A i)) = g A i * Q.eval (nodes A i)
  by_cases h : g A i=0
  · simp [h]
  · rw [show Q.eval (nodes A i)=f (nodes A i) from
      Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (mem_offKnots.mpr ⟨i,h,rfl⟩)]
    dsimp [f]
    ring

/-- The two-clock branch makes grade three stable and violates the
outgoing gain; three clocks make grade four stable and violate the incoming
gain. Both use precisely the actual minimal grade-three and grade-four ranks. -/
theorem not_two_or_three [CharZero K] (ha : ∀ i j, i≤j → A i j=0)
    (sep : PolySeparated A 4) (r3 : finrank K (zeroSpace A 3)=2)
    (r4 : finrank K (zeroSpace A 4)=3) :
    (offKnots A).card≠2 ∧ (offKnots A).card≠3 := by
  constructor
  · intro h
    have r := band_rank (A:=A) (q:=1) (by omega)
    have eqn : band A 1=zeroSpace A 3 := Submodule.eq_of_le_of_finrank_le
      (band_le A 1) (by omega)
    have stab := band_stable (A:=A) (q:=1) (by omega)
    rw [eqn] at stab
    have cost := clock_invariant_outgoing ha (sep.mono (by decide : 3≤4)) le_rfl stab
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at cost
    omega
  · intro h
    have r := band_rank (A:=A) (q:=2) (by omega)
    have eqn : band A 2=zeroSpace A 4 := Submodule.eq_of_le_of_finrank_le
      (band_le A 2) (by omega)
    have stab := band_stable (A:=A) (q:=2) (by omega)
    rw [eqn] at stab
    have cost := clock_invariant_incoming (j:=3) ha sep stab
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at cost
    omega

/-- Every nonzero quadratic defect is on one and the same nonzero quadratic
curve for every branch having at least three distinct defective clocks. -/
theorem two_curve_head (r3 : finrank K (zeroSpace A 3)=2) (r4 : finrank K (zeroSpace A 4)=3)
    (many : 3≤(offKnots A).card) :
    ∃ P : K[X], P.natDegree≤2 ∧ P≠0 ∧ zeroSpace A 3=band A 1 ∧ zeroSpace A 4=band A 2 ∧
      ∀ i, g A i≠0 → P.eval (nodes A i)=g A i := by
  have rone := band_rank (A:=A) (q:=1) (by omega)
  have rtwo := band_rank (A:=A) (q:=2) (by omega)
  have eq3 : band A 1=zeroSpace A 3 := Submodule.eq_of_le_of_finrank_le (band_le A 1) (by omega)
  have eq4 : band A 2=zeroSpace A 4 := Submodule.eq_of_le_of_finrank_le (band_le A 2) (by omega)
  have sq : g A * g A ∈ zeroSpace A 4 := zeroSpace_mul (mDef_mem A 1) (mDef_mem A 1)
  obtain ⟨P,hd,eq⟩ := band_iff.mp (eq4.symm ▸ sq)
  have fit (i) (nz : g A i≠0) : P.eval (nodes A i)=g A i :=
    (mul_left_cancel₀ nz (show g A i*g A i=g A i*P.eval (nodes A i) from congrFun eq i)).symm
  refine ⟨P,hd,?_,eq3.symm,eq4.symm,fit⟩
  intro z
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0<(offKnots A).card)
  obtain ⟨i,hi,_⟩ := mem_offKnots.mp hx
  exact hi (by simpa [z] using (fit i hi).symm)

/-- All fourth-grade defects vanish on the clean rows of a two-curve chart. -/
theorem clean_four_vanish (hF : zeroSpace A 4=band A 2) {i : Fin s}
    (clean : g A i=0) {w : Fin s→K} (hw : w∈zeroSpace A 4) : w i=0 := by
  obtain ⟨P,_,rfl⟩ := band_iff.mp (hF ▸ hw)
  simp [clean]

end Bands

section TaggedMoments
variable {K : Type*} [Field K] {s : ℕ}
variable {p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

noncomputable def cleanKnots (A : Matrix (Fin s) (Fin s) K) : Finset K :=
  (Finset.univ.filter fun i => g A i=0).image (nodes A)

theorem mem_cleanKnots {x : K} : x∈cleanKnots A ↔ ∃i,g A i=0 ∧ nodes A i=x := by
  simp [cleanKnots]

theorem clean_off_count (A : Matrix (Fin s) (Fin s) K) :
    (cleanKnots A).card + (offKnots A).card ≤ s := by
  unfold cleanKnots offKnots
  apply (add_le_add Finset.card_image_le Finset.card_image_le).trans
  simpa using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => g A i=0)).le

noncomputable def offMass (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (x : K) : K :=
  ∑ i, if g A i≠0 ∧ nodes A i=x then b i else 0

theorem offMass_zero_of_head (ho : HasOrder p A b) {P : K[X]}
    (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (pay : (offKnots A).card+2≤p) (x : K) (hx : x∈offKnots A) : offMass A b x=0 := by
  let S := offKnots A
  let f : K→K := fun y=>if y=x then 1 else 0
  let Q := Lagrange.interpolate S id f
  have ev (y : K) (hy : y∈S) : Q.eval y=f y := Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hy
  have dQ : Q.natDegree<S.card := by
    by_cases z : Q=0
    · rw [z,natDegree_zero]
      exact Finset.card_pos.mpr ⟨x,hx⟩
    · exact (natDegree_lt_iff_degree_lt z).mpr (Lagrange.degree_interpolate_lt f (Set.injOn_id _))
  have inF := band_le A Q.natDegree (band_iff.mpr ⟨Q,le_rfl,rfl⟩)
  change S.card+2≤p at pay
  have eqn : probe A b 0 (diag (g A) (evalNodes A Q))=0 :=
    probe_zeroSpace ho (by omega) inF
  have prod : probe A b 0 (diag (g A) (evalNodes A Q))=P.eval x*offMass A b x := by
    simp only [probe,row_apply,dotProduct,diag_apply,evalNodes_apply,offMass,Finset.mul_sum,pow_zero,mul_one]
    apply Finset.sum_congr rfl
    intro i _
    by_cases z : g A i=0
    · simp [z]
    · have mi : nodes A i∈S := mem_offKnots.mpr ⟨i,z,rfl⟩
      rw [ev _ mi]
      by_cases atx : nodes A i=x
      · have u := fit i z
        rw [atx] at u
        simp [f,z,atx,u,mul_comm]
      · simp [f,z,atx]
  obtain ⟨i,ng,atx⟩ := mem_offKnots.mp hx
  have nz : P.eval x≠0 := by rwa [←atx,fit _ ng]
  exact (mul_eq_zero.mp (prod.symm.trans eqn)).resolve_left nz

/-- Any test function vanishing at the clean knots is killed at every
monomial probe after aggregate cancellation. No polynomial degree enters here. -/
theorem probe_zero_of_clean_roots
    (cancel : ∀ x∈offKnots A, offMass A b x=0)
    (P : K[X]) (roots : ∀x∈cleanKnots A, P.eval x=0) (k : ℕ) :
    probe A b k (evalNodes A P)=0 := by
  let T := offKnots A
  have split (i : Fin s) : b i * nodes A i^k * P.eval (nodes A i) =
      ∑ x∈T, (if g A i≠0 ∧ nodes A i=x then b i else 0) * (x^k*P.eval x) := by
    by_cases hi : g A i=0
    · have z := roots _ (mem_cleanKnots.mpr ⟨i,hi,rfl⟩)
      simp [hi,z]
    · have hm : nodes A i∈T := mem_offKnots.mpr ⟨i,hi,rfl⟩
      rw [Finset.sum_eq_single (nodes A i)]
      · simp [hi,mul_assoc]
      · intro x _ hx; simp [Ne.symm hx]
      · intro h; exact (h hm).elim
  simp only [probe,row_apply,dotProduct,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => split i),Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x hx
  rw [←Finset.sum_mul]
  change offMass A b x*(x^k*P.eval x)=0
  rw [cancel x hx,zero_mul]

end TaggedMoments

section TaggedOrigin
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
theorem zero_mem_cleanKnots {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : ∀ i j, i≤j → A i j=0) : 0∈cleanKnots A := by
  apply mem_cleanKnots.mpr
  refine ⟨0,origin_zeroSpace ha 2 (mDef_mem A 1),?_⟩
  change (∑ j, A 0 j * 1) = 0
  exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]

end TaggedOrigin

section PositiveOff
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem off_pos [CharZero K] (ha : ∀ i j, i≤j → A i j=0) (sep : PolySeparated A 4) :
    0 < (offKnots A).card := by
  by_contra! no
  have gz : g A=0 := by
    funext i
    by_contra h
    have pos := Finset.card_pos.mpr ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩
    omega
  exact not_invariant_with_g ha sep (by decide) (U:=⊥) bot_le (gz ▸ Submodule.zero_mem _)
    (fun _ hv=> by rw [(Submodule.mem_bot K).mp hv,map_zero]; exact Submodule.zero_mem _)
    (fun _ hv=> by rw [(Submodule.mem_bot K).mp hv,map_zero]; exact Submodule.zero_mem _)

end PositiveOff

section TaggedStates
variable {K : Type*} [Field K] {s : ℕ}

theorem coordinate_as_single (i : Fin s) : Reverse.coordinate (K:=K) i = Pi.single i 1 := by
  ext j
  by_cases eq : j=i
  · subst j; simp [Reverse.coordinate]
  · simp [Reverse.coordinate,eq]

noncomputable def onOffEval (A : Matrix (Fin s) (Fin s) K) :
    (((cleanKnots A) → K) × ((offKnots A) → K)) →ₗ[K] (Fin s → K) where
  toFun z i := if h : g A i=0 then z.1 ⟨nodes A i,mem_cleanKnots.mpr ⟨i,h,rfl⟩⟩
    else z.2 ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩
  map_add' x y := by ext i; dsimp; split <;> rfl
  map_smul' a x := by ext i; dsimp; split <;> rfl

noncomputable def onOffSpace (A : Matrix (Fin s) (Fin s) K) : Submodule K ((Fin s → K)) :=
  LinearMap.range (onOffEval A)

theorem onOffEval_on (A : Matrix (Fin s) (Fin s) K) (z) {i : Fin s} (hi : g A i=0) :
    onOffEval A z i = z.1 ⟨nodes A i,mem_cleanKnots.mpr ⟨i,hi,rfl⟩⟩ := dite_eq_left hi

theorem onOffEval_off (A : Matrix (Fin s) (Fin s) K) (z) {i : Fin s} (hi : g A i≠0) :
    onOffEval A z i = z.2 ⟨nodes A i,mem_offKnots.mpr ⟨i,hi,rfl⟩⟩ := dite_eq_right hi

theorem pairProfile_mem_onOffSpace {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i) (Q R : K[X]) :
    evalNodes A Q+diag (g A) (evalNodes A R)∈onOffSpace A := by
  refine ⟨(fun a => Q.eval a.val,fun a => Q.eval a.val + P.eval a.val*R.eval a.val),?_⟩
  ext i
  by_cases h : g A i=0
  · rw [onOffEval_on A _ h]
    simp [h]
  · rw [onOffEval_off A _ h]
    simp [hP i h]

noncomputable def gradeFiveStateMap (A : Matrix (Fin s) (Fin s) K) : ((Fin 6 → K) × (Fin 4 → K)) →ₗ[K] (Fin s → K) :=
  (coeffEval A 5).coprod ((diag (g A)).comp (coeffEval A 3))

noncomputable def gradeFiveStateSpace (A : Matrix (Fin s) (Fin s) K) : Submodule K ((Fin s → K)) :=
  LinearMap.range (gradeFiveStateMap A)

theorem pairProfile_mem_E5 (A : Matrix (Fin s) (Fin s) K) (Q R : K[X])
    (hQ : Q.natDegree ≤ 5) (hR : R.natDegree ≤ 3) :
    evalNodes A Q + diag (g A) (evalNodes A R) ∈ treeSpace A 5 := by
  apply (treeSpace A 5).add_mem (evalNodes_mem_treeSpace A Q hQ)
  apply zeroSpace_le_treeSpace A 5
  apply band_le A 3
  exact band_iff.mpr ⟨R,hR,rfl⟩

theorem gradeFiveStateMap_eq_eval (A : Matrix (Fin s) (Fin s) K) (z : (Fin 6 → K) × (Fin 4 → K)) :
    gradeFiveStateMap A z = evalNodes A (ofFn 6 z.1) + diag (g A) (evalNodes A (ofFn 4 z.2)) := by
  rw [ofFn_eval A 5,ofFn_eval A 3]
  rfl

theorem gradeFiveStateSpace_le (A : Matrix (Fin s) (Fin s) K) :
    gradeFiveStateSpace A ≤ treeSpace A 5 := by
  rintro _ ⟨z,rfl⟩
  rw [gradeFiveStateMap_eq_eval]
  apply pairProfile_mem_E5
  · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)

theorem gradeFiveState_injective {A : Matrix (Fin s) (Fin s) K} (hM : 6 ≤ (cleanKnots A).card)
    (hN : 4 ≤ (offKnots A).card) : Function.Injective (gradeFiveStateMap A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  have hQ : Q.natDegree ≤ 5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hR : R.natDegree ≤ 3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have he (i : Fin s) : Q.eval (nodes A i)+g A i*R.eval (nodes A i)=0 := by
    rw [gradeFiveStateMap_eq_eval] at hz
    exact congrFun hz i
  have hQ0 : Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q (cleanKnots A)
    (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_cleanKnots.mp hx
      simpa [hi] using he i) (by omega)
  have hR0 : R=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R (offKnots A)
    (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_offKnots.mp hx
      exact (mul_eq_zero.mp (by simpa [hQ0] using he i)).resolve_left hi) (by omega)
  exact Prod.ext (injective_ofFn 6 (hQ0.trans (ofFn_zero _).symm))
    (injective_ofFn 4 (hR0.trans (ofFn_zero _).symm))

theorem gradeFiveState_rank {A : Matrix (Fin s) (Fin s) K} (hM : 6 ≤ (cleanKnots A).card)
    (hN : 4 ≤ (offKnots A).card) : finrank K (gradeFiveStateSpace A)=10 := by
  rw [gradeFiveStateSpace,LinearMap.finrank_range_of_inj (gradeFiveState_injective hM hN),
    Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun]

theorem state_single_is_unique_off {A : Matrix (Fin s) (Fin s) K} {i j : Fin s}
    (hi : Pi.single i 1 ∈ onOffSpace A) (hdi : g A i≠0) (hdj : g A j≠0)
    (hc : nodes A j=nodes A i) : j=i := by
  obtain ⟨z,hz⟩ := hi
  have he : onOffEval A z j=onOffEval A z i := by
    rw [onOffEval_off A _ hdj,onOffEval_off A _ hdi]
    have h : (⟨nodes A j,mem_offKnots.mpr ⟨j,hdj,rfl⟩⟩ : offKnots A) =
        ⟨nodes A i,mem_offKnots.mpr ⟨i,hdi,rfl⟩⟩ := Subtype.ext hc
    rw [h]
  rw [hz] at he
  by_contra h
  simp [h] at he

/-- A unique off state with a nonzero weight cannot lie in a state-valued
terminal coordinate once the off weights cancel in each state. -/
theorem on_of_state_single {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {i : Fin s}
    (hA : Pi.single i 1 ∈ onOffSpace A) (hbi : b i≠0)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    g A i=0 := by
  by_contra hd
  have he := hoff _ (mem_offKnots.mpr ⟨i,hd,rfl⟩)
  unfold offMass at he
  rw [Finset.sum_eq_single i] at he
  · simp [hd,hbi] at he
  · intro j _ hj
    have h : ¬ (g A j≠0 ∧ nodes A j=nodes A i) :=
      fun hh => hj (state_single_is_unique_off hA hd hh.1 hh.2)
    simp [h]
  · simp

end TaggedStates

section AnchoredPrimitives
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
/-- Product of the two head curves vanishes at every affordable probe
whenever its value vanishes on the clean knots. -/
theorem probe_head_product_zero {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder p A b) {P : K[X]} (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (Q : K[X]) (on : ∀ x∈cleanKnots A, P.eval x*Q.eval x=0)
    (k : ℕ) (pay : k+Q.natDegree+3≤p) : probe A b k (evalNodes A (P*Q))=0 := by
  apply probe_zeroSpace ho (j:=2+Q.natDegree) (by omega)
  apply band_le A Q.natDegree
  apply band_iff.mpr ⟨Q,le_rfl,?_⟩
  ext i
  by_cases hi : g A i=0
  · have z := on _ (mem_cleanKnots.mpr ⟨i,hi,rfl⟩)
    simp [hi,z]
  · simp [fit i hi]

theorem on_primitive_zero_of_prefix {A : Matrix (Fin s) (Fin s) K} {i : Fin s}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4=band A 2) (hi : g A i=0)
    (Q : K[X]) (hq : Q.natDegree≤3) (v : Fin s→K) (hv : mat A v i=0)
    (hpre : ∀ j, j < i → Q.eval (nodes A j)=v j) : (primitive Q).eval (nodes A i)=0 := by
  have rem := clean_four_vanish hF hi (primitive_defect A Q (q:=3) hq)
  have eq := causal_action_eq ha i (evalNodes A Q) v hpre
  change mat A (evalNodes A Q) i - (primitive Q).eval (nodes A i)=0 at rem
  rw [eq,hv,zero_sub,neg_eq_zero] at rem
  exact rem

theorem clean_mixed_defect {A : Matrix (Fin s) (Fin s) K}
    (hF : zeroSpace A 4=band A 2) {i : Fin s} (hi : g A i=0) :
    mat A (diag (nodes A) (g A)) i=0 :=
  clean_four_vanish hF hi (mat_zeroSpace_charZero A 3 (diag_zeroSpace A 2 (mDef_mem A 1)))

omit [CharZero K] in
theorem exists_nonzero_on_of_card {A : Matrix (Fin s) (Fin s) K}
    (h : 2 ≤ (cleanKnots A).card) : ∃ i, g A i=0 ∧ nodes A i≠0 := by
  by_contra! h'
  have hs : cleanKnots A ⊆ ({0}:Finset K) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_cleanKnots.mp hx
    simpa using h' i hi
  have hn := Finset.card_le_card hs
  simp at hn
  omega

omit [CharZero K] in
theorem anchor_probe_coeff {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder p A b) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+2 ≤ p)
    (hz : probe A b k (evalNodes A (X*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he : probe A b k (evalNodes A (X*Q)) = probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,eval_mul,eval_X,pow_succ]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,evalNodes_eq_coeffEval A Q hd,probe_coeffEval ho (by omega)] at hz
  have e (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e] using hz

omit [CharZero K] in
theorem anchored_poly_zero_of_probes {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder p A b) (n : ℕ) (pay : 2*n+2≤p)
    (Q : K[X]) (hd : Q.natDegree≤n)
    (hm : ∀ k : Fin (n+1), probe A b k.val (evalNodes A (X*Q))=0) : Q=0 := by
  let a : Fin (n+1) → K := fun j => Q.coeff j.val
  have hs (k : Fin (n+1)) : (∑ j : Fin (n+1),a j/((k.val+j.val+2:ℕ):K))=0 :=
    anchor_probe_coeff ho Q hd (by have := k.isLt; omega) (hm k)
  have hz := moments_detect ho (d:=2) (by decide) (by omega) (fun i j => by omega) a hs
  ext k
  by_cases hk : k<n+1
  · exact hz ⟨k,hk⟩
  · simpa using (coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree<k))

end AnchoredPrimitives

section TerminalProfiles
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem profile_on_eval {A : Matrix (Fin s) (Fin s) K} (Q R : K[X]) {v : (Fin s→K)}
    (hv : evalNodes A Q + diag (g A) (evalNodes A R)=v) {i : Fin s}
    (hi : g A i=0) : Q.eval (nodes A i)=v i := by
  simpa [hi] using congrFun hv i

omit [CharZero K] in
theorem profile_off_eval {A : Matrix (Fin s) (Fin s) K} {P Q R : K[X]} {v : (Fin s→K)}
    (hv : evalNodes A Q + diag (g A) (evalNodes A R)=v)
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    {i : Fin s} (hi : g A i≠0) : (Q+P*R).eval (nodes A i)=v i := by
  simpa [hP i hi] using congrFun hv i

omit [CharZero K] in
theorem single_profile_on_unique {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {Q R : K[X]}
    (he : evalNodes A Q + diag (g A) (evalNodes A R) = Pi.single (Fin.last s) 1)
    (hdi : g A (Fin.last s)=0) (hc : nodes A (Fin.last s)=1) (j : Fin (s+1))
    (hj : g A j=0) (h1 : nodes A j=1) : j=Fin.last s := by
  by_contra hne
  have h := (profile_on_eval Q R he hj).symm.trans ((congrArg (fun x => Q.eval x)
    (h1.trans hc.symm)).trans (profile_on_eval Q R he hdi))
  simp [hne] at h

omit [CharZero K] in
theorem on_hull_times_head_probes {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder p A b) {P : K[X]} (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (k : ℕ) (pay : k+(cleanKnots A).card+3≤p) :
    probe A b k (evalNodes A (P*nodalHull (cleanKnots A)))=0 :=
  probe_head_product_zero ho fit _ (fun _ hx=>by rw [nodalHull_eval_of_mem hx,mul_zero])
    k (by rwa [natDegree_nodalHull])

omit [CharZero K] in
theorem profile_terminal_on_of_large_off {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {P Q R : K[X]}
    (rank : (Q+P*R).natDegree+1<(offKnots A).card)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (profile : evalNodes A Q+diag (g A) (evalNodes A R)=Pi.single (Fin.last s) 1) :
    g A (Fin.last s)=0 := by
  by_contra hn
  let i := Fin.last s
  let T := @Finset.erase K (fun _ _ => Classical.propDecidable _) (offKnots A) (nodes A i)
  have card : T.card+1=(offKnots A).card :=
    Finset.card_erase_add_one (mem_offKnots.mpr ⟨i,hn,rfl⟩)
  have eq : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T (fun x hx=>by
    obtain ⟨hxi,hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,hxj⟩ := mem_offKnots.mp hx
    have ji : j≠i := fun e => hxi (hxj.symm.trans (congrArg (nodes A) e))
    rw [←hxj,profile_off_eval profile fit hj]
    simp [ji,i]) (by omega)
  have h := profile_off_eval profile fit hn
  simp [eq] at h

end TerminalProfiles

section CubicProbes
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem beta_probe_coeff {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder p A b) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+3 ≤ p)
    (h : probe A b k (evalNodes A ((X^2-X)*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+3:ℕ):K)) -
      (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he :
      probe A b k (evalNodes A ((X^2-X)*Q)) =
        probe A b (k+2) (evalNodes A Q) - probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,←Finset.sum_sub_distrib,eval_mul,eval_sub,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_add,pow_one]
    ring
  rw [he,evalNodes_eq_coeffEval A Q hd,probe_coeffEval ho (by omega),
    probe_coeffEval ho (by omega)] at h
  have e (j : Fin (n+1)) : k+2+j.val+1=k+j.val+3 := by omega
  have e' (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e,e'] using h

theorem beta_cubic_from_actual_probes {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder p A b) (hp : 8 ≤ p) (Q : K[X]) (hd : Q.natDegree ≤ 3)
    (hz : ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*Q))=0) :
    Q = C (Q.coeff 3)*RKResearch.Certified.Graded.LobattoEight.lobattoCubic := by
  apply RKResearch.Certified.Graded.LobattoEight.lobatto_cubic_decoder Q hd
  intro k
  exact beta_probe_coeff ho Q hd (by have := k.isLt; omega) (hz k)

end CubicProbes

end RKResearch.Certified.Graded.ERKTaggedHorizon

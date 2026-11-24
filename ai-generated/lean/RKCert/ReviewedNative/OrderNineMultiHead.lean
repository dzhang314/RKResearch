module
public import RKCert.ReviewedNative.OrderNineOneOffPaid
public import RKCert.ReviewedNative.ForwardNodalGain
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-! # Clock bands for the multi-defect order-nine census

The vectors, ranks and order witnesses are native throughout. At the exact
number of supported clocks the band is clock-stable by interpolation. This
allows the incoming Hermite gain to eliminate three clocks without the
separate three-off chronology or any ordered-field assumption. -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Polynomial Module OneOff
open scoped Matrix Classical

variable {K : Type*} [Field K] {s p : ℕ}
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

theorem order9_two_curve_head [CharZero K] (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b 9) (cap : s≤12) (many : 3≤(offKnots A).card) :
    ∃ P : K[X], P.natDegree≤2 ∧ P≠0 ∧ zeroSpace A 3=band A 1 ∧ zeroSpace A 4=band A 2 ∧
      ∀ i, g A i≠0 → P.eval (nodes A i)=g A i := by
  obtain ⟨_,r3,r4,_⟩ := order9_forward_chart ha ho cap
  exact two_curve_head r3 r4 many

end RKResearch.Certified.Graded.MultiOff

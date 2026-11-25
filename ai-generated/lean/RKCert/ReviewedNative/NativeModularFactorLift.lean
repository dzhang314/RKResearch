module

public import RKCert.ReviewedNative.NativeModularRootLift
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

/-! # A monic factor and a marked complementary root in one residue place

A simultaneous monic divisor is lifted before the chosen prime reduction.
If the reduction of its marked root were also a root of the reduced
factor, the target separable polynomial would have a square divisor. -/

namespace RKResearch.Certified.Graded.NativeModularRootLift

open Polynomial
open scoped BigOperators

universe u

/-- In addition to the two distinct roots, keep the chosen monic factor
in the same integral closure and keep the whole marked divisor. The
second root may be the origin. -/
theorem with_reduced_monic_factor_at_distinct_root
    {E : Type u} [Field E] [CharZero E] (p : ℕ) (pp : p.Prime)
    {P : ℤ[X]} (m : P.Monic)
    (s : (P.map (Int.castRingHom (ZMod p))).Separable)
    {a b : E} (ha : (P.map (algebraMap ℤ E)).IsRoot a)
    (hb : (P.map (algebraMap ℤ E)).IsRoot b) (different : a ≠ b)
    {R : E[X]} (mr : R.Monic) (dvd : (X - C a) * R ∣ P.map (algebraMap ℤ E))
    {goal : Prop}
    (h : ∀ (k : Type u) [Field k] [CharP k p]
       (q : integralClosure ℤ E →+* k) (A B : integralClosure ℤ E)
       (U : (integralClosure ℤ E)[X]),
       (A : E) = a → (B : E) = b → q A ≠ q B →
       (P.map (Int.castRingHom k)).IsRoot (q A) →
       U.map (algebraMap (integralClosure ℤ E) E) = R → U.Monic →
       (X - C (q A)) * U.map q ∣ P.map (Int.castRingHom k) →
       ¬ (U.map q).IsRoot (q A) → goal) : goal := by
  classical
  let C₀ := integralClosure ℤ E
  let e : C₀ →+* E := algebraMap C₀ E
  have inj : Function.Injective e := fun _ _ z => Subtype.ext z
  have rD : R ∣ P.map (algebraMap ℤ E) := (dvd_mul_left R (X-C a)).trans dvd
  have lift : R ∈ Polynomial.lifts e :=
    integralClosure.mem_lifts_of_monic_of_dvd_map E m mr rD
  obtain ⟨U, eU⟩ := (Polynomial.mem_lifts (f:=e) R).mp lift
  have mU : U.Monic := inj.monic_map_iff.mpr (eU.symm ▸ mr)
  refine with_distinct_monic_root_reduction p pp m s ha hb different ?_
  intro k _ _ q A B haA hbB hAr hBr sepAB
  let P₀ := P.map (algebraMap ℤ C₀)
  have ep : P₀.map e = P.map (algebraMap ℤ E) := by
    dsimp only [P₀, e]
    rw [map_map, ← IsScalarTower.algebraMap_eq ℤ C₀ E]
  have ea : e A = a := haA
  have dB : (X - C A) * U ∣ P₀ := by
    apply (Polynomial.map_dvd_map e inj ((monic_X_sub_C A).mul mU)).mp
    simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      ea, eU, ep] using dvd
  have red : P₀.map q = P.map (Int.castRingHom k) := by
    dsimp only [P₀]
    rw [map_map]
    exact congrArg (fun f : ℤ →+* k => P.map f) (RingHom.ext_int _ _)
  have dK : (X - C (q A)) * U.map q ∣ P.map (Int.castRingHom k) := by
    simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      red] using Polynomial.map_dvd q dB
  let z := ZMod.castHom (dvd_refl p) k
  have rK : P.map (Int.castRingHom k) = (P.map (Int.castRingHom (ZMod p))).map z := by
    rw [Polynomial.map_map]
    exact congrArg (fun f : ℤ →+* k => P.map f) (RingHom.ext_int _ _)
  have sK : (P.map (Int.castRingHom k)).Separable := rK.symm ▸ s.map
  have excluded : ¬ (U.map q).IsRoot (q A) := by
    intro rt
    have d := dvd_iff_isRoot.mpr rt
    have sq : (X - C (q A)) * (X - C (q A)) ∣ P.map (Int.castRingHom k) :=
      (mul_dvd_mul_left (X - C (q A)) d).trans dK
    exact not_isUnit_X_sub_C _ (isUnit_of_self_mul_dvd_separable sK sq)
  exact h k q A B U haA hbB sepAB hAr eU mU dK excluded

/-- A monic polynomial of the right degree vanishing at all injective
numerical labels is their full product. -/
theorem eq_prod_of_monic_label_roots {K ι : Type*} [Field K] [Fintype ι]
    (r : ι → K) (inj : Function.Injective r) (P : K[X]) (m : P.Monic)
    (degree : P.natDegree ≤ Fintype.card ι) (roots : ∀ i, P.IsRoot (r i)) :
    P = ∏ i, (X - C (r i)) := by
  classical
  have pd : (∏ i, (X - C (r i))).natDegree = Fintype.card ι := by
    rw [natDegree_prod_of_monic (Finset.univ : Finset ι) (fun i => (X:K[X]) - C (r i))
      (fun i _ => monic_X_sub_C (r i))]
    simp
  have d : (∏ i, (X - C (r i))) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ ne
      exact pairwise_coprime_X_sub_C inj ne
    · exact fun i _ => dvd_iff_isRoot.mpr (roots i)
  exact eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C r Finset.univ) m d
    (pd.symm ▸ degree)

/-- A monic divisor of a distinctly labelled split polynomial is the
product of exactly its own root labels, each used once. -/
theorem monic_divisor_eq_label_subproduct {K ι : Type*} [Field K] [Fintype ι]
    (r : ι → K) (inj : Function.Injective r) (P : K[X]) (m : P.Monic)
    (d : P ∣ ∏ i, (X - C (r i))) :
    ∃ S : Finset ι, (∀ i, i ∈ S ↔ P.IsRoot (r i)) ∧
      P = ∏ i ∈ S, (X - C (r i)) := by
  classical
  let F : K[X] := ∏ i, (X - C (r i))
  have nz : F ≠ 0 := (monic_prod_X_sub_C r Finset.univ).ne_zero
  have split : F.Splits := Splits.prod (fun i _ => Splits.X_sub_C (r i))
  have small : P.Splits := split.of_dvd nz d
  have sep : F.Separable := separable_prod (pairwise_coprime_X_sub_C inj)
    (fun _ => separable_X_sub_C)
  have nd : P.roots.Nodup := nodup_roots (sep.of_dvd d)
  have rloc {x : K} (hh : P.IsRoot x) : ∃ i, r i = x := by
    have hz := (hh.dvd d).eq_zero
    change F.eval x=0 at hz
    dsimp only [F] at hz
    rw [eval_prod] at hz
    simp only [eval_sub, eval_X, eval_C] at hz
    obtain ⟨i, _, he⟩ := Finset.prod_eq_zero_iff.mp hz
    exact ⟨i, (sub_eq_zero.mp he).symm⟩
  let S : Finset ι := Finset.univ.filter (fun i => P.IsRoot (r i))
  have mem (i : ι) : i ∈ S ↔ P.IsRoot (r i) := by simp [S]
  have image : S.image r = P.roots.toFinset := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Multiset.mem_toFinset.mpr ((mem_roots m.ne_zero).mpr ((mem i).mp hi))
    · intro hx
      have hr := (mem_roots m.ne_zero).mp (Multiset.mem_toFinset.mp hx)
      obtain ⟨i, hi⟩ := rloc hr
      exact Finset.mem_image.mpr ⟨i, (mem i).mpr (hi.symm ▸ hr), hi⟩
  refine ⟨S, mem, ?_⟩
  calc
    P = ∏ x ∈ P.roots.toFinset, (X-C x) := by
      conv_lhs => rw [small.eq_prod_roots_of_monic m]
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr nd]
    _ = _ := by rw [←image, Finset.prod_image inj.injOn]

end RKResearch.Certified.Graded.NativeModularRootLift

module
public import RKCert.NodalHermiteRank
public import RKCert.ReviewedNative.GradedPrimitives
public import RKCert.ReviewedNative.CausalStage

@[expose] public section

/-! # Strictly causal Hermite gain in either stage order

The permutation only names the chronology. The signature, failed-block
count, subspaces, and the test with the native primitive all use the
original vectors, so no tableau surgery is involved. -/
namespace RKResearch.Certified.Graded
open RKResearch Polynomial Module RKCert.Endpoint

variable {K : Type*} [Field K] {s : ℕ}

/-- The existing Hermite primitive has precisely the native coefficients. -/
theorem formalPrimitive_eq_native (P : K[X]) : formalPrimitive P=primitive P := by
  unfold formalPrimitive
  conv_rhs => rw [P.as_sum_support]
  simp only [map_sum, primitive_monomial, Nat.cast_add,Nat.cast_one]

/-- A native primitive is paid in arbitrary Z, not necessarily an annihilator.
The original coordinates may be read forwards or backwards (or under any
other explicit permutation), and the base column need not be one. -/
theorem ordered_hermite_outgoing [CharZero K]
    (ord : Fin s ≃ Fin s) (N : Module.End K (Fin s→K)) (hc : Causal ord N)
    (c v : Fin s → K) (U Z : Submodule K (Fin s→K))
    (hmask : MaskInvariant c U) (sub : U ≤ Z) (moves : ∀ x∈U,N x∈Z) (r : ℕ)
    (count : r ≤ (failedNodes c v U s).card)
    (paid : ∀ P : K[X],P.natDegree+1 ≤ 2*r →
      N (weightedEval c v P)-weightedEval c v (primitive P)∈Z) :
    finrank K U+r ≤ finrank K Z := by
  classical
  let E : (Fin s→K) ≃ₗ[K] (Fin s→K) := LinearEquiv.funCongrLeft K K ord.symm
  let M := E.toLinearMap.comp (N.comp E.symm.toLinearMap)
  have atOrd (x : Fin s→K) (i : Fin s) : E x (ord i)=x i :=
    congrArg x (ord.symm_apply_apply i)
  have mE (x : Fin s→K) : M (E x)=E (N x) := by
    change E (N (E.symm (E x)))=_
    rw [E.symm_apply_apply]
  have chron : StrictlyCausal M := by
    intro i x y hxy
    have z := hc (ord.symm i) (E.symm x-E.symm y) (by
      intro k hk
      rw [ord.apply_symm_apply] at hk
      change x (ord k)-y (ord k)=0
      exact sub_eq_zero.mpr (hxy (ord k) hk))
    change N (E.symm x) (ord.symm i)=N (E.symm y) (ord.symm i)
    simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using z
  have mask : MaskInvariant (E c) (U.map E.toLinearMap) := by
    rintro a _ ⟨x,hx,rfl⟩
    exact ⟨blockMask c a x,hmask a x hx,rfl⟩
  have nodes : failedNodes c v U s ⊆ failedNodes (E c) (E v) (U.map E.toLinearMap) s := by
    intro a h
    obtain ⟨an,no⟩:=mem_failedNodes.mp h
    refine mem_failedNodes.mpr ⟨an,?_⟩
    rintro ⟨_,⟨x,hx,rfl⟩,matchx⟩
    apply no
    refine ⟨x,hx,fun i _ hi => ?_⟩
    have q := matchx (ord i) (ord i).isLt ((atOrd c i).trans hi)
    change E x (ord i)=E v (ord i) at q
    rwa [atOrd,atOrd] at q
  have ew (P : K[X]) : weightedEval (E c) (E v) P=E (weightedEval c v P) := by
    ext i
    change weightedEval (E c) (E v) P i=weightedEval c v P (ord.symm i)
    simp only [weightedEval_apply]
    rfl
  have rank := outgoing_nodal_gain (E c) (E v) (U.map E.toLinearMap) (Z.map E.toLinearMap) M
    chron mask (Submodule.map_mono sub) (by
      rintro _ ⟨x,hx,rfl⟩
      change M (E x)∈_
      rw [mE]
      exact Submodule.mem_map_of_mem (moves x hx)) r
    (count.trans (Finset.card_le_card nodes)) (by
      intro P hp
      rw [ew,ew,mE,formalPrimitive_eq_native,←map_sub]
      exact Submodule.mem_map_of_mem (paid P hp))
  rw [←(E.submoduleMap U).finrank_eq,←(E.submoduleMap Z).finrank_eq] at rank
  exact rank

end RKResearch.Certified.Graded

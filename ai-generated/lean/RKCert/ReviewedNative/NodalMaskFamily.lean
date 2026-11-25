module

public import RKCert.ReviewedNative.NonsingularNodalPackets
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # The actual finite independent masked family

The packet theorem is also a linearly independent list of the literal
polynomial-clock vectors. Its kth block consists of T^k applied to
the initial masked monomials within that block's paid degree bound.
-/

namespace RKResearch.Certified.Graded
open Module Polynomial
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- One block of the actual polynomial-masked family. -/
def maskedClockVectors (L : K[X] →ₗ[K] V) (P : K[X]) (q : ℕ) : List V :=
  List.ofFn (fun i : Fin (q+1) => L (P*X^i.val))

/-- The explicit list of all paid blocks, starting with the unadvanced
masked clock block. Repetitions, were they to exist, would remain in the
list and therefore cannot be hidden by changing to a finite set. -/
def maskedParityVectors (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V) (P : K[X]) (m : ℕ) :
    ℕ → List V
  | 0 => maskedClockVectors L P 0
  | 1 => maskedClockVectors L P (min 1 (m-2))
  | r+2 => maskedClockVectors L P (min (r+2) (m-1-(r+2))) ++
      (maskedParityVectors L T P m r).map T

theorem length_maskedParityVectors (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (P : K[X]) (m : ℕ) : ∀ r,
    (maskedParityVectors L T P m r).length = parityCensus m r
  | 0 => by simp only [maskedParityVectors,maskedClockVectors,List.length_ofFn,parityCensus]
  | 1 => by simp only [maskedParityVectors,maskedClockVectors,List.length_ofFn,parityCensus]
  | r+2 => by simp only [maskedParityVectors,maskedClockVectors,List.length_append,List.length_map,
      List.length_ofFn,length_maskedParityVectors L T P m r,parityCensus]

private theorem maskedClockVectors_span (L : K[X] →ₗ[K] V) (P : K[X]) (q : ℕ) :
    Submodule.span K {v : V | v ∈ maskedClockVectors L P q} = maskedPolyClockBand L P q := by
  classical
  let F : K[X] →ₗ[K] V := L.comp (LinearMap.mulLeft K P)
  let U : Finset K[X] := (Finset.range (q+1)).image (fun i => (X : K[X])^i)
  have hset : F '' (↑U : Set K[X]) = {v : V | v ∈ maskedClockVectors L P q} := by
    ext v
    constructor
    · rintro ⟨Q,hQ,rfl⟩
      change Q ∈ U at hQ
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hQ
      change _ ∈ List.ofFn _
      exact List.mem_ofFn.mpr ⟨⟨j,Finset.mem_range.mp hj⟩,rfl⟩
    · intro hv
      change v ∈ List.ofFn _ at hv
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
      exact ⟨(X : K[X])^j.val,Finset.mem_image.mpr ⟨j.val,Finset.mem_range.mpr j.isLt,rfl⟩,rfl⟩
  change _ = (degreeLT K (q+1)).map F
  rw [degreeLT_eq_span_X_pow,Submodule.map_span]
  exact congrArg (Submodule.span K) hset.symm

private theorem listSet_append (l₁ l₂ : List V) :
    {v : V | v ∈ l₁ ++ l₂} = {v : V | v ∈ l₁} ∪ {v : V | v ∈ l₂} := by
  ext v
  exact List.mem_append

private theorem listSet_map (T : V →ₗ[K] V) (l : List V) :
    {v : V | v ∈ l.map T} = T '' {v : V | v ∈ l} := by
  ext v
  exact List.mem_map

theorem span_maskedParityVectors (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (P : K[X]) (m : ℕ) : ∀ r,
    Submodule.span K {v : V | v ∈ maskedParityVectors L T P m r} =
      maskedParityPacket L T P m r
  | 0 => maskedClockVectors_span L P 0
  | 1 => maskedClockVectors_span L P (min 1 (m-2))
  | r+2 => by
      simp only [maskedParityVectors,maskedParityPacket,listSet_append,Submodule.span_union,
        maskedClockVectors_span,listSet_map,← Submodule.map_span,span_maskedParityVectors L T P m r]

theorem span_range_get_maskedParityVectors (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (P : K[X]) (m r : ℕ) :
    Submodule.span K (Set.range (maskedParityVectors L T P m r).get) =
      maskedParityPacket L T P m r := by
  have hset : Set.range (maskedParityVectors L T P m r).get =
      {v : V | v ∈ maskedParityVectors L T P m r} := by
    ext v
    exact List.mem_iff_get.symm
  rw [hset,span_maskedParityVectors]

variable [FiniteDimensional K V]

/-- Literal linear independence, including the original indexing of
the whole list. Together with its span equality this also gives a basis
of the invariant target whenever the cut rank is tight. -/
theorem linearIndependent_maskedParityVectors {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (sys : PaidPolyClockSystem L T E p)
    (P : K[X]) (hP : P ≠ 0) {m r : ℕ} (hscale : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    LinearIndependent K (maskedParityVectors L T P m r).get := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin (maskedParityVectors L T P m r).length) =
    finrank K (Submodule.span K (Set.range (maskedParityVectors L T P m r).get))
  calc
    Fintype.card (Fin (maskedParityVectors L T P m r).length) = parityCensus m r :=
      (Fintype.card_fin _).trans (length_maskedParityVectors L T P m r)
    _ = _ := by
      rw [span_range_get_maskedParityVectors, (maskedParityPacket_rank_and_le sys P hP hscale r hr).1]

end

section RK
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Actual columns R^k (P(x) ⊙ x^a) are independently indexed. -/
theorem nodalColumn_maskedIndependent (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (P : K[X]) (hP : P ≠ 0)
    {m r : ℕ} (hscale : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    LinearIndependent K (maskedParityVectors (nodalColumn A) (volterra A) P m r).get :=
  linearIndependent_maskedParityVectors (nodalColumn_paidSystem ho hR) P hP hscale hr

/-- Actual rows β P(C) C^a R^k are independently indexed. -/
theorem nodalRow_maskedIndependent (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (P : K[X]) (hP : P ≠ 0)
    {m r : ℕ} (hscale : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    LinearIndependent K (maskedParityVectors (nodalRow A b) (volterra A).dualMap P m r).get :=
  linearIndependent_maskedParityVectors (nodalRow_paidSystem ho hR) P hP hscale hr

end
end RK
end RKResearch.Certified.Graded

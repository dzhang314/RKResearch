module

public import RKCert.ReviewedNative.GradedPrefix
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Causal stage coalescing through an explicitly earned grade

A removed stage is redirected to its earlier representative only when
each needed native derivative column agrees there. No higher rooted
condition or stage-count bound is assumed by the merging lemma. -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {K : Type*} [Field K] {s n : ℕ}

def causalMergeMatrix (A : Matrix (Fin s) (Fin s) K) (e : Fin n→Fin s) (r : Fin s→Fin n) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => ∑ l ∈ Finset.univ.filter (fun l => r l=j), A (e i) l

theorem causalMerge_strict {A : Matrix (Fin s) (Fin s) K}
    (ha : ∀ i j,i≤j → A i j=0) {e : Fin n→Fin s} {r : Fin s→Fin n}
    (order : Monotone e) (previous : ∀ j,e (r j) ≤ j) :
    ∀ i j,i≤j → causalMergeMatrix A e r i j=0 := by
  intro i j ij
  apply Finset.sum_eq_zero
  intro l hl
  have eq := (Finset.mem_filter.mp hl).2
  apply ha
  exact (order ij).trans (eq ▸ previous l)

private theorem causalMerge_mat_value (A : Matrix (Fin s) (Fin s) K) (e : Fin n→Fin s)
    (r : Fin s→Fin n) (v : Fin s→K) (matchV : ∀ j, v (e (r j))=v j) (i : Fin n) :
    mat (causalMergeMatrix A e r) (fun t=>v (e t)) i = mat A v (e i) := by
  simp only [mat_apply,Matrix.mulVec,dotProduct,causalMergeMatrix]
  rw [← Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ) (g:=r)
    (fun j _=>Finset.mem_univ _) (fun j=>A (e i) j*v j)]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have eq := (Finset.mem_filter.mp hj).2
  rw [←eq,matchV]

/-- The preserved input budget is q+1 in tree order. At the kept rows
one additional root application is valid, giving q+2. -/
theorem Φ_causalMerge {A : Matrix (Fin s) (Fin s) K} {e : Fin n→Fin s} {r : Fin s→Fin n}
    {q : ℕ} (agree : ∀ v∈treeSpace A q, ∀ j,v (e (r j))=v j)
    (t : FiniteRootedTree) (pay : (t.order:ℕ)≤q+2) :
    Φ t (causalMergeMatrix A e r) = fun i=>Φ t A (e i) := by
  induction t with
  | leaf => rfl
  | butcherProduct u v ihu ihv =>
    have a := u.order.pos
    have b := v.order.pos
    have funds : (u.order:ℕ)+(v.order:ℕ)≤q+2 := by simpa only [order,PNat.add_coe] using pay
    rw [Φ,ihu (by omega),ihv (by omega)]
    ext i
    have last := causalMerge_mat_value A e r (Φ v A)
      (agree _ (Φ_mem_treeSpace A v (by omega))) i
    change Φ u A (e i)*mat (causalMergeMatrix A e r) (fun j=>Φ v A (e j)) i =
      Φ u A (e i)*mat A (Φ v A) (e i)
    rw [last]

/-- An existing clean physical receiver whose row is kept remains
clean at that new index, with exactly the same clock. -/
theorem clean_causalMerge {A : Matrix (Fin s) (Fin s) K} {e : Fin n→Fin s} {r : Fin s→Fin n}
    {q : ℕ} (agree : ∀ v∈treeSpace A q, ∀ j,v (e (r j))=v j) (i : Fin n)
    (clean : ∀v∈zeroSpace A (q+1), v (e i)=0) :
    nodes (causalMergeMatrix A e r) i = nodes A (e i) ∧
    ∀v∈zeroSpace (causalMergeMatrix A e r) (q+1), v i=0 := by
  let B := causalMergeMatrix A e r
  refine ⟨?_,?_⟩
  · have pay : ((.leaf ◂ .leaf : FiniteRootedTree).order : ℕ)≤q+2 := by
      simp only [order,PNat.add_coe,PNat.one_coe]
      omega
    have h := congrFun (Φ_causalMerge agree (.leaf ◂ .leaf) pay) i
    simpa [Φ,nodes] using h
  · change zeroSpace B (q+1) ≤ (LinearMap.proj i).ker
    apply Submodule.span_le.mpr
    rintro _ ⟨t,u,eOrder,ht,rfl⟩
    have hu : (u.order:ℕ)≤q+1+1 := by rwa [←eOrder]
    change normTree B t i - normTree B u i = 0
    dsimp only [B]
    simp only [normTree,Pi.smul_apply,Φ_causalMerge agree t (by omega),
      Φ_causalMerge agree u (by omega)]
    exact clean _ (normDiff_mem A t u eOrder ht)

end RKResearch.Certified.Graded

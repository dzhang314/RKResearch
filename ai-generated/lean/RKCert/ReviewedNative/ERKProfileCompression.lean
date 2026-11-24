module

public import RKCert.ReviewedNative.OddHorizon
public import RKCert.ReviewedNative.GradedPrefix
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Exact reviewed order survives chronological profile compression

No duplicate of the elementary weights is needed. Retain the first
physical occurrence of each external label and aggregate incoming and
output weights along those fibres. A label is usable whenever it already
identifies the actual reviewed elementary columns through the requested
order. -/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

private theorem sum_label_fibre {n : ℕ} (σ : Fin s→Fin n) (u : Fin n→K) (w : Fin s→K) :
    (∑ j, (∑ k : Fin s with σ k=j, w k)*u j) = ∑ k, w k*u (σ k) := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun k (_ : k ∈ (Finset.univ : Finset (Fin s))) => Finset.mem_univ (σ k))
      (fun k => w k*u (σ k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(Finset.mem_filter.mp hk).2]

/-- Earliest representatives carry a truly strictly lower reviewed
tableau, not only effective moment weights. Its stage count is exactly
the number of distinct physical labels. -/
theorem explicit_order_on_first_profiles {α : Type*} [DecidableEq α] (f : Fin s→α)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder A b p)
    (pref : ∀ i j, f i=f j → ∀ t : FiniteRootedTree, (t.order:ℕ)≤p → Φ t A i=Φ t A j) :
    ∃ (B : Matrix (Fin (Finset.univ.image f).card) (Fin (Finset.univ.image f).card) K)
      (w : Fin (Finset.univ.image f).card→K), (∀ i j,i ≤ j → B i j=0) ∧ HasOrder B w p := by
  classical
  let first (j : Fin s) := ∀ i, i < j → f i≠f j
  let S := Finset.univ.filter first
  let e := S.orderEmbOfFin rfl
  have repr (j : Fin s) : ∃ l : Fin S.card, e l≤j ∧ f (e l)=f j := by
    let T : Set (Fin s) := {i | f i=f j}
    obtain ⟨i,hi,imin⟩ := wellFounded_lt.has_min T ⟨j,rfl⟩
    have hfirst : first i := by
      intro k ki eq
      exact imin k (eq.trans hi) ki
    have mem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfirst⟩
    have ran : i ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact mem
    obtain ⟨l,rfl⟩ := ran
    exact ⟨l,le_of_not_gt (imin j rfl),hi⟩
  choose σ chronological label using repr
  have inj : Set.InjOn f (S : Set (Fin s)) := by
    intro i hi j hj eq
    have hfi := (Finset.mem_filter.mp hi).2
    have hfj := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with a|a|a
    · exact (hfj i a eq).elim
    · exact a
    · exact (hfi j a eq.symm).elim
  have image : S.image f=Finset.univ.image f := by
    apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.subset_univ S))
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨e (σ i),S.orderEmbOfFin_mem rfl _,label i⟩
  have card : S.card=(Finset.univ.image f).card := by
    rw [←image,Finset.card_image_of_injOn inj]
  let B : Matrix (Fin S.card) (Fin S.card) K :=
    fun i j => ∑ k : Fin s with σ k=j, A (e i) k
  let w : Fin S.card→K := fun j => ∑ k : Fin s with σ k=j, b k
  have strict : ∀ i j,i ≤ j → B i j=0 := by
    intro i j ij
    apply Finset.sum_eq_zero
    intro k hk
    have pre := chronological k
    rw [(Finset.mem_filter.mp hk).2] at pre
    exact ha _ _ ((e.monotone ij).trans pre)
  have φ (t : FiniteRootedTree) (paid : (t.order:ℕ)≤p) :
      Φ t B = Φ t A ∘ e := by
    induction t with
    | leaf => rfl
    | butcherProduct t u ht hu =>
      have htP : (t.order:ℕ)≤p := by simp only [order,PNat.add_coe] at paid; omega
      have huP : (u.order:ℕ)≤p := by simp only [order,PNat.add_coe] at paid; omega
      rw [Φ,Φ,ht htP,hu huP]
      ext i
      simp only [Pi.mul_apply, Function.comp_apply]
      congr 1
      rw [Matrix.mulVec_apply_eq_sum,Matrix.mulVec_apply_eq_sum]
      change (∑ j, (∑ k : Fin s with σ k=j, A (e i) k)*Φ u A (e j)) = _
      rw [sum_label_fibre]
      exact Finset.sum_congr rfl (fun k _=>congrArg (A (e i) k * ·) (pref _ _ (label k) u huP))
  have ord : HasOrder B w p := by
    intro t ht
    have dot : w ⬝ᵥ Φ t B=b ⬝ᵥ Φ t A := by
      rw [φ t ht,dotProduct,dotProduct]
      change (∑ j, (∑ k : Fin s with σ k=j, b k)*Φ t A (e j)) = _
      rw [sum_label_fibre]
      exact Finset.sum_congr rfl (fun k _=>congrArg (b k * ·) (pref _ _ (label k) t ht))
    rw [dot]
    exact ho t ht
  exact card ▸ ⟨B,w,strict,ord⟩

/-- If an exact nonzero receiver's paid input columns depend only on
a physical label, order five requires six distinct predecessor labels.
One may not count a repeated label as another predecessor. -/
theorem clean_five_receiver_profile_floor {α : Type*} [DecidableEq α]
    (ha : ∀ i j,i ≤ j → A i j=0) (i : Fin s) (nz : nodes A i≠0)
    (clean : ∀ v∈zeroSpace A 5,v i=0) (f : Fin i.val→α)
    (pref : ∀ j k, f j=f k → ∀ t : FiniteRootedTree, (t.order:ℕ)≤5 →
      Φ t A (Fin.castLE i.isLt.le j)=Φ t A (Fin.castLE i.isLt.le k)) :
    6≤(Finset.univ.image f).card := by
  let a := (nodes A i)⁻¹
  let h : i.val≤s := i.isLt.le
  let B := a • prefixMatrix A h
  let w : Fin i.val→K := fun j => a*A i (Fin.castLE h j)
  have e : HasOrder B w 5 := exact_receiver_prefix_order ha i 5 nz clean
  have sB : ∀ j k,j ≤ k → B j k=0 := by
    intro j k jk
    change a*(prefixMatrix A h) j k=0
    rw [prefix_strict_lower ha h j k jk,mul_zero]
  have pr (j k : Fin i.val) (eq : f j=f k) (t : FiniteRootedTree) (ht : (t.order:ℕ)≤5) :
      Φ t B j=Φ t B k := by
    simp only [B,Φ_smul,Φ_prefix ha,Pi.smul_apply,smul_eq_mul,prefixRestrict_apply]
    rw [pref j k eq t ht]
  obtain ⟨T,z,sT,order⟩ := explicit_order_on_first_profiles f sB e pr
  exact Reverse.odd_midpoint_floor sT order (q:=2) (by decide) (by decide)

end RKResearch.Certified.Graded

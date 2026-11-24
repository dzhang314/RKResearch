module

public import RKCert.CompanionWeightedMoment
public import RKCert.CompanionBidegree

@[expose] public section

/-! # Exact degree caps and coefficient-ring maps for the norm polynomials

The block Gram norm is used over the integer coefficient ring. Keeping
both columns of a Gram block avoids any division by a possibly singular
moment matrix. -/
namespace RKCert.Compound
open Polynomial Set Set.powersetCard
open scoped Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def rawGramMatrix {n k : ℕ} (M j w : ℕ) (u : R) (b : Fin (n+1)→R) :
    Matrix (powersetCard (Fin n) k ⊕ powersetCard (Fin n) k)
      (powersetCard (Fin n) k ⊕ powersetCard (Fin n) k) R :=
  Matrix.fromBlocks (rawMomentMatrix M j w u b) (rawMomentMatrix M (j+1) w u b)
    (rawMomentMatrix M (j+1) w u b) (rawMomentMatrix M (j+2) w u b)

def rawMomentNorm {n : ℕ} (k M j w : ℕ) (u : R) (b : Fin (n+1)→R) : R :=
  (rawMomentMatrix (k:=k) M j w u b).det

def rawGramNorm {n : ℕ} (k M j w : ℕ) (u : R) (b : Fin (n+1)→R) : R :=
  (rawGramMatrix (k:=k) M j w u b).det

theorem rawGramMatrix_map {n k : ℕ} (f : R→+*S) (M j w : ℕ) (u : R) (b : Fin (n+1)→R) :
    f.mapMatrix (rawGramMatrix (k:=k) M j w u b) =
      rawGramMatrix M j w (f u) (f ∘ b) := by
  apply Matrix.ext
  intro i t
  cases i <;> cases t <;> simp [rawGramMatrix,Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂]
  all_goals apply congrFun₂ (rawMomentMatrix_map (k:=k) f M _ w u b)

theorem rawMomentNorm_map {n : ℕ} (f : R→+*S) (k M j w : ℕ) (u : R) (b : Fin (n+1)→R) :
    f (rawMomentNorm k M j w u b)=rawMomentNorm k M j w (f u) (f ∘ b) := by
  rw [rawMomentNorm,rawMomentNorm,f.map_det,rawMomentMatrix_map]

theorem rawGramNorm_map {n : ℕ} (f : R→+*S) (k M j w : ℕ) (u : R) (b : Fin (n+1)→R) :
    f (rawGramNorm k M j w u b)=rawGramNorm k M j w (f u) (f ∘ b) := by
  rw [rawGramNorm,rawGramNorm,f.map_det,rawGramMatrix_map]

theorem det_column_cap {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I R[X]) (cap : I→ℕ)
    (good : ∀ i t,(A i t).natDegree≤cap t) :
    A.det.natDegree≤∑ t,cap t := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  exact (natDegree_smul_le _ _).trans ((natDegree_prod_le Finset.univ _).trans
    (Finset.sum_le_sum (fun t _ => good _ t)))

theorem rawMomentMatrix_degree {n k : ℕ} (M j w : ℕ) {u : R[X]} {U B : ℕ}
    (hd : u.natDegree≤U) (b : Fin (n+1)→R[X]) (bd : ∀ t,(b t).natDegree≤B)
    (i t : powersetCard (Fin n) k) :
    (rawMomentMatrix M j w u b i t).natDegree≤U*(k+w)+(if hasLast t then B else 0) := by
  unfold rawMomentMatrix scaledMoment
  apply natDegree_sum_le_of_forall_le
  intro r _
  have qc := coefficientCap_mul (constant_weight_coeff_cap (R:=R) w) (rawMinor_inner_cap b bd i t) r.val
  simp only [Nat.zero_add] at qc
  have up : (u^r.val).natDegree≤U*(k+w) := by
    apply natDegree_pow_le.trans
    rw [mul_comm r.val u.natDegree]
    exact Nat.mul_le_mul hd (Nat.le_of_lt_succ r.isLt)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (by rw [natDegree_natCast,Nat.zero_add]; exact up)) qc)

private def lastIndex (n : ℕ) (hn : 0<n) : Fin n := ⟨n-1,by omega⟩

private theorem hasLast_iff {n k : ℕ} (hn : 0<n) (t : powersetCard (Fin n) k) :
    hasLast t ↔ lastIndex n hn∈(t:Finset (Fin n)) := by
  rw [mem_coe_iff,←mem_range_ofFinEmbEquiv_symm_iff_mem]
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,Fin.ext ?_⟩
    have lt := (powersetCard.ofFinEmbEquiv.symm t i).isLt
    change (powersetCard.ofFinEmbEquiv.symm t i).val=n-1
    omega
  · rintro ⟨i,eq⟩
    refine ⟨i,?_⟩
    rw [eq]
    change ¬n-1+1<n
    omega

theorem count_last_subset {n k : ℕ} (hn : 0<n) (hk : 0<k) :
    Fintype.card {t : powersetCard (Fin n) k // hasLast t}=(n-1).choose (k-1) := by
  classical
  let a := lastIndex n hn
  let S : Finset (Finset (Fin n)) := (Finset.univ.powersetCard k).filter ({a}⊆·)
  let e : {t : powersetCard (Fin n) k // hasLast t} ≃ ↥S :=
    { toFun := fun t =>
        ⟨(t.1 : Finset (Fin n)),Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard_univ.mpr t.1.prop,
            Finset.singleton_subset_iff.mpr ((hasLast_iff hn t.1).mp t.2)⟩⟩
      invFun := fun t =>
        ⟨⟨t.1,Finset.mem_powersetCard_univ.mp (Finset.mem_filter.mp t.2).1⟩,
          (hasLast_iff hn _).mpr (Finset.singleton_subset_iff.mp (Finset.mem_filter.mp t.2).2)⟩
      left_inv := fun t => by rfl
      right_inv := fun t => by rfl }
  rw [Fintype.card_congr e,Fintype.card_coe]
  dsimp only [S]
  rw [Finset.card_filter_powersetCard_subset]
  · simp
  · exact Finset.subset_univ _
  · rwa [Finset.card_singleton]

theorem sum_column_caps {n k : ℕ} (hn : 0<n) (hk : 0<k) (U B w : ℕ) :
    (∑ t : powersetCard (Fin n) k,(U*(k+w)+(if hasLast t then B else 0)))=
      U*(k+w)*n.choose k+B*(n-1).choose (k-1) := by
  classical
  have total : Fintype.card (powersetCard (Fin n) k)=n.choose k := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
      (powersetCard.card (α:=Fin n) (n:=k))
  have count :
      (Finset.univ.filter (fun t : powersetCard (Fin n) k => hasLast t)).card=
        (n-1).choose (k-1) := by
    rw [←Fintype.card_subtype]
    exact count_last_subset hn hk
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,total,
    ←Finset.sum_filter,Finset.sum_const,count]
  simp only [nsmul_eq_mul,Nat.cast_id]
  ring

theorem rawMomentNorm_degree {n k : ℕ} (hn : 0<n) (hk : 0<k) (M j w : ℕ)
    {u : R[X]} {U B : ℕ} (hd : u.natDegree≤U) (b : Fin (n+1)→R[X])
    (bd : ∀ t,(b t).natDegree≤B) :
    (rawMomentNorm k M j w u b).natDegree≤U*(k+w)*n.choose k+B*(n-1).choose (k-1) := by
  unfold rawMomentNorm
  exact (det_column_cap _ _ (fun i t => rawMomentMatrix_degree M j w hd b bd i t)).trans_eq
    (sum_column_caps hn hk U B w)

theorem rawGramNorm_degree {n k : ℕ} (hn : 0<n) (hk : 0<k) (M j w : ℕ)
    {u : R[X]} {U B : ℕ} (hd : u.natDegree≤U) (b : Fin (n+1)→R[X])
    (bd : ∀ t,(b t).natDegree≤B) :
    (rawGramNorm k M j w u b).natDegree≤2*(U*(k+w)*n.choose k+B*(n-1).choose (k-1)) := by
  classical
  let cap (t : powersetCard (Fin n) k) := U*(k+w)+(if hasLast t then B else 0)
  have eq : (∑ t : powersetCard (Fin n) k ⊕ powersetCard (Fin n) k,Sum.elim cap cap t)=
      2*(U*(k+w)*n.choose k+B*(n-1).choose (k-1)) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr]
    change (∑ t,cap t)+(∑ t,cap t)=_
    rw [show (∑ t,cap t)=_ from sum_column_caps hn hk U B w,two_mul]
  rw [←eq]
  unfold rawGramNorm
  apply det_column_cap
  intro i t
  cases i <;> cases t <;> exact rawMomentMatrix_degree M _ w hd b bd _ _

end
end RKCert.Compound

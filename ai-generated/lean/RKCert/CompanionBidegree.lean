module

public import RKCert.CompanionClearedCompound

@[expose] public section

/-! # Column-sensitive coefficient-variable degree of compound minors -/
namespace RKCert.Compound
open Polynomial Set Set.powersetCard
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R]

/-- A uniform degree cap in the coefficient variable of an outer polynomial. -/
def coefficientCap (P : R[X][X]) (B : ℕ) : Prop :=
  ∀ d,(P.coeff d).natDegree≤B

theorem coefficientCap_mono {P : R[X][X]} {A B : ℕ} (h : coefficientCap P A) (r : A≤B) :
    coefficientCap P B := fun d => (h d).trans r

theorem coefficientCap_C {P : R[X]} {B : ℕ} (h : P.natDegree≤B) : coefficientCap (C P) B := by
  intro d
  by_cases e : d=0 <;> simp [coeff_C,e,h]

theorem coefficientCap_C_mul_X {P : R[X]} {B : ℕ} (h : P.natDegree≤B) :
    coefficientCap (C P*X) B := by
  intro d
  rw [coeff_C_mul_X]
  split_ifs <;> simp [h]

theorem coefficientCap_sub {P Q : R[X][X]} {B : ℕ}
    (p : coefficientCap P B) (q : coefficientCap Q B) : coefficientCap (P-Q) B := by
  intro d
  rw [coeff_sub]
  exact (natDegree_sub_le _ _).trans (max_le (p d) (q d))

theorem coefficientCap_add {P Q : R[X][X]} {B : ℕ}
    (p : coefficientCap P B) (q : coefficientCap Q B) : coefficientCap (P+Q) B := by
  intro d
  rw [coeff_add]
  exact (natDegree_add_le _ _).trans (max_le (p d) (q d))

theorem coefficientCap_mul {P Q : R[X][X]} {B D : ℕ}
    (p : coefficientCap P B) (q : coefficientCap Q D) : coefficientCap (P*Q) (B+D) := by
  intro d
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro a _
  exact natDegree_mul_le.trans (Nat.add_le_add (p a.1) (q a.2))

private theorem coefficientCap_one : coefficientCap (1:R[X][X]) 0 := by
  intro d
  rw [Polynomial.coeff_one]
  split_ifs <;> simp

private theorem coefficientCap_X : coefficientCap (X:R[X][X]) 0 := by
  intro d
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem coefficientCap_prod {I : Type*} (S : Finset I) (P : I→R[X][X]) (degree : I→ℕ)
    (h : ∀ i∈S,coefficientCap (P i) (degree i)) :
    coefficientCap (∏ i∈S,P i) (∑ i∈S,degree i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using (coefficientCap_one (R:=R))
  | insert a t hat ih =>
    rw [Finset.prod_insert hat,Finset.sum_insert hat]
    exact coefficientCap_mul (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem rawResolvent_inner_cap {n : ℕ} (b : Fin (n+1)→R[X]) {B : ℕ}
    (bh : ∀ t,(b t).natDegree≤B) (i j : Fin n) :
    coefficientCap (rawResolvent b i j) (if j.val+1<n then 0 else B) := by
  by_cases hj : j.val+1<n
  · unfold rawResolvent
    rw [ite_eq_left hj,ite_eq_left hj]
    apply coefficientCap_sub
    · split_ifs
      · exact coefficientCap_X
      · intro d
        simp
    · split_ifs
      · exact coefficientCap_one
      · intro d
        simp
  · unfold rawResolvent
    rw [ite_eq_right hj,ite_eq_right hj]
    apply coefficientCap_add _ (coefficientCap_C (bh i.castSucc))
    split_ifs
    · exact coefficientCap_C_mul_X (bh (Fin.last n))
    · intro d
      simp

theorem rawMinor_inner_cap {n k : ℕ} (b : Fin (n+1)→R[X]) {B : ℕ}
    (bh : ∀ t,(b t).natDegree≤B) (i j : powersetCard (Fin n) k) :
    coefficientCap (rawMinor b i j) (if hasLast j then B else 0) := by
  classical
  let r := powersetCard.ofFinEmbEquiv.symm i
  let c := powersetCard.ofFinEmbEquiv.symm j
  let d : Fin k→ℕ := fun t => if (c t).val+1<n then 0 else B
  have hd : (∑ t,d t)=(if hasLast j then B else 0) := by
    split_ifs with h
    · obtain ⟨t,ht⟩ := h
      rw [Finset.sum_eq_single t]
      · simp [d,c,ht]
      · intro z _ ne
        have lt : (c z).val+1<n := by
          by_contra hz
          exact ne (unique_last j hz ht)
        simp [d,lt]
      · simp
    · apply Finset.sum_eq_zero
      intro t _
      have lt : (c t).val+1<n := by
        by_contra ht
        exact h ⟨t,ht⟩
      simp [d,lt]
  rw [←hd]
  intro e
  unfold rawMinor
  rw [Matrix.det_apply,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have hprod : coefficientCap (∏ t,rawResolvent b (r (σ t)) (c t)) (∑ t,d t) :=
    coefficientCap_prod Finset.univ _ d (fun t _ => rawResolvent_inner_cap b bh _ _)
  change (((_ • ∏ t,rawResolvent b (r (σ t)) (c t)) : R[X][X]).coeff e).natDegree≤_
  rw [AddMonoidAlgebra.coeff_smul_apply]
  exact (natDegree_smul_le _ _).trans (hprod e)

theorem constant_weight_coeff_cap (w : ℕ) : coefficientCap ((1-X : R[X][X])^w) 0 := by
  have aux : coefficientCap (1-X : R[X][X]) 0 := by
    exact coefficientCap_sub coefficientCap_one coefficientCap_X
  induction w with
  | zero => simpa only [pow_zero] using (coefficientCap_one (R:=R))
  | succ w ih =>
    rw [pow_succ]
    simpa only [Nat.add_zero] using coefficientCap_mul ih aux

end
end RKCert.Compound

module
public import RKCert.ReverseHermiteRank
@[expose] public section

/-! # The two additional reflected primitive rows needed at the finite midpoint
The published order-twelve proof pays through the fourth reflected power.
Here the exact same beta identities are checked at the fifth and sixth powers.
-/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] {A:Fin s→Fin s→K} {b:Vec K s}

theorem finite_reflected5 (A:Fin s→Fin s→K) (b x:Vec K s) :
    row (reflWeight A b 5) x=probe A b 0 x - 5*probe A b 1 x + 10*probe A b 2 x - 10*probe A b 3 x + 5*probe A b 4 x - probe A b 5 x := by
  simp only [reflWeight,reflNode,row_apply,probe,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finite_reflected6 (A:Fin s→Fin s→K) (b x:Vec K s) :
    row (reflWeight A b 6) x=probe A b 0 x - 6*probe A b 1 x + 15*probe A b 2 x - 20*probe A b 3 x + 15*probe A b 4 x - 6*probe A b 5 x + probe A b 6 x := by
  simp only [reflWeight,reflNode,row_apply,probe,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option maxHeartbeats 3500000 in
theorem quartic_tree {p:ℕ} (ho:HasTreeOrderAtLeast A b p) (t:Tree) (hp:t.order+5≤p) :
    row (reflected A b 4) (normTree A t)=0 := by
  rw [reflected_apply,reflected_4,finite_reflected5]
  let d : K := t.order
  have h0 (i:ℕ) (hi:i≤5) :
      probe A b i (normTree A t)=(d+(i:K))⁻¹ := probe_norm_inv ho t i (by omega)
  have h1 (i:ℕ) (hi:i≤4) :
      probe A b i (mat A (normTree A t))=(d+(i+1:ℕ))⁻¹/d := by
    simpa only [d,Nat.cast_add,Nat.cast_one,add_right_comm _ (1:K),add_assoc] using
      probe_mat_norm_inv ho t i (by omega)
  have hden (i:ℕ) (hi:i≤5) : d+(i:K)≠0 := by
    change (t.order:K)+(i:K)≠0
    rw [←Nat.cast_add]
    exact cast_ne_zero_of_budget ho (Nat.add_pos_left t.order_pos i) (by omega)
  have h0' := hden 0 (by decide)
  have h1' := hden 1 (by decide)
  have h2' := hden 2 (by decide)
  have h3' := hden 3 (by decide)
  have h4' := hden 4 (by decide)
  have h5' := hden 5 (by decide)
  rw [h0 0 (by decide), h0 1 (by decide), h0 2 (by decide), h0 3 (by decide), h0 4 (by decide), h0 5 (by decide),
    h1 0 (by decide), h1 1 (by decide), h1 2 (by decide), h1 3 (by decide), h1 4 (by decide)]
  norm_num at h0' h1' h2' h3' h4' h5' ⊢
  field_simp
  ring

set_option maxHeartbeats 3500000 in
theorem quintic_tree {p:ℕ} (ho:HasTreeOrderAtLeast A b p) (t:Tree) (hp:t.order+6≤p) :
    row (reflected A b 5) (normTree A t)=0 := by
  rw [reflected_apply,finite_reflected5,finite_reflected6]
  let d : K := t.order
  have h0 (i:ℕ) (hi:i≤6) :
      probe A b i (normTree A t)=(d+(i:K))⁻¹ := probe_norm_inv ho t i (by omega)
  have h1 (i:ℕ) (hi:i≤5) :
      probe A b i (mat A (normTree A t))=(d+(i+1:ℕ))⁻¹/d := by
    simpa only [d,Nat.cast_add,Nat.cast_one,add_right_comm _ (1:K),add_assoc] using
      probe_mat_norm_inv ho t i (by omega)
  have hden (i:ℕ) (hi:i≤6) : d+(i:K)≠0 := by
    change (t.order:K)+(i:K)≠0
    rw [←Nat.cast_add]
    exact cast_ne_zero_of_budget ho (Nat.add_pos_left t.order_pos i) (by omega)
  have h0' := hden 0 (by decide)
  have h1' := hden 1 (by decide)
  have h2' := hden 2 (by decide)
  have h3' := hden 3 (by decide)
  have h4' := hden 4 (by decide)
  have h5' := hden 5 (by decide)
  have h6' := hden 6 (by decide)
  rw [h0 0 (by decide), h0 1 (by decide), h0 2 (by decide), h0 3 (by decide), h0 4 (by decide), h0 5 (by decide), h0 6 (by decide),
    h1 0 (by decide), h1 1 (by decide), h1 2 (by decide), h1 3 (by decide), h1 4 (by decide), h1 5 (by decide)]
  norm_num at h0' h1' h2' h3' h4' h5' h6' ⊢
  field_simp
  ring

theorem finite_reflected_annih {p k j:ℕ} (ho:HasTreeOrderAtLeast A b p) (hk:k≤5)
    (hp:j+k+2≤p) : reflected A b k∈annih (treeSpace A j) := by
  by_cases h:k≤3
  · exact reflected_annih ho h hp
  · interval_cases k
    · exact annih_of_norm ho (by omega) (fun t h=>quartic_tree ho t (by omega))
    · exact annih_of_norm ho (by omega) (fun t h=>quintic_tree ho t (by omega))

variable [CharZero K]

theorem reverse_primitive_annih_six {p:ℕ} (ho:HasTreeOrderAtLeast A b p)
    (j:ℕ) (hp:j+7≤p) (P:K[X]) (hP:P.natDegree≤5) :
    transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)
      ∈annih (treeSpace A j) := by
  let E := weightedEval (mirror A) b
  let D := (transMat A).comp E - E.comp formalPrimitiveLinear
  change D P ∈ _
  rw [P.as_sum_range' 6 (by omega),map_sum]
  apply (annih (treeSpace A j)).sum_mem
  intro k hk
  have hle : k≤5 := by have := Finset.mem_range.mp hk; omega
  let r := P.coeff k
  have hn : ((k+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hh := (annih (treeSpace A j)).smul_mem (r/((k+1:ℕ):K))
    (finite_reflected_annih ho hle (by omega))
  change transMat A (weightedEval (mirror A) b (monomial k r)) -
    weightedEval (mirror A) b (formalPrimitive (monomial k r))∈_
  rw [formalPrimitive_eq_treePrimitive,primitive_monomial,weighted_monomial,weighted_monomial,map_smul]
  convert hh using 1
  rw [reflected,smul_sub,smul_smul,div_mul_cancel₀ _ hn]

theorem mirror_moments_five {p:ℕ} (ho:HasTreeOrderAtLeast A b p)
    (hp:6≤p) (k:ℕ) (h1:1≤k) (h5:k≤5) :
    (∑ i,(mirror A i)^k*b i)=1/(k+1:ℕ) := by
  have sm (r:ℕ) : (∑i,(mirror A i)^r*b i)=row (reflWeight A b r) (1:Vec K s) := by
    simp only [row_apply,Pi.one_apply,mul_one,reflWeight,reflNode,mirror,Pi.sub_apply]
  have h (r:ℕ) (hr:r≤5) : probe A b r (1:Vec K s)=((1:K)+(r:K))⁻¹ := by
    simpa [normTree_leaf,Tree.order] using probe_norm_inv ho .leaf r (by change r+1≤p;omega)
  interval_cases k
  · exact (mirror_moments ho (by omega)).1
  · exact (mirror_moments ho (by omega)).2.1
  · exact (mirror_moments ho (by omega)).2.2
  · rw [sm,reflected_4,h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide)]
    norm_num
  · rw [sm,finite_reflected5,h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide),h 5 (by decide)]
    norm_num

theorem three_failed_of_five_moments (c v:Vec K s) (U:Submodule K (Vec K s))
    (hm:MaskInvariant c U) (mass:∀u∈U,∑i,u i=0)
    (e:∀ k:ℕ,1≤k→k≤5→(∑i,(c i)^k*v i)=1/(k+1:ℕ)) :
    3≤(failedNodes c v U s).card := by
  classical
  by_contra! hn
  let S:=failedNodes c v U s
  change S.card<3 at hn
  have xy : ∃ a b:K,S⊆{a,b} := by
    by_cases l:S.card≤1
    · obtain ⟨a,ha⟩:=Finset.card_le_one_iff_subset_singleton.mp l
      exact ⟨a,a,by simpa using ha⟩
    · obtain ⟨a,b,_,h⟩:=Finset.card_eq_two.mp (by omega : S.card=2)
      exact ⟨a,b,le_of_eq h⟩
  obtain ⟨a,b,hab⟩:=xy
  have hk (k:ℕ) (h0:1≤k) (h3:k≤3) :
      1/(k+2+1:ℕ)-(a+b)*(1/(k+1+1:ℕ))+a*b*(1/(k+1:ℕ))=0 := by
    let Q := X^k*(X-C a)*(X-C b)
    obtain ⟨w,hw,eq⟩:=exists_masked_prefix_lift c v hm s Q (by simp [Q,zero_pow (by omega : k≠0)])
      (fun z hz=>by
        have hh := hab hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hh
        rcases hh with h|h <;> simp [Q,h])
    have he := mass w hw
    have hc : (∑ i,(c i)^(k+2)*v i)-(a+b)*(∑ i,(c i)^(k+1)*v i)+a*b*(∑ i,(c i)^k*v i)=0 := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib,←he]
      apply Finset.sum_congr rfl
      intro i _
      rw [eq i i.isLt]
      simp only [Q,eval_mul,eval_X,eval_C,eval_sub,eval_pow,pow_add,pow_one]
      ring
    rwa [e (k+2) (by omega) (by omega),e (k+1) (by omega) (by omega),e k h0 (by omega)] at hc
  have h1:=hk 1 (by decide) (by decide)
  have h2:=hk 2 (by decide) (by decide)
  have h3:=hk 3 (by decide) (by decide)
  norm_num at h1 h2 h3
  apply (one_ne_zero : (1:K)≠0)
  linear_combination 180*h1-720*h2+600*h3

end RKCert.Paired.ReverseHull


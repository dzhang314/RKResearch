module
public import RKCert.DirkEvenJointSupport
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] {s m:ℕ}
noncomputable section

/-- A moment-annihilating signed physical vector pays twice for each of its
numerically distinct knots, unless there are already enough distinct knots.
This counts actual coordinates, never aggregate atoms or nominal nodes. -/
theorem signed_fiber_payment (y v:Vec K s) (k:ℕ) (hk:k≤(Clock.headSites y v).card)
    (mom:∀P:K[X],P.natDegree+2≤2*k → (∑i:Fin s,v i*P.eval (y i))=0) :
    2*k≤(Finset.univ.filter fun i=>v i≠0).card := by
  classical
  let I:=Finset.univ.filter fun i=>v i≠0
  let S:=I.image y
  change k≤S.card at hk
  change 2*k≤I.card
  by_cases big:2*k≤S.card
  · exact big.trans (Finset.card_image_le)
  have fiber (a:K) (ha:a∈S) : 2≤(I.filter fun t=>y t=a).card := by
    by_contra! small
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    have hvi:v i≠0:=(Finset.mem_filter.mp hi).2
    let T:=S.erase (y i)
    let P:=Lagrange.nodal T id
    have ndeg:P.natDegree+2≤2*k := by
      rw [show P.natDegree=T.card from Lagrange.natDegree_nodal,show T.card=S.card-1 from Finset.card_erase_of_mem ha]
      have pos:S.card≠0 := Finset.card_ne_zero.mpr ⟨_,ha⟩
      omega
    have pvi:P.eval (y i)≠0 := Lagrange.eval_nodal_not_at_node (fun z hz e=>by
      have ne:z≠y i:=(Finset.mem_erase.mp hz).1; exact ne e.symm)
    have zero (j:Fin s) (ne:j≠i) : v j*P.eval (y j)=0 := by
      by_cases vj:v j=0
      · simp [vj]
      have hIj:j∈I:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,vj⟩
      have yne:y j≠y i:=by
        intro eqn
        apply ne
        exact Finset.card_le_one.mp (by omega : (I.filter fun t=>y t=y i).card≤1)
          j (Finset.mem_filter.mpr ⟨hIj,eqn⟩) i (Finset.mem_filter.mpr ⟨hi,rfl⟩)
      have hT:y j∈T:=Finset.mem_erase.mpr ⟨yne,Finset.mem_image_of_mem y hIj⟩
      rw [show P.eval (y j)=0 from Lagrange.eval_nodal_at_node (v:=id) hT,mul_zero]
    have eqn:=mom P ndeg
    rw [Finset.sum_eq_single i (fun j _ h=>zero j h) (fun h=>False.elim (h (Finset.mem_univ _)))] at eqn
    exact mul_ne_zero hvi pvi eqn
  calc
    2*k≤2*S.card := by omega
    _ = ∑ _a∈S,2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a∈S,(I.filter fun t=>y t=a).card := Finset.sum_le_sum fiber
    _ = I.card := (Finset.card_eq_sum_card_image y I).symm

variable [CharZero K] {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem tau_polynomial_zero (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (P:K[X]) (hp:P.natDegree+4≤2*m) :
    (∑ i:Fin (s+1),tau A b i*P.eval (mirror A i))=0 := by
  have t:tau A b∈dirkBack A b 1 := (word_one hm ha ho he) ▸ Submodule.subset_span (Set.mem_singleton _)
  have mem:=evalNodes_mem_treeSpace A (reflectPolynomial P) (reflectPolynomial_degree P)
  have h:=mem_annih.mp (dirkBack_annih ho P.natDegree 1 (by omega) t) _ mem
  simpa only [row_apply,evalNodes_apply,reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X,mirror,Pi.sub_apply,Pi.one_apply] using h

theorem dirty_stage_count (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) :
    2*(m-1)≤(Finset.univ.filter fun i=>tau A b i≠0).card :=
  signed_fiber_payment _ _ _ (nonlocal_sites hm ha ho he (even_reverse_nonlocal hm ha ho he))
    (fun P hd=>tau_polynomial_zero hm ha ho he P (by omega))

theorem clean_active_budget (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) :
    (Finset.univ.filter fun i=>b i≠0 ∧ tau A b i=0).card≤m-2 := by
  classical
  let D:=Finset.univ.filter fun i=>tau A b i≠0
  let C:=Finset.univ.filter fun i=>b i≠0 ∧ tau A b i=0
  obtain ⟨i,_,bi,ti,_⟩:=exists_hidden_stage hm ha ho he
  have hd:Disjoint D C:=Finset.disjoint_left.mpr (fun j hd hc=>(Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp hc).2.2)
  have le:D ∪ C⊆Finset.univ.erase i:=by
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    rintro rfl
    rcases Finset.mem_union.mp hj with h|h
    · exact (Finset.mem_filter.mp h).2 ti
    · exact (Finset.mem_filter.mp h).2.1 bi
  have total:=Finset.card_le_card le
  rw [Finset.card_union_of_disjoint hd,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin] at total
  have dirty:2*(m-1)≤D.card:=dirty_stage_count hm ha ho he
  change C.card≤m-2
  omega
end
end RKCert.Paired.Terminal

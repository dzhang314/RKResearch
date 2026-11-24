module

public import RKCert.Dirk15K2GoodSignatures

@[expose] public section

/-! # The visible two-core quartic is an actual factor of the common pencil -/
namespace RKCert.Paired.Signature
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {n : ℕ}

set_option maxHeartbeats 1400000 in
theorem two_value_signature_factor (c v : Fin n → K) (D P R : K[X])
    (arg : D.natDegree+(D-P*R).natDegree<n)
    (nz : D≠0) (inj : Function.Injective (fun i => (c i,v i)))
    (relation : ∀ i,D.eval (c i)=v i*R.eval (c i))
    (values : ∀ i,v i=0 ∨ v i=P.eval (c i)) : D=P*R := by
  have cap (a : K) : (fiberAt c a).card≤2 := by
    let B := fiberAt c a
    have vi : Set.InjOn v (B:Set (Fin n)) := by
      intro i hi j hj eq
      have c1 : c i=a := (Finset.mem_filter.mp hi).2
      have c2 : c j=a := (Finset.mem_filter.mp hj).2
      exact inj (Prod.ext (c1.trans c2.symm) eq)
    have s : B.image v⊆({0,P.eval a}:Finset K) := by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have e : c i=a := (Finset.mem_filter.mp hi).2
      rcases values i with r|r <;> simp [r,e]
    have z := Finset.card_le_card s
    rw [Finset.card_image_of_injOn vi] at z
    exact z.trans ((Finset.card_insert_le 0 {P.eval a}).trans_eq (by simp))
  have f (i : Fin n) : D.eval (c i)*(D-P*R).eval (c i)=0 := by
    rw [eval_sub,eval_mul,relation]
    rcases values i with eq|eq <;> simp [eq]
  have both (i j : Fin n) (ne : i≠j) (eq : c i=c j) :
      D.eval (c i)=0 ∧ (D-P*R).eval (c i)=0 := by
    have w : v i≠v j := fun h => ne (inj (Prod.ext eq h))
    have d := relation j
    rw [←eq] at d
    have x := values j
    rw [←eq] at x
    rcases values i with a|a <;> rcases x with b|b
    · exact (w (a.trans b.symm)).elim
    · have e := relation i
      rw [a,zero_mul] at e
      rw [b] at d
      exact ⟨e,by rw [eval_sub,eval_mul,d,sub_self]⟩
    · have e := relation i
      rw [a] at e
      rw [b,zero_mul] at d
      exact ⟨d,by rw [eval_sub,eval_mul,e,sub_self]⟩
    · exact (w (a.trans b.symm)).elim
  exact sub_eq_zero.mp ((mul_eq_zero.mp (counted_factors_zero c D (D-P*R) arg cap f both)).resolve_left nz)

end
end RKCert.Paired.Signature

namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b v : Vec K 20}

namespace Order15K2Head
variable (h : Order15K2Head A b v) (D : h.head.DeletedPencil)

structure TrueVisibleFactor where
  P : K[X]
  R : K[X]
  nonzero : P≠0
  degree : P.natDegree≤4
  factor : D.D=P*R
  matchMark : ∀ i : Fin 20, reverseCubic A b i≠0 → v i=P.eval (nodes A i)
  weighted_good : ∀ i : Fin 20,i≠Fin.last 19 → nodes A i≠1 → b i≠0 →
    D.D.eval (nodes A i)=v i*R.eval (nodes A i)

set_option maxHeartbeats 2100000 in
theorem actual_visible_factor (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (hm : finrank K (marked A 15 4)=2) :
    Nonempty (h.TrueVisibleFactor D) := by
  let c := nodes A
  obtain ⟨R,rd,sg,act⟩ := h.actual_good_signatures D ha ho H
  obtain ⟨Q,dQ,mp,clean⟩ := order15_grade_four_profile ha ho H hm
    (order15_minimal_reverse_nonlocal ha ho H) h.paid
  let P := reflectPolynomial Q
  have dP : P.natDegree≤4 := (reflectPolynomial_degree Q).trans dQ
  have matchP (i : Fin 20) (nz : reverseCubic A b i≠0) : v i=P.eval (c i) := by
    change v i=(reflectPolynomial Q).eval (nodes A i)
    rw [reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X]
    exact mp i nz
  have vals (i : Fin 20) (gi : i∉ghostPositions A b) :
      v i=0 ∨ v i=P.eval (c i) := by
    by_cases z : v i=0
    · exact Or.inl z
    · refine Or.inr (matchP i (fun ti => ?_))
      apply z
      by_cases bi : b i≠0
      · exact clean i bi ti
      · by_cases i0 : i=0
        · rw [i0]
          exact zeroSpace_first_of_row H.initial.first_zero 4 h.paid
        · exact (gi (mem_ghostPositions.mpr ⟨i0,not_ne_iff.mp bi,ti⟩)).elim
  have dn : D.D≠0 := by
    intro z
    have e := D.dmin
    rw [z,natDegree_zero] at e
    contradiction
  let S := h.goodSignatures D R
  obtain ⟨idx,inj,mem,_⟩ := finset_enum S
  have fits (i : Fin S.card) :
      D.D.eval (idx i).1=(idx i).2*R.eval (idx i).1 ∧
      ((idx i).2=0 ∨ (idx i).2=P.eval (idx i).1) := by
    have k : idx i∈h.goodSignatures D R := mem i
    obtain ⟨j,z,sig⟩ := Finset.mem_image.mp k
    rw [←sig]
    obtain ⟨jt,je⟩ := Finset.mem_filter.mp z
    exact ⟨je,vals j (mem_retainedNonghostPositions.mp jt).2⟩
  have bd : D.D.natDegree+(D.D-P*R).natDegree<S.card := by
    have m := D.dmax
    have e : (D.D-P*R).natDegree≤8 := (natDegree_sub_le _ _).trans
      (max_le m (natDegree_mul_le.trans (by omega)))
    change 17≤S.card at sg
    omega
  have fac := Signature.two_value_signature_factor (fun i=>(idx i).1) (fun i=>(idx i).2)
    D.D P R bd dn inj (fun i=>(fits i).1) (fun i=>(fits i).2)
  exact ⟨⟨P,R,fun z=>dn (by rw [fac,z,zero_mul]),dP,fac,matchP,act⟩⟩

end Order15K2Head
end
end RKCert.Paired

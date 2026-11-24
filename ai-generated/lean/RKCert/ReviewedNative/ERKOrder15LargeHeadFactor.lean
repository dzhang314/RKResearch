module

public import RKCert.ReviewedNative.ERKOrder15PhysicalCore

@[expose] public section

/-! # The hypothetical large head gives an actual divisor of the mesh
No endpoint arithmetic or root-splitting assumption is used. The next
physical knot obstruction can consume this cubic-or-smaller factor. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a r : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

private theorem weighted_eval_in_chain {c v : Fin (s+1)→K} {n : ℕ} (P : K[X]) (d : P.natDegree < n) :
    weightedEval c v P∈chain (diag c) U v n := by
  have h := (clock_chain_le_iff (T:=diag c) (U:=U) (w:=v) n).mp le_rfl
  rw [P.as_sum_range' n d,map_sum]
  apply (chain (diag c) U v n).sum_mem
  intro j hj
  have eq : weightedEval c v (monomial j (P.coeff j))=P.coeff j • (diag c^j) v := by
    ext i
    simp [mul_assoc]
  rw [eq]
  exact (chain (diag c) U v n).smul_mem _ (h.2 j (Finset.mem_range.mp hj))

private theorem head_squares_paid (S : Order15PaidStaircase A b a G r U w)
    (k : ℕ) (cap : k≤2*r-2) :
    (diag (nodes A)^k) (w*w)∈markedDefectSpace A b 10 := by
  let D := diag (nodes A)
  let f := min k (r-1)
  let g := k-f
  have fk : f≤k := min_le_left _ _
  have fr : f≤r-1 := min_le_right _ _
  have r2 := S.headLength
  have gr : g < r := by dsimp [g,f];omega
  have e : f+g=k := by dsimp [g];omega
  have e5 := S.early 0 (by decide)
  change markedDefectSpace A b 5=chain D U w r at e5
  have m := (clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp e5.ge
  have fit : (D^k) (w*w)=((D^f) w)*((D^g) w) := by
    ext i
    simp only [D,HeadFiber.clock_power_value,Pi.mul_apply]
    rw [←e,pow_add]
    ring
  change (D^k) (w*w)∈_
  rw [fit]
  exact marked_defect_mul (j:=5) (k:=5) (m.2 f (by omega)) (m.2 g gr)

/-- The paid staircase forces a genuine polynomial multiplier for a
hypothetical large physical head. The square shifts are not assumed. -/
theorem Order15PaidStaircase.large_head_profile (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b) (large : 3≤r) :
    ∃ (v : Fin (s+1)→K) (P : K[X]), Order15PaidStaircase A b a G r U v ∧
      (∀ i, (∃ u∈U,u i≠0) → v i=0) ∧ P≠0 ∧ P.natDegree+2*r-2<order15HeadLength a r 10 ∧
      (∀ i,v i≠0 → v i=P.eval (nodes A i)) := by
  obtain ⟨v,S,dis,_⟩:=S.clean_head ha ho
  let D := diag (nodes A)
  let N := 2+terminalDebit A b
  have balance := terminalDebit_balance A b
  have Nc : N≤2*r-2 := by dsimp [N];omega
  have squares (k : ℕ) (hk : k≤2*r-2) :
      (D^k) (v*v)∈order15HeadBand A a r 10 U v := by
    let j := min k (2*r-2-N)
    have jk : j≤k := min_le_left _ _
    have jb : j≤2*r-2-N := min_le_right _ _
    have win : k-j≤N := by dsimp [j];omega
    have row (i : ℕ) (ip : i≤N) : (D^i) ((D^j) (v*v))∈markedDefectSpace A b 10 := by
      rw [←LinearMap.comp_apply,←Module.End.mul_eq_comp,←pow_add]
      exact head_squares_paid S _ (by omega)
    have h := S.ten_leak_free_all ha ho row (k-j) win
    rw [←LinearMap.comp_apply,←Module.End.mul_eq_comp,←pow_add,show k-j+j=k by omega] at h
    exact h
  have n := S.ten_has_escape_sites ho
  have many : order15HeadLength a r 10 < (HeadFiber.physicalSites (nodes A) v).card :=
    n.trans_le (Finset.card_le_card HeadFiber.escape_le_physical)
  obtain ⟨P,pd,repr⟩:=HeadFiber.multiplier_polynomial (a:=v) (d:=2*r-2) dis many squares
  have hn : P≠0 := by
    intro eq
    obtain ⟨x,hm⟩:=Finset.card_pos.mp (show 0<(HeadFiber.physicalSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hm
    have z := (Finset.mem_filter.mp hi).2
    exact z (by rw [repr _ z,eq,eval_zero])
  have pd' := pd.resolve_left hn
  exact ⟨v,P,S,dis,hn,by omega,repr⟩

/-- Actual large-head factorization. Since r ≥ 3, the physical multiplier
has degree at most three. No algebraic or numerical exclusion of that
remaining factor is assumed by this declaration. -/
theorem Order15PaidStaircase.large_head_factor (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b) (large : 3≤r) :
    ∃ (v : Fin (s+1)→K) (P Q : K[X]), Order15PaidStaircase A b a G r U v ∧
      (∀ i, (∃ u∈U,u i≠0) → v i=0) ∧ P≠0 ∧ P.natDegree≤3 ∧ G=P*Q ∧
      Q.natDegree=r+2 ∧ P.natDegree+r+1=a ∧ (∀ i,v i≠0 → v i=P.eval (nodes A i)) := by
  obtain ⟨v,P,S,dis,pn,pd,repr⟩:=S.large_head_profile ha ho large
  let T := HeadFiber.physicalSites (nodes A) v
  have many : order15HeadLength a r 10 < T.card :=
    (S.ten_has_escape_sites ho).trans_le (Finset.card_le_card HeadFiber.escape_le_physical)
  have gd := S.first.degree
  have aa := S.base_degree
  have gn : G≠0 := by intro e; rw [e,natDegree_zero] at gd; omega
  obtain ⟨u,hu,Q,qdeg,e⟩ := HeadFiber.exists_poly (S.escape ▸ S.first.paid)
  have qd : Q.natDegree≤r+2 := by
    by_cases z : Q=0
    · simp [z]
    · have t := (natDegree_lt_iff_degree_lt z).mpr qdeg
      omega
  have de := natDegree_mul_le (p:=P) (q:=Q)
  unfold order15HeadLength at pd many
  have eq : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq T
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show G.natDegree<T.card by omega))
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Q).natDegree<T.card by omega))
    · intro x hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
      have v0 := (Finset.mem_filter.mp hi).2
      have u0 : u i=0 := by by_contra z; exact v0 (dis _ ⟨u,hu,z⟩)
      have h := congrFun e i
      simpa only [evalNodes_apply,Pi.add_apply,weightedEval_apply,u0,zero_add,repr i v0,eval_mul,mul_comm] using h
  have qn : Q≠0 := fun z=>gn (by rw [eq,z,mul_zero])
  have ps := congrArg Polynomial.natDegree eq
  rw [gd,natDegree_mul pn qn] at ps
  have qexact : Q.natDegree=r+2 := by
    by_cases az : a=7
    · omega
    by_contra qe
    have fit : Q.natDegree < r+2 := by omega
    have mem : evalNodes A G∈markedDefectSpace A b 7 := by
      have early := S.early 2 (by decide)
      rw [early,e]
      exact (chain (diag (nodes A)) U v (r+2)).add_mem
        (((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=v) (r+2)).mp le_rfl).1 hu)
        (weighted_eval_in_chain Q fit)
    exact gn (eval_eq_zero_of_coeff_separated
      (marked_coeff_separated ha ho S.frame.lastActive (by have := S.frame.size;omega)
        (q:=7) (j:=7) (by decide) (by decide)) G (by omega) mem)
  exact ⟨v,P,Q,S,dis,pn,by omega,eq,qexact,by omega,repr⟩

end
end RKResearch.Certified.Graded

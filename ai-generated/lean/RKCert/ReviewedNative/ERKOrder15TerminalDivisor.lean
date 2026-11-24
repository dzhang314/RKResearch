module

public import RKCert.ReviewedNative.ERKOrder15PaidTerminalSquares

@[expose] public section

/-! # The actual rank-two terminal head divides the same paid mesh -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G P : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

structure Order15TerminalDivisor (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1)→K) (a : ℕ) (U : Submodule K (Fin (s+1)→K))
    (w : Fin (s+1)→K) (G P : K[X]) : Prop where
  chart : Order15PaidStaircase A b a G 2 U w
  disjoint : ∀ i, LiveCore.live U i → w i=0
  repr : ∀ i,w i≠0 → w i=P.eval (nodes A i)
  nonzero : P≠0
  divides : P∣G
  degree : P.natDegree+3=a

private theorem physical_sites_after_eleven (S : Order15PaidStaircase A b a G 2 U w)
    (ho : HasOrder 15 A b) :
    order15HeadLength a 2 11<(HeadFiber.physicalSites (nodes A) w).card := by
  have ab := S.base_degree
  have dim11 := (S.band_direct_rank ho (j:=11) (by omega) (by decide)).2
  have dim12 := (S.band_direct_rank ho (j:=12) (by omega) (by decide)).2
  have len : order15HeadLength a 2 12=order15HeadLength a 2 11+1 := by
    unfold order15HeadLength;omega
  have no : ¬ (order15HeadBand A a 2 11 U w).map (diag (nodes A))≤order15HeadBand A a 2 11 U w := by
    intro inv
    have step := (S.band_next (j:=11) (by omega)).symm.trans (sup_eq_left.mpr inv)
    rw [step,dim11,len] at dim12
    omega
  exact (HeadFiber.more_escape_sites S.stable (by unfold order15HeadLength;omega) no).trans_le
    (Finset.card_le_card HeadFiber.escape_le_physical)

/-- The two square shifts give a genuine divisor, of degree four in
the variable pencil and degree three in the fixed alias. -/
theorem Order15PaidStaircase.actual_terminal_divisor [CharZero K]
    (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (seed : firstSeed A b=0) (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8) :
    ∃ (v : Fin (s+1)→K) (P : K[X]), Order15TerminalDivisor A b a U v G P := by
  obtain ⟨v,T,dis,_⟩ := S.clean_head ha ho
  have hs := T.three_terminal_squares ha ho seed term dis
  let M := HeadFiber.physicalSites (nodes A) v
  have many : order15HeadLength a 2 11<M.card := physical_sites_after_eleven T ho
  have cap : order15HeadLength a 2 10<M.card := by
    unfold order15HeadLength at many ⊢
    omega
  obtain ⟨P,d,repr⟩ := HeadFiber.multiplier_polynomial (a:=v) (d:=2) dis cap hs
  have pn : P≠0 := by
    intro z
    obtain ⟨_,h⟩ := Finset.card_pos.mp (show 0<M.card by omega)
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp h
    have vn := (Finset.mem_filter.mp hi).2
    exact vn (by rw [repr i vn,z,eval_zero])
  have pd := d.resolve_left pn
  have ab := T.base_degree
  have gd := T.first.degree
  have gn : G≠0 := fun z=>by rw [z,natDegree_zero] at gd;omega
  obtain ⟨u,hu,Q,qsmall,e⟩ := HeadFiber.exists_poly (T.escape ▸ T.first.paid)
  have qd : Q.natDegree≤4 := by
    by_cases z : Q=0
    · simp [z]
    · have h := (natDegree_lt_iff_degree_lt z).mpr qsmall
      omega
  have prod := natDegree_mul_le (p:=P) (q:=Q)
  unfold order15HeadLength at pd many
  have eq : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq M
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show G.natDegree<M.card by omega))
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Q).natDegree<M.card by omega))
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have vn := (Finset.mem_filter.mp hi).2
      have u0 : u i=0 := by by_contra z;exact vn (dis i ⟨u,hu,z⟩)
      have z := congrFun e i
      simpa only [evalNodes_apply,Pi.add_apply,weightedEval_apply,u0,zero_add,repr i vn,
        eval_mul,mul_comm] using z
  have qn : Q≠0 := fun z=>gn (by rw [eq,z,mul_zero])
  have sum := congrArg natDegree eq
  rw [gd,natDegree_mul pn qn] at sum
  have qexact : Q.natDegree=4 := by
    by_cases ae : a=7
    · omega
    by_contra no
    have f7 : markedDefectSpace A b 7=chain (diag (nodes A)) U v 4 := T.early 2 (by decide)
    have u7 : u∈markedDefectSpace A b 7 := f7.symm ▸ ((clock_chain_le_iff _).mp le_rfl).1 hu
    have q7 : weightedEval (nodes A) v Q∈markedDefectSpace A b 7 := by
      apply weighted_eval_mem_of_powers (m:=3) ?_ Q (by omega)
      intro k hk
      rw [f7]
      exact ((clock_chain_le_iff _).mp le_rfl).2 k (by omega)
    have pay : evalNodes A G∈markedDefectSpace A b 7 :=
      e.symm ▸ (markedDefectSpace A b 7).add_mem u7 q7
    exact gn (eval_eq_zero_of_coeff_separated
      (marked_coeff_separated ha ho T.frame.lastActive (by have := T.frame.size;omega)
        (q:=7) (j:=7) (by decide) (by decide)) G (by omega) pay)
  exact ⟨v,P,T,dis,repr,pn,⟨Q,eq⟩,by omega⟩

end
end RKResearch.Certified.Graded

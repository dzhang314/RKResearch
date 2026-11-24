module
public import RKCert.DirkCleanTracePivot
public import RKCert.DirkEvenMarked
public import RKCert.LobattoFactors
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
variable {K : Type*} [Field K] [CharZero K] {s m j : ℕ}
variable {A : Fin (s+1) → Fin (s+1) → K} {b θ : Vec K (s+1)} {P : K[X]}
noncomputable section

/-- Every actually midpoint-clean row other than the chronological last lies on
the native Lobatto grid. The last row and its cardinal are earned by the
tableau, so there is no endpoint relabelling or assumed terminal index. -/
theorem lobatto_zero_of_clean_nonlast (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    {i : Fin (s+1)} (nonlast : i≠Fin.last s) (clean : ∀ f∈zeroSpace A m, f i=0) :
    (lobatto m).eval (nodes A i)=0 := by
  have lo : 7≤m := by rcases hm with rfl|rfl|rfl|rfl <;>decide
  obtain ⟨origin,_⟩:=even_boundary lo ha ho he
  obtain ⟨_,node,_,card,lastclean⟩:=last_physical lo ha ho he
  have orig : nodes A 0=0 := by simp [nodes,origin]
  obtain ⟨mom,atOne⟩:=lobatto_fixed (K:=K) hm
  obtain ⟨_,_,roots⟩:=lobatto_tableau ho (by omega) (by omega) 0 (Fin.last s)
    orig node (fun _ hf=>zeroSpace_first_of_row origin m hf) lastclean card mom atOne
  exact roots i nonlast clean

/-- The direct p14/p16 physical head-factor exclusion. The only additional
data are the genuine trace, its paid grade, and actual midpoint cleanliness
on its support. A nonterminal supported coordinate, the chronological pivot,
a zero pivot diagonal, a primitive payment, a nonzero grid root and the
factor degree bound are all derived. -/
theorem no_clean_head_lobatto_factor (hm : m=7 ∨ m=8)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (tr : OrdinaryTrace A j θ (X*P)) (pay : j+2≤m) (fact : P ∣ lobatto m)
    (clean : ∀ i : Fin (s+1), θ i≠0 → ∀ f∈zeroSpace A m, f i=0) : False := by
  have fixed : m=7 ∨ m=8 ∨ m=9 ∨ m=10 := hm.imp_right Or.inl
  have lo : 7≤m := by rcases hm with rfl|rfl <;>decide
  have dn : (lobatto (K:=K) m).natDegree=m := by
    rcases hm with rfl|rfl
    · exact FixedFactor.degree_lobatto7
    · exact FixedFactor.degree_lobatto8
  have ng : lobatto (K:=K) m≠0 := fun e=>by rw [e,natDegree_zero] at dn;omega
  have nz : P≠0 := ne_zero_of_dvd_ne_zero ng fact
  have bound:=tr.degree
  rw [natDegree_X_mul nz] at bound
  have hmult:=natDegree_mul_le (p:=X*P) (q:=X-C (1:K))
  rw [natDegree_X_mul nz,natDegree_X_sub_C] at hmult
  obtain ⟨k,_,hk,away⟩:=tr.exists_weighted_active_outside_roots ho (mul_ne_zero X_ne_zero nz)
    (X-C 1) (X_sub_C_ne_zero _) (by rw [natDegree_X_sub_C];omega)
  obtain ⟨_,lastClock,_,_,_⟩:=last_physical lo ha ho he
  have early : k<Fin.last s := lt_of_le_of_ne (Fin.le_last k) (fun e=>by
    apply away
    simp [e,lastClock])
  have ne : θ≠0 := fun z => hk (by rw [z];rfl)
  obtain ⟨i,hi,before⟩:=exists_first_coordinate ne
  have ilast : i≠Fin.last s := fun e=>hk (before k (e ▸ early))
  have ci:=clean i hi
  have nod := lobatto_zero_of_clean_nonlast fixed ha ho he ilast ci
  have eqn:=ci _ (zeroSpace_mono A (show j≤m by omega) tr.pure)
  have vx : θ i=nodes A i * P.eval (nodes A i) := by
    simpa only [Pi.sub_apply,evalNodes_apply,eval_mul,eval_X,sub_eq_zero] using eqn
  have active : nodes A i≠0 := fun z=>hi (by rw [vx,z,zero_mul])
  have prim:=(tr.primitive_zero_at_first_clean ha ho (by omega) pay hi before ci).2
  rcases hm with rfl|rfl
  · exact FixedFactor.lobatto7_first_moment fact (by omega) active nod prim
  · exact FixedFactor.lobatto8_first_moment fact (by omega) active nod prim


/-- A physical interpolation form avoiding any need for the caller to
construct a trace: if a paid defect agrees with P(c) on every row where
any midpoint defect is nonzero, subtract it and multiply by the genuine
stage clock to get the excluded clean trace. No condition is required on
the value of the defect at clean rows. -/
theorem no_lobatto_factor_mask_on_dirty (hm : m=7 ∨ m=8)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (fact : P ∣ lobatto m) (dp : P.natDegree≤j) (pay : j+3≤m)
    {w : Vec K (s+1)} (hw : w∈zeroSpace A j)
    (mask : ∀ i, (∃ f∈zeroSpace A m, f i≠0) → w i=P.eval (nodes A i)) : False := by
  let t:=evalNodes A P-w
  have raw : OrdinaryTrace A j t P := (OrdinaryTrace.scalar A dp).sub_pure hw
  apply no_clean_head_lobatto_factor hm ha ho he raw.clock (by omega) fact
  intro i act f hf
  by_contra hn
  apply act
  have atrow:=mask i ⟨f,hf,hn⟩
  simp [diag_apply,t,atrow]

end
end RKCert.Paired.Terminal

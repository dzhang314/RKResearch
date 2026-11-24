module
public import RKCert.ERKShortReverseHull
public import RKCert.ERKEightPureContrast

@[expose] public section

/-! # True chronological ports for the difference of two thin traces

No off-hull tableau is constructed. The proof checks the actual primitive
and transpose pairings on the original complement, then reads its first
two distinct active physical ports in backwards chronology. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K] {s p m:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

def reverseContrast (A:Fin s→Fin s→K) (b:Vec K s) (Q P:K[X]) : Vec K s :=
  weightedEval (mirror A) b (X*Q)-weightedEval (mirror A) (backSeed2 A b) P

omit [CharZero K] in
theorem reverseContrast_weighted (Q P R:K[X]) :
    weightedEval (mirror A) (reverseContrast A b Q P) R =
      weightedEval (mirror A) b (R*(X*Q))-weightedEval (mirror A) (backSeed2 A b) (R*P) := by
  ext i
  simp only [reverseContrast,weightedEval_apply,Pi.sub_apply,eval_mul]
  ring

omit [CharZero K] in
theorem seed_eval_annih (ho:HasTreeOrderAtLeast A b p) (P:K[X])
    (pay:m+P.natDegree+3≤p) :
    weightedEval (mirror A) (backSeed2 A b) P∈annih (treeSpace A m) := by
  have e:ofFn (P.natDegree+1) (toFn _ P)=P:=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  apply seed_band_annih ho m (P.natDegree+1) (by omega)
  exact ⟨toFn _ P,by change weightedEval _ _ (ofFn _ (toFn _ P))=_;rw [e]⟩

omit [CharZero K] in
theorem seed_eval_mass (ho:HasTreeOrderAtLeast A b p) (P:K[X]) (pay:P.natDegree+3≤p) :
    (∑ i,weightedEval (mirror A) (backSeed2 A b) P i)=0 := by
  have t:=mem_annih.mp (seed_eval_annih (m:=0) ho P (by omega)) (1:Vec K s)
    (stageWeight_mem_space A .leaf (by decide))
  simpa only [row_apply,Pi.one_apply,mul_one] using t

/-- A support-only cover of the genuine terminal-zero complement. This
is weaker than demanding that the whole complement be a polynomial band. -/
def SupportsComplement (A:Fin s→Fin s→K) (b:Vec K s) (m:ℕ) (t:Fin s) : Prop :=
  ∀ w∈annih (treeSpace A m)⊓LinearMap.ker (LinearMap.proj t),
    ∀ i,backSeed2 A b i=0→w i=0

omit [CharZero K] in
theorem support_of_orbit_cover {t:Fin s} (cover:
    (annih (treeSpace A m)⊓LinearMap.ker (LinearMap.proj t)) ≤
      nodalOrbit (mirror A) (backSeed2 A b)) : SupportsComplement A b m t := by
  intro w hw i h
  have q:=cover hw
  rw [nodalOrbit_eq_weightedEval] at q
  obtain ⟨P,rfl⟩:=q
  simp [h]

theorem true_port_eval (ho:HasTreeOrderAtLeast A b p) {t:Fin s}
    (y0:mirror A t=0) (col:∀k,A k t=0) (cover:SupportsComplement A b m t)
    (Q P R:K[X]) (qb:m+Q.natDegree+R.natDegree+3≤p)
    (pb:m+P.natDegree+R.natDegree+4≤p)
    {i:Fin s} (off:backSeed2 A b i=0) :
    transMat A (weightedEval (mirror A) (reverseContrast A b Q P) R) i =
      (Paired.primitive (R*(X*Q))).eval (mirror A i)*b i := by
  let y:=mirror A
  let S:=R*(X*Q)
  let T:=R*P
  let d:=backSeed2 A b
  have dg:S.natDegree≤R.natDegree+1+Q.natDegree:=by
    have h:=natDegree_mul_le (p:=R) (q:=X*Q)
    have k:=natDegree_mul_le (p:=X) (q:=Q)
    rw [natDegree_X] at k
    dsimp [S];omega
  have dt:T.natDegree≤R.natDegree+P.natDegree:=natDegree_mul_le
  have d1:transMat A (weightedEval y b S)-weightedEval y b (formalPrimitive S)∈
      annih (treeSpace A m)⊓LinearMap.ker (LinearMap.proj t):=by
    refine ⟨primitive_annihilator_paid ho S (by omega),?_⟩
    change transMat A (weightedEval y b S) t-weightedEval y b (formalPrimitive S) t=0
    simp [y,y0,transMat_zero_column t col]
  have d2:transMat A (weightedEval y d T)∈
      annih (treeSpace A m)⊓LinearMap.ker (LinearMap.proj t):=by
    refine ⟨mem_annih.mpr ?_,transMat_zero_column t col _⟩
    intro x hx
    rw [row_flip_mat]
    exact mem_annih.mp (seed_eval_annih (m:=m+1) ho T (by omega)) _ (mat_treeSpace A m hx)
  have z1:=cover _ d1 i off
  have z2:=cover _ d2 i off
  rw [reverseContrast_weighted,map_sub,Pi.sub_apply]
  change transMat A (weightedEval y b S) i-transMat A (weightedEval y d T) i=_
  change transMat A (weightedEval y b S) i-weightedEval y b (formalPrimitive S) i=0 at z1
  rw [z2,sub_zero,sub_eq_zero.mp z1,weightedEval_apply,formalPrimitive_eq_treePrimitive]

structure ReverseThreeTwo (A:Fin s→Fin s→K) (Q:K[X]) (u v:K) : Prop where
  u_ne : u≠0
  v_ne : v≠0
  different : v≠u
  left : ∀R:K[X],R.natDegree≤2→(Paired.primitive (R*(X*Q))).eval u=0
  right : ∀R:K[X],R.natDegree≤1→(Paired.primitive (R*(X*(X-C u)*Q))).eval v=0

/-- For two distinct active numerical ports on the actual contrast, each
chronological pivot receives exactly the required strict prefix mask. -/
theorem actual_reverse_three_two (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) {t:Fin s}
    (y0:mirror A t=0) (col:∀k,A k t=0) (cover:SupportsComplement A b m t)
    (Q P:K[X]) (qb:m+Q.natDegree+5≤p) (pb:m+P.natDegree+6≤p)
    (off:∀i,reverseContrast A b Q P i≠0→backSeed2 A b i=0)
    (two:∀a:K,∃i,reverseContrast A b Q P i≠0 ∧ mirror A i≠a) :
    ∃u v,ReverseThreeTwo A Q u v := by
  classical
  let y:=mirror A
  let w:=reverseContrast A b Q P
  let L:=Finset.univ.filter (fun i:Fin s =>w i≠0)
  obtain ⟨i,hi,imax⟩:=Finset.exists_max_image L id (by
    obtain ⟨k,kw,_⟩:=two 0
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,kw⟩⟩)
  have iw:w i≠0:=(Finset.mem_filter.mp hi).2
  let u:=y i
  let M:=L.filter (fun k=>y k≠u)
  obtain ⟨j,hj,jmax⟩:=Finset.exists_max_image M id (by
    obtain ⟨k,kw,ku⟩:=two u
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,kw⟩,ku⟩⟩)
  have jw:w j≠0:=(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have jv:y j≠u:=(Finset.mem_filter.mp hj).2
  have active (k:Fin s)(hk:w k≠0):y k≠0 ∧ b k≠0:=by
    have zz:=off k hk
    refine ⟨?_,?_⟩
    · intro yk
      apply hk
      simp [w,reverseContrast,y,yk,zz]
    · intro bk
      apply hk
      simp [w,reverseContrast,bk,zz]
  refine ⟨u,y j,⟨(active i iw).1,(active j jw).1,jv,?_,?_⟩⟩
  · intro R hr
    have z:transMat A (weightedEval y w R) i=0:=by
      apply causal_transpose ha
      intro k hk
      have lt:=Fin.rev_lt_rev.mp hk
      have no:w k=0:=by
        by_contra kn
        exact (not_le_of_gt lt) (imax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,kn⟩))
      simp [no]
    have eq:=true_port_eval ho y0 col cover Q P R (by omega) (by omega) (off i iw)
    change transMat A (weightedEval y w R) i=_ at eq
    rw [z] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_right (active i iw).2
  · intro R hr
    let H:=R*(X-C u)
    have hd:H.natDegree≤2:=by
      have e:=natDegree_mul_le (p:=R) (q:=X-C u)
      rw [natDegree_X_sub_C] at e
      dsimp [H];omega
    have z:transMat A (weightedEval y w H) j=0:=by
      apply causal_transpose ha
      intro k hk
      have lt:=Fin.rev_lt_rev.mp hk
      by_cases no:w k=0
      · simp [no]
      have ky:y k=u:=by
        by_contra ne
        exact (not_le_of_gt lt) (jmax k (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩,ne⟩))
      simp [H,ky]
    have eq:=true_port_eval ho y0 col cover Q P H (by omega) (by omega) (off j jw)
    change transMat A (weightedEval y w H) j=_ at eq
    rw [z] at eq
    have van: (Paired.primitive (H*(X*Q))).eval (y j)=0:=
      (mul_eq_zero.mp eq.symm).resolve_right (active j jw).2
    rwa [show H*(X*Q)=R*(X*(X-C u)*Q) by dsimp [H];ring] at van

end
end RKCert.Paired.ReverseHull

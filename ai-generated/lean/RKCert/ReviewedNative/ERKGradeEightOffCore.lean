module

public import RKCert.ReviewedNative.NativeLiveCore
public import RKCert.ReviewedNative.ERKGradeEightCubic

@[expose] public section

/-! # The rank-three core forces at most five actual clocks

The proof uses a one-dimensional space of off-core row functionals and
one paid derivative test, not three manually combined primitive moments. -/
namespace RKResearch.Certified.Graded
open RKResearch Module Polynomial RKCert.Endpoint LiveCore
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
noncomputable section

set_option maxRecDepth 3500 in
set_option maxHeartbeats 650000 in
/-- In a rank-three core equal to F4, off-core rows annihilate F3.
All their nonzero numerical clocks coincide. The polynomial test is
the derivative of X²(X-h)², whose primitive has double roots at 0 and h. -/
theorem rank_three_off_core_clocks (ha : ∀ i j, i≤j → A i j=0)
    (U : Submodule K (Fin s→K))
    (stable : U.map (diag (nodes A))≤U) (f4 : zeroSpace A 4=U)
    (dU : finrank K U=3) (d3 : finrank K (zeroSpace A 3)=2)
    {e : Fin s → K} (eu : e∈U) (ind : ∀ i, e i=if live U i then 1 else 0) :
    ∃ h : K, ∀ j, ¬live U j → nodes A j=0 ∨ nodes A j=h := by
  classical
  let c := nodes A
  have U3 : zeroSpace A 3≤U := (zeroSpace_mono A (by decide : 3≤4)).trans f4.le
  let F3 := (zeroSpace A 3).comap U.subtype
  let L := F3.dualAnnihilator
  have df : finrank K F3=2 := (Submodule.comapSubtypeEquivOfLe U3).finrank_eq.trans d3
  have dl : finrank K L=1 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq F3
    change finrank K F3+finrank K L=finrank K U at h
    omega
  let f (j : Fin s) : U→ₗ[K] K := (LinearMap.proj j).comp ((mat A).comp U.subtype)
  have fL (j : Fin s) (off : ¬live U j) : f j∈L := by
    change f j∈F3.dualAnnihilator
    apply (Submodule.mem_dualAnnihilator (f j)).mpr
    intro x hx
    have q : (x.val : Fin s→K)∈zeroSpace A 3 := hx
    have move : mat A x.val∈U := f4.le (mat_zeroSpace_charZero A 3 q)
    exact val_eq_zero_of_not_live off move
  let M := weightedEval c e
  let N := weightedEval c (1-e)
  have Mu (P : K[X]) : M P∈U := by
    have eq : M P=fun i => P.eval (c i)*e i := by ext i; simp [M]
    rw [eq]
    exact clock_function_mem (fun _ hu => stable (Submodule.mem_map_of_mem hu)) (fun x=>P.eval x) eu
  have paid (j : Fin s) (off : ¬live U j) (P : K[X]) (d : P.natDegree≤3)
      (pre : ∀ i, i<j → ¬live U i → P.eval (c i)=0) :
      f j ⟨M P,Mu P⟩=(primitive P).eval (c j) := by
    have nn : mat A (N P) j=0 := by
      apply causal_mat ha j
      intro i ij
      change i<j at ij
      by_cases li : live U i
      · simp [N,ind i,li]
      · simp [N,pre i ij li]
    have eP : evalNodes A P=M P+N P := by
      ext i
      simp only [evalNodes_apply,Pi.add_apply,M,N,weightedEval_apply,Pi.sub_apply,Pi.one_apply,c]
      ring
    have inc : mat A (evalNodes A P)-evalNodes A (primitive P)∈U := f4.le (primitive_defect A P d)
    have z := val_eq_zero_of_not_live off inc
    change mat A (evalNodes A P) j-(primitive P).eval (c j)=0 at z
    rw [eP,map_add,Pi.add_apply,nn,add_zero] at z
    exact sub_eq_zero.mp z
  let S := Finset.univ.filter (fun j : Fin s => ¬live U j ∧ c j≠0)
  by_cases sn : S.Nonempty
  · let q := S.min' sn
    have qd := (Finset.mem_filter.mp (S.min'_mem sn)).2
    let h := c q
    have qpre (i : Fin s) (iq : i<q) (off : ¬live U i) : c i=0 := by
      by_contra nz
      exact not_le_of_gt iq (S.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,off,nz⟩))
    let fq : L := ⟨f q,fL q qd.1⟩
    have nq : fq≠0 := by
      intro zz
      have hx := paid q qd.1 X (by simp) (fun i iq off => by rw [eval_X,qpre i iq off])
      have w := congrArg (fun g : L => g.val ⟨M X,Mu X⟩) zz
      change f q ⟨M X,Mu X⟩=0 at w
      rw [hx,show (X:K[X])=monomial 1 1 by simp [←C_mul_X_pow_eq_monomial],
        primitive_monomial,eval_monomial] at w
      have two : ((1+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by decide)
      exact mul_ne_zero (div_ne_zero one_ne_zero two) (pow_ne_zero _ qd.2) w
    have span : Submodule.span K ({fq} : Set L)=⊤ := by
      simpa using (FiniteDimensional.basisSingleton Unit dl fq nq).span_eq
    refine ⟨h,fun j off => ?_⟩
    by_contra! bad
    let T := Finset.univ.filter (fun i : Fin s => ¬live U i ∧ c i≠0 ∧ c i≠h)
    have tn : T.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,off,bad.1,bad.2⟩⟩
    let k := T.min' tn
    have kd := (Finset.mem_filter.mp (T.min'_mem tn)).2
    have kpre (i : Fin s) (ik : i<k) (oi : ¬live U i) : c i=0 ∨ c i=h := by
      by_contra! ne
      exact not_le_of_gt ik (T.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,oi,ne.1,ne.2⟩))
    let F : K[X] := X^2*(X-C h)^2
    let R := F.derivative
    have dF : F.natDegree≤4 := by
      have m := natDegree_mul_le (p:=(X:K[X])^2) (q:=(X-C h)^2)
      rw [natDegree_X_pow,natDegree_pow,natDegree_X_sub_C] at m
      exact m
    have dR : R.natDegree≤3 := by
      change F.derivative.natDegree≤3
      rw [natDegree_derivative]
      omega
    have origin : F.coeff 0=0 := by rw [coeff_zero_eq_eval_zero]; simp [F]
    have prim : primitive R=F := primitive_derivative F origin
    have roots : R.eval 0=0 ∧ R.eval h=0 := by
      constructor <;> simp [R,F,derivative_mul,derivative_pow]
    have fqe : f q ⟨M R,Mu R⟩=0 := by
      rw [paid q qd.1 R dR (fun i iq oi => by rw [qpre i iq oi,roots.1]),prim]
      change F.eval h=0
      simp [F]
    have ke : f k ⟨M R,Mu R⟩=(primitive R).eval (c k) :=
      paid k kd.1 R dR (fun i ik oi => by
        rcases kpre i ik oi with h0|hh
        · rw [h0,roots.1]
        · rw [hh,roots.2])
    let fk : L := ⟨f k,fL k kd.1⟩
    obtain ⟨a,hak⟩ := (Submodule.span_singleton_eq_top_iff K fq).mp span fk
    have w := congrArg (fun g : L => g.val ⟨M R,Mu R⟩) hak
    change a*f q ⟨M R,Mu R⟩=f k ⟨M R,Mu R⟩ at w
    rw [fqe,mul_zero,ke,prim] at w
    have zero : (c k)^2*(c k-h)^2=0 := by simpa only [F,eval_mul,eval_pow,eval_X,eval_sub,eval_C] using w.symm
    exact mul_ne_zero (pow_ne_zero _ kd.2.1) (pow_ne_zero _ (sub_ne_zero.mpr kd.2.2)) zero
  · refine ⟨0,fun j off => Or.inl ?_⟩
    by_contra nz
    exact sn ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,off,nz⟩⟩

end

/-- The core case is already incompatible with reviewed order ten:
three live clocks and two off-core values are too few to separate F5. -/
theorem no_rank_three_clock_core_at_order_ten
    {T : Matrix (Fin (s+1)) (Fin (s+1)) K} {w : Fin (s+1)→K}
    (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder p T w) (pay : 10≤p)
    (U : Submodule K (Fin (s+1)→K))
    (stable : U.map (diag (nodes T))≤U) (f4 : zeroSpace T 4=U)
    (dU : finrank K U=3) (d3 : finrank K (zeroSpace T 3)=2)
    (closed : ∀ u∈U, ∀ v∈U, u*v∈U) : False := by
  classical
  obtain ⟨e,eu,ind⟩ := exists_live_indicator U closed
  obtain ⟨h,off⟩ := rank_three_off_core_clocks ha U stable f4 dU d3 eu ind
  let S := (liveSites (nodes T) U) ∪ {0,h}
  have dl := live_sites_le_rank_of_indicator (nodes T) U stable eu ind
  have d2 : ({0,h}:Finset K).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
  have dS : S.card≤5 := by
    have h := Finset.card_union_le (liveSites (nodes T) U) {0,h}
    change S.card≤_ at h
    omega
  have sep : PolySeparated T 5 := PolySeparated.of_coeff (explicit_coeff_separated ha ho pay)
  refine sep.knots_not_cover S dS (fun i => ?_)
  apply Finset.mem_union.mpr
  by_cases li : live U i
  · exact Or.inl (mem_liveSites.mpr ⟨i,li,rfl⟩)
  · rcases off i li with e|e
    · exact Or.inr (by simp [e])
    · exact Or.inr (by simp [e])

/-- After the off-mask argument, the genuine grade-four quartic chart is
the only remaining route to a small grade-eight space over an ordered field. -/
theorem ordered_grade_eight_quartic_only [LinearOrder K] [IsStrictOrderedRing K]
    {T : Matrix (Fin (s+1)) (Fin (s+1)) K} {w : Fin (s+1)→K}
    (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder p T w) (pay : 16≤p)
    (cap : finrank K (zeroSpace T 8)≤8) :
    finrank K (zeroSpace T 4)=4 ∧ ∃ r U v, FlatClockHead T 4 4 r U v := by
  rcases grade_eight_remaining_two_cases ha ho pay cap with quartic | ⟨r,U,v,H,_,dU,d3,e,closed⟩
  · exact quartic
  · exact (no_rank_three_clock_core_at_order_ten ha ho (by omega) U H.coreStable e dU d3 closed).elim

end RKResearch.Certified.Graded

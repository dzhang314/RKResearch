module

public import RKCert.DirkBalancedPrimitive
public import RKCert.Dirk15TwoEndedPivots

@[expose] public section

/-! # Hiding the true ordinary cubic in the minimal marked chart
The only additional structural premise is the first reverse-clock escape.
Both chronological pivots come from the actual tableau and use genuinely
paid terminal-zero marked rows, not a shortened method. -/
namespace RKCert.Paired
open RKCert.Endpoint RKCert.OneEscape Polynomial Signature
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace ReverseTrace

omit [CharZero K] in
theorem scale {n : ℕ} {w : Vec K 20} {P : K[X]}
    (h : ReverseTrace A b 15 n w P) (a : K) :
    ReverseTrace A b 15 n (a • w) (C a*P) := by
  refine ⟨(natDegree_C_mul_le a P).trans h.degree,?_⟩
  rw [←smul_eq_C_mul,map_smul,←smul_sub]
  exact (marked A 15 n).smul_mem a h.pure

omit [CharZero K] in
theorem clock_sub_const {n : ℕ} {w : Vec K 20} {P : K[X]}
    (h : ReverseTrace A b 15 n w P) (hn : n+2≤15) (a : K) :
    ReverseTrace A b 15 (n+1) (diag (mirror A) w-a • w) ((X-C a)*P) := by
  rw [sub_mul]
  exact (h.clock hn).sub ((h.scale a).mono (Nat.le_succ n))

/-- A single primitive at a proved clean reverse pivot, paid in the true
terminal-zero band. This version can be used after more than one clock shift. -/
theorem primitive_at_refunded_last {n : ℕ} {w : Vec K 20} {P : K[X]}
    (h : ReverseTrace A b 15 n w P) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (T : PhysicalTerminal (s:=19) A b)
    (hn : n+1≤7) {i : Fin 20} (hpre : ∀ j,i<j → w j=0)
    (hbi : b i≠0) (hdiag : A i i=0)
    (clean : ∀ u∈markedTerminalZero (s:=19) A 15 7,u i=0) :
    (formalPrimitive P).eval (mirror A i)=0 := by
  have hB := h.primitive ho (by omega)
  have hdiff : transMat A w-weightedEval (mirror A) b (formalPrimitive P)
      ∈markedTerminalZero (s:=19) A 15 7 :=
    ⟨marked_mono A 15 hn hB.pure,prior_last_iff.mpr (by
      rw [Pi.sub_apply,T.trans_zero_terminal,weightedEval_apply,terminal_mirror_zero T,
        formalPrimitive_eval_zero,zero_mul,sub_zero])⟩
  have hmat : transMat A w i=0 := by rw [transMat_last_apply ha i w hpre,hdiag,zero_mul]
  have e := clean _ hdiff
  simp only [Pi.sub_apply,hmat,weightedEval_apply,zero_sub,neg_eq_zero] at e
  exact (mul_eq_zero.mp e).resolve_right hbi

theorem three_two_contrast_zero {θ : Vec K 20} {Q : K[X]}
    (hθ : ReverseTrace A b 15 3 θ Q) (dQ : Q.natDegree≤3)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (T : PhysicalTerminal (s:=19) A b)
    (hclean : ∀ i, θ i≠0 → b i≠0 ∧
      ∀ w∈markedTerminalZero (s:=19) A 15 7,w i=0) : Q=0 := by
  by_contra hQ
  let y := mirror A
  let C' := diag y
  let x := C' θ
  have hx : x≠0 := hθ.clock_witness ho hQ dQ (by decide)
  obtain ⟨i,hi,hpre⟩ := exists_last_coordinate hx
  let u := y i
  have hu : u≠0 := by intro e; exact hi (by simp [x,C',diag_apply,e,u])
  have hθi : θ i≠0 := fun e => hi (by simp [x,C',e])
  obtain ⟨bi,cleanI⟩ := hclean i hθi
  have ht4 : ReverseTrace A b 15 4 x (X*Q) := hθ.clock (by decide)
  obtain ⟨ai,e₁,e₂⟩ := ht4.two_primitive_last_pivot ha ho T
    (H:=7) (by decide) (by decide) hi hpre bi cleanI
  have ht6 := (ht4.clock (by decide : 4+2≤15)).clock (by decide : 5+2≤15)
  have e₃' := ht6.primitive_at_refunded_last ha ho T (by decide) (fun j hj => by
    simp [hpre j hj,x,C'] ) bi ai cleanI
  have e₃ : paidMoment Q u 3=0 := by
    have he : X^3*Q=X*(X*(X*Q)) := by ring
    simpa only [paidMoment,u,y,he] using e₃'
  let θ' := C' θ-u • θ
  let P := (X-C u)*Q
  have hθ' : ReverseTrace A b 15 4 θ' P := hθ.clock_sub_const (by decide) u
  have dP : P.natDegree≤4 := by
    have hA := natDegree_mul_le (p:=(X-C u:K[X])) (q:=Q)
    rw [natDegree_X_sub_C] at hA
    dsimp [P]
    omega
  have hP : P≠0 := mul_ne_zero (monic_X_sub_C u).ne_zero hQ
  obtain ⟨j,hj,hpreJ⟩ := exists_last_coordinate (hθ'.clock_witness ho hP dP (by decide))
  have hj0 : y j≠0 := fun e => hj (by simp [y,e])
  have hj1 : y j≠u := fun e => hj (by
    have hz : θ' j=0 := by simp [θ',C',y,e]
    simp [hz])
  have jnz : θ j≠0 := fun e => hj (by simp [θ',C',e])
  obtain ⟨bj,cleanJ⟩ := hclean j jnz
  obtain ⟨_,j₁,j₂⟩ := (hθ'.clock (by decide : 4+2≤15)).two_primitive_last_pivot
    ha ho T (H:=7) (by decide) (by decide) hj hpreJ bj cleanJ
  exact balanced_three_two_impossible Q hQ dQ hu hj0 hj1 e₁ e₂ e₃ j₁ j₂

end ReverseTrace

/-- A true grade-three pure vanishes on both active channels once the
genuine paid cubic orbit and its physical terminal are fixed. -/
theorem order15_cubic_channels_of_orbit (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (T : PhysicalTerminal (s:=19) A b)
    (orb : ∀ j : ℕ, 3≤j → j≤7 → markedTerminalZero (s:=19) A 15 j=
      chain (diag (mirror A)) ⊥ (reverseCubic A b) (j-2))
    {f : Vec K 20} (hf : f∈zeroSpace A 3) (t0 : f (Fin.last 19)=0) :
    ∀ i, (b i≠0 ∨ reverseCubic A b i≠0) → f i=0 := by
  let τ := reverseCubic A b
  let y := mirror A
  have hτ : τ∈markedTerminalZero (s:=19) A 15 3 :=
    order15_reverseCubic_mem ho T
  have ht : τ*f∈markedTerminalZero (s:=19) A 15 6 :=
    ⟨marked_mul_tree (j:=3) (k:=3) (by decide) hτ.1 (zeroSpace_le_treeSpace A 3 hf),
      prior_last_iff.mpr (by rw [Pi.mul_apply,prior_last_iff.mp hτ.2,zero_mul])⟩
  rw [orb 6 (by decide) (by decide)] at ht
  obtain ⟨w,hw,Q,hQ',hEq⟩ := Clock.exists_head_poly ht
  have hw0 : w=0 := by simpa using hw
  have dQ : Q.natDegree≤3 := by
    by_cases hz : Q=0
    · simp [hz]
    · have he := (natDegree_lt_iff_degree_lt hz).mpr hQ'
      omega
  have hmatch (i : Fin 20) (hi : τ i≠0) : f i=Q.eval (y i) := by
    have e := hEq i
    simp only [Pi.mul_apply,hw0,Pi.zero_apply,zero_add] at e
    apply mul_left_cancel₀ hi
    simpa only [mul_comm (Q.eval _)] using e
  let θ := weightedEval y b Q-b*f
  have bf := weights_mul_zeroSpace ho (by decide : 3+1≤15) hf
  have θTrace : ReverseTrace A b 15 3 θ Q := (ReverseTrace.scalar A b dQ).sub_pure bf
  have clean (i : Fin 20) (hn : θ i≠0) : b i≠0 ∧
      ∀ w∈markedTerminalZero (s:=19) A 15 7,w i=0 := by
    have bi : b i≠0 := fun he => hn (by simp [θ,he])
    have ti : τ i=0 := by
      by_contra hh
      exact hn (by simp [θ,hmatch i hh,mul_comm])
    refine ⟨bi,fun v hv => ?_⟩
    rw [orb 7 (by decide) (by decide)] at hv
    obtain ⟨u,hu,R,_,hR⟩ := Clock.exists_head_poly hv
    have hu0 : u=0 := by simpa using hu
    have ti' : reverseCubic A b i=0 := ti
    simpa only [hu0,Pi.zero_apply,ti',mul_zero,add_zero] using hR i
  have Qzero := θTrace.three_two_contrast_zero dQ ha ho T clean
  have bf0 : b*f∈markedTerminalZero (s:=19) A 15 7 :=
    ⟨marked_mono A 15 (by decide : 3≤7) bf,prior_last_iff.mpr (by
      rw [Pi.mul_apply,t0,mul_zero])⟩
  rw [orb 7 (by decide) (by decide)] at bf0
  obtain ⟨r,hr,R,_,hR⟩ := Clock.exists_head_poly bf0
  have hr0 : r=0 := by simpa using hr
  intro i hi
  by_cases ti : τ i=0
  · have bni : b i≠0 := hi.resolve_right (not_not_intro ti)
    have e := hR i
    have ti' : reverseCubic A b i=0 := ti
    simp only [Pi.mul_apply,hr0,Pi.zero_apply,zero_add,ti',mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left bni
  · simp only [hmatch i ti,Qzero,eval_zero]

/-- The anchored minimal branch forces F3 into the simultaneous ghost
coordinate space. This interface accepts an independently proved first
escape, and retains the actual zero initial row. -/
theorem order15_cubic_le_simultaneous_ghosts (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬(markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3) :
    zeroSpace A 3≤simultaneousGhosts A b := by
  intro f hf
  rw [simultaneousGhosts_mem]
  refine ⟨zeroSpace_first_of_row h.initial.first_zero 3 hf,
    order15_cubic_channels_of_orbit ha ho h.terminal (order15_minimal_cubic_orbit ha ho h hfirst)
      hf (h.f4_terminal_zero _ (zeroSpace_mono A (by decide) hf))⟩

end RKCert.Paired

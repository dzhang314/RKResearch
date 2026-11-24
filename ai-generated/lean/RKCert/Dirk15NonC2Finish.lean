module

public import RKCert.Dirk15NonC2HeadPolynomial
public import RKCert.DirkCleanTracePivot

@[expose] public section

/-! # Exclusion of the entire non-C(2) twenty-stage branch

The chronological pivot is chosen among all physical rows, not among
nonzero-output-weight rows. Its scalar is the verified fixed Radau
omitted-factor moment. This theorem is a class bound, not the unrestricted
order-fifteen endpoint.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint RKCert.OneEscape
open RKCert.FixedPolynomial.Radau77569 RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

private theorem radau_nonmonic_paid_ne {P : K[X]} (pn : P≠0) (pd : P.natDegree≤4)
    (pf : P∣(normalizedRightRadau7 : K[X])) {u : K}
    (hr : (rightRadau7 : K[X]).eval u=0) (ou : P.eval u≠0) :
    paidMoment P u 1≠0 := by
  classical
  let T := normalize P
  have Tdiv : T∣(rightRadau7 : K[X]) := normalize_dvd_iff.mpr
    ((Polynomial.dvd_C_mul (inv_ne_zero (rightRadau7_one_ne (K:=K)))).mp pf)
  have Tmono : T.Monic := monic_normalize pn
  have dT : T.natDegree≤4 := by rw [show T=normalize P from rfl,natDegree_normalize]; exact pd
  have eq : T=P*C P.leadingCoeff⁻¹ := by
    change normalize P=_
    rw [normalize_apply,coe_normUnit_of_ne_zero pn]
  have om : T.eval u≠0 := by
    rw [eq,eval_mul,eval_C]
    exact mul_ne_zero ou (inv_ne_zero (leadingCoeff_ne_zero.mpr pn))
  intro zero
  apply right_divisor_paid_ne Tmono dT Tdiv hr om
  unfold paidMoment at zero ⊢
  change (formalPrimitiveLinear (X^1*T)).eval u=0
  rw [eq,show X^1*(P*C P.leadingCoeff⁻¹)=P.leadingCoeff⁻¹ • (X^1*P) by
    rw [smul_eq_C_mul]; ring,map_smul,eval_smul,smul_eq_mul]
  change P.leadingCoeff⁻¹*(formalPrimitive (X^1*P)).eval u=0
  rw [zero,mul_zero]

set_option maxHeartbeats 1250000 in
theorem order15_twenty_implies_C2 (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) :
    q₂ (mat A) (nodes A) 1=0 := by
  classical
  by_contra hq
  obtain ⟨h⟩ := order15_nonC2_head ha ho hq
  obtain ⟨P,pn,pd,headP,pf⟩ := order15_nonC2_head_polynomial ha ho hq h
  let G : K[X] := normalizedRightRadau7
  let w := h.head
  let c := nodes A
  let C' := diag c
  let F := zeroSpace A
  let s := Fin.last 19
  let H := order15_nonC2_rank_chart ha ho hq
  let g : Vec K 20 := fun i => if b i=0 ∧ reverseCubic A b i=0 then (X*P).eval (c i) else 0
  let θ := evalNodes A (X*P)-g-C' w
  have hg : g∈nonC2Ghosts A b := by
    apply mem_nonC2Ghosts.mpr
    intro i hi
    have hh : ¬(b i=0 ∧ reverseCubic A b i=0) := fun e => hi.elim (· e.1) (· e.2)
    simp [g,hh]
  have c5 : C' w∈F 5 := (h.band 0 (by decide)).ge
    (by
      have p := ((chain_le_iff (T:=C') (U:=nonC2Ghosts A b) (w:=w) 2).mp le_rfl).2 1 (by decide)
      simpa only [pow_one] using p)
  have pureG : g∈F 5 := zeroSpace_mono A (by decide : 4≤5) (h.core_eq.ge hg)
  have tr : OrdinaryTrace A 5 θ (X*P) := by
    refine ⟨natDegree_mul_le.trans (by rw [natDegree_X]; omega),?_⟩
    have e : θ-evalNodes A (X*P)= -g-C' w := by dsimp only [θ]; abel
    rw [e]
    exact (F 5).sub_mem ((F 5).neg_mem pureG) c5
  have away : ∃ i : Fin 20,i≠s ∧ θ i≠0 := by
    by_contra! h0
    apply pn
    apply two_end_weight_primitive_detect P (d:=4) (k:=1) pd
    intro j
    let Q : K[X] := (1-X)*X^j.val
    have dQ : Q.natDegree≤5 := natDegree_mul_le.trans (by
      rw [one_sub_clock_degree,natDegree_X_pow]
      have := j.isLt
      omega)
    have e := tr.pair_polynomial ho Q (by omega)
    have vanish : row (weightedEval c b Q) θ=0 := by
      rw [row_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases is : i=s
      · subst i
        have co : nodes A s=1 := H.terminal.node_one
        simp [weightedEval_apply,c,co,Q]
      · rw [h0 i is,mul_zero]
    rw [vanish] at e
    rw [show X^(1+j.val)*((1-X)*P)=(X*P)*Q by dsimp only [Q]; rw [pow_add,pow_one]; ring]
    exact e.symm
  obtain ⟨l,ls,ln⟩ := away
  have θn : θ≠0 := fun e => ln (by rw [e,Pi.zero_apply])
  obtain ⟨i,iz,before⟩ := exists_first_coordinate θn
  have is : i≠s := fun e => ln (before l (e ▸ (lt_of_le_of_ne (Fin.le_last l) ls)))
  have notGhost : ¬(b i=0 ∧ reverseCubic A b i=0) := by
    intro e
    apply iz
    simp [θ,g,e,h.disjoint i e.1 e.2,C',c,w]
  have wi0 : w i=0 := by
    by_contra wi
    apply iz
    have p := headP i wi
    change w i=P.eval (c i) at p
    simp [θ,g,notGhost,C',c,p,eval_mul]
  have outside : b i≠0 ∨ reverseCubic A b i≠0 := by
    by_cases bi : b i=0
    · exact Or.inr (fun e => notGhost ⟨bi,e⟩)
    · exact Or.inl bi
  have θi : θ i=c i*P.eval (c i) := by
    simp [θ,g,notGhost,C',wi0,c,eval_mul]
  have omitP : P.eval (c i)≠0 := fun e => iz (by rw [θi,e,mul_zero])
  have clean (v : Vec K 20) (hv : v∈F 7) : v i=0 := by
    have hv' := (h.band 2 (by decide)).le hv
    obtain ⟨y,hy,Q,_,vQ⟩ := Clock.exists_head_poly hv'
    have h0 := mem_nonC2Ghosts.mp hy i outside
    have hi : h.head i=0 := wi0
    simpa only [h0,hi,mul_zero,zero_add] using vQ i
  have qroot : G.eval (c i)=0 := by
    have v : terminalCardinal K 19-evalNodes A G∈F 7 := order15_nonC2_terminal_profile ha ho hq
    have e := clean _ v
    simpa only [Pi.sub_apply,terminalCardinal_apply_ne is,evalNodes_apply,zero_sub,neg_eq_zero] using e
  have rightRoot : (rightRadau7 : K[X]).eval (c i)=0 := by
    change (C ((rightRadau7 : K[X]).eval 1)⁻¹*rightRadau7).eval (c i)=0 at qroot
    rw [eval_mul,eval_C] at qroot
    exact (mul_eq_zero.mp qroot).resolve_left (inv_ne_zero rightRadau7_one_ne)
  have prim := (tr.primitive_zero_at_first_clean ha ho (by decide) (by decide : 5+2≤7) iz before clean).2
  apply radau_nonmonic_paid_ne pn pd pf rightRoot omitP
  unfold paidMoment
  rw [pow_one,formalPrimitive_eq_treePrimitive]
  exact prim

theorem dirk_order15_nonC2_ge_21 {s : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (hq : q₂ (mat A) (nodes A) 1≠0) :
    21≤s := by
  have lower := dirk_order15_native_rank ha ho
  by_contra h
  have eq : s=20 := by omega
  subst s
  exact hq (order15_twenty_implies_C2 ha ho)

end
end RKCert.Paired

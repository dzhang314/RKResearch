module
public import RKCert.ERKTerminalSteering
public import RKCert.OrderTwelveReverseRows

@[expose] public section
/-! # Actual one-row repair of the missing unary-root conditions
The top branched roots are kept exact. No lower tree weights are changed.
Only if the first reflected residual is nonzero on the last active output
does this particular causal repair become unavailable.
-/
namespace RKCert.Paired
open RKCert.Paired.OrderTwelve Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
set_option maxHeartbeats 2400000

abbrev BranchedTop (A:Fin s→Fin s→K) (b:Vec K s) (m:ℕ) : Prop :=
  ∀ t u v:Tree, (Tree.attach t (.attach u v)).order≤m →
    ((Tree.attach t (.attach u v)).density:K)*weight A b (.attach t (.attach u v))=1

omit [CharZero K] in
theorem order_norm_equation (A:Fin s→Fin s→K) (b:Vec K s) (t:Tree) :
    (t.density:K)*weight A b t=(t.order:K)*row b (normTree A t) := by
  rw [Tree.density,Nat.cast_mul,normTree,map_smul,smul_eq_mul]
  change (t.order:K)*(t.childDensityProduct:K)*row b (stageWeight A t)=_
  ring

omit [CharZero K] in
theorem first_residual_eq_backSeed (A:Fin s→Fin s→K) (b:Vec K s) :
    reverseResidual A b 0=backSeed1 A b := by
  rw [reverseResidual_eq _ _ _ (by norm_num),reflWeight_power,reflWeight_power]
  ext i
  simp [backSeed1,powerWeight]

omit [CharZero K] in
theorem partial_top_finish_of_seed_zero {A:Fin s→Fin s→K} {b:Vec K s}
    (hp:2≤p) (ho:HasTreeOrderAtLeast A b p) (hb:BranchedTop A b (p+1))
    (hz:backSeed1 A b=0) : HasTreeOrderAtLeast A b (p+1) := by
  intro t ht
  by_cases lower:t.order≤p
  · exact ho t lower
  cases t with
  | leaf => simp only [Tree.order] at lower; omega
  | attach t v =>
    cases v with
    | attach u v => exact hb t u v ht
    | leaf =>
      have tt : t.order=p := by
        change t.order+1≤p+1 at ht
        change ¬t.order+1≤p at lower
        omega
      have e : t≠Tree.leaf := by
        intro hz
        rw [hz,Tree.order] at tt
        omega
      have cm : ((Tree.attach .leaf t).density:K)*weight A b (.attach .leaf t)=1 := by
        cases t with
        | leaf => exact (e rfl).elim
        | attach u v =>
          apply hb
          change 1+ (Tree.attach u v).order≤p+1
          omega
      have st := ho t (by omega)
      rw [order_norm_equation] at st cm ⊢
      have rw0 : transMat A b=diag (mirror A) b := sub_eq_zero.mp hz
      have mv : row b (mat A (normTree A t))=
          row b (normTree A t)-row b (diag (nodes A) (normTree A t)) := by
        rw [←row_flip_mat,rw0,row_flip_diag]
        have e : diag (mirror A) (normTree A t)=normTree A t-diag (nodes A) (normTree A t) := by
          ext i
          simp [mirror,sub_mul]
        rw [e,map_sub]
      rw [normTree_unary,map_smul,smul_eq_mul,mv] 
      rw [normTree_shift] at cm
      simp only [Tree.order,Nat.cast_add,Nat.cast_one] at cm ⊢
      linear_combination ((t.order:K)+1)*st-(t.order:K)*cm

omit [CharZero K] in
def repairPivot (k:Fin s) : Vec K s := Pi.single k (1:K)

omit [CharZero K] in
noncomputable def repairTop (A:Fin s→Fin s→K) (b:Vec K s) (k:Fin s) (i j:Fin s) : K :=
  A i j-(repairPivot k) i*(backSeed1 A b j/b k)

omit [CharZero K] in
theorem seed_vanish_after_output {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:StrictLower A) {k:Fin s} (later:∀j,k<j→b j=0) :
    ∀j,k<j→backSeed1 A b j=0 := by
  intro j hj
  have t : transMat A b j=0 := by
    apply causal_transpose ha j
    intro l hl
    exact later l (lt_trans hj (Fin.rev_lt_rev.mp hl))
  simp [backSeed1,t,later j hj]

theorem repair_partial_top {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
    (ha:StrictLower A) (hp:2≤p) (ho:HasTreeOrderAtLeast A b p)
    (hb:BranchedTop A b (p+1)) {k:Fin (s+1)}
    (bk:b k≠0) (later:∀j,k<j→b j=0) (zeroK:reverseResidual A b 0 k=0) :
    StrictLower (repairTop A b k) ∧ HasTreeOrderAtLeast (repairTop A b k) b (p+1) := by
  classical
  let B:=repairTop A b k
  have zero : ∀j,k≤j→backSeed1 A b j=0 := by
    intro j jj
    rcases lt_or_eq_of_le jj with h|rfl
    · exact seed_vanish_after_output ha later j h
    · rwa [←first_residual_eq_backSeed]
  have strict : StrictLower B := by
    intro i j hij
    by_cases h:i=k
    · subst i
      simp [B,repairTop,repairPivot,ha _ _ hij,zero j hij]
    · simp [B,repairTop,repairPivot,ha _ _ hij,Pi.single_eq_of_ne h]
  have agree (v:Vec K (s+1)) (hv:v∈treeSpace A (p-2)) : mat B v=mat A v := by
    have h0:=mem_annih.mp (backSeed1_annih ho (j:=p-2) (by omega)) v hv
    ext i
    simp only [mat_apply,B,repairTop,sub_mul,Finset.sum_sub_distrib]
    have e : (∑ j,(repairPivot k) i*(backSeed1 A b j/b k)*v j)=
        ((repairPivot k) i/b k)*row (backSeed1 A b) v := by
      rw [row_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e,h0,mul_zero,sub_zero]
  have paid := TerminalSteering.stageWeight_eq_of_agrees hp agree
  have hO : HasTreeOrderAtLeast B b p := by
    intro t ht
    simpa only [weight,paid t ht] using ho t ht
  have br : BranchedTop B b (p+1) := by
    intro t u v ht
    have tp:=t.order_pos
    have up:=u.order_pos
    have vp:=v.order_pos
    change t.order+(u.order+v.order)≤p+1 at ht
    have eq : stageWeight B (.attach t (.attach u v))=stageWeight A (.attach t (.attach u v)) := by
      change mat B (stageWeight B t)*stageWeight B (.attach u v)=
        mat A (stageWeight A t)*stageWeight A (.attach u v)
      rw [paid t (by omega),paid (.attach u v) (by change u.order+v.order≤p;omega),
        agree _ (stageWeight_mem_space _ _ (by omega))]
    simpa only [weight,eq] using hb t u v ht
  have same : nodes B=nodes A := by
    have e := paid (.attach .leaf .leaf) (by change 2≤p;exact hp)
    ext i
    simpa [stageWeight,nodes] using congrFun e i
  have tr : transMat B b=transMat A b-backSeed1 A b := by
    ext j
    simp only [mat_apply,B,repairTop,sub_mul,Finset.sum_sub_distrib,Pi.sub_apply]
    have e : (∑ i,(repairPivot k) i*(backSeed1 A b j/b k)*b i)=
        (backSeed1 A b j/b k)*row b (repairPivot k) := by
      rw [row_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have byw : row b (repairPivot k)=b k := by simp [repairPivot,row_apply,Pi.single_apply]
    rw [e,byw,div_mul_cancel₀ _ bk]
  have sz:backSeed1 B b=0 := by
    rw [backSeed1,tr,show mirror B=mirror A from by unfold mirror;rw [same]]
    rw [backSeed1]
    abel
  exact ⟨strict,partial_top_finish_of_seed_zero hp hO br sz⟩

end RKCert.Paired

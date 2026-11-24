module
public import RKCert.ERKOrder13MarkedFeatureCapacity
public import RKCert.ERKOrder13TerminalMoments
public import RKCert.ERKOrder13TiedFeatures

@[expose] public section
/-! # Actual late marked rank-two genuine-ghost exclusion -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G H:K[X]}
set_option maxHeartbeats 3000000

omit [CharZero K] in
theorem marked13_cleaned_terminal_zero (C:Chart13 A 1 a 2 U w G)
    (dis:∀i,Live U i→w i=0) : w (Fin.last s)=0 := by
  apply dis
  refine ⟨terminal s,marked13_terminal_in_core C ?_,?_⟩
  · rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)]
    exact Submodule.mem_span_singleton_self _
  · rw [terminal_at_last]
    exact one_ne_zero

omit [CharZero K] in
theorem marked13_four_paid (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (rank4:finrank K (zeroSpace A 4)=4) : U≤defectPlus A 1 4 ∧ w∈defectPlus A 1 4 := by
  rw [marked13_four_exact ho S M C.marked rank4]
  have h:= (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mp le_rfl
  exact ⟨h.1,by simpa only [pow_zero,one_apply_eq_self] using h.2 0 (by decide)⟩

theorem marked13_late_rank_two_no_eight (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 2 U w G)
    (rank4:finrank K (zeroSpace A 4)=4) (dis:∀i,Live U i→w i=0)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7) :
    (terminal s:Vec K (s+1))∉treeSpace A 8 := by
  intro eighth
  have end0 (v:Vec K (s+1)) (hv:v∈zeroSpace A 4) : v (Fin.last s)=0 :=
    actual_terminal_vanishes ho S.lastLive (by decide) eighth hv
  have ⟨up,wp⟩:=marked13_four_paid ho S M C rank4
  have we:=marked13_cleaned_terminal_zero C dis
  have w4:=ordinary_when_augmented_terminal_zero end0 wp we
  have gm : (0:Vec K (s+1))-evalNodes A G∈chain (diag (nodes A)) U w 4 := by
    rw [zero_sub,show chain (diag (nodes A)) U w 4=firstEscape A 1 6 from C.marked.edge.symm]
    exact Submodule.neg_mem _ C.meshPaid
  have gl := terminal_lift_from_paid_head (P:=G) (j:=7) (n:=4) ho (M.atOne (by decide))
    up end0 w4 we ((zeroSpace A 7).zero_mem) (by rfl) (by decide) (by decide)
    (by decide) (by decide) gm
  have gd : G.natDegree≤7 := by rw [C.meshDegree]
  have actual : evalNodes A G∈zeroSpace A 7 :=
    unmark_before_tail late (firstEscape_defect C.meshPaid) (evalNodes_mem_treeSpace A _ gd)
  have d:= (zeroSpace A 7).sub_mem actual gl
  have sc : G.eval 1 • (terminal s:Vec K (s+1))∈zeroSpace A 7 := by
    convert d using 1
    abel
  obtain ⟨_,t,tn,mesh⟩:=late13_mesh ha ho S C late
  have e : G.eval 1=t := by rw [mesh,odd6_as_oddSix];norm_num [oddSixValue]
  have gn : G.eval 1≠0:= e ▸ tn
  exact late (((treeSpace A 7).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr gn)).mp
    (zeroSpace_le_treeSpace A 7 sc))

theorem marked13_late_clean_ghost_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (rank4:finrank K (zeroSpace A 4)=4) (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7)
    (hd:H.natDegree≤a) (hn:H≠0) (ghost:w*w-evalNodes A H∈Band13 A a 2 U w 8) : False := by
  obtain ⟨rfl,t,tn,gt⟩:=late13_mesh ha ho S C late
  have late8:=marked13_late_rank_two_no_eight ha ho S M C rank4 dis late
  have wp := (marked13_four_paid ho S M C rank4).2
  have hE : evalNodes A H∈defectPlus A 1 8 := by
    have d := (defectPlus A 1 8).sub_mem (Fplus_mul (j:=4) (k:=4) wp wp)
      (band13_paid C (j:=8) (by decide) ghost)
    simpa only [sub_sub_cancel] using d
  have hA := unmark_before_tail late8 hE (evalNodes_mem_treeSpace A _ (by omega))
  have o:=marked_eval_origin ha (by have:=S.size;omega) H hE
  obtain ⟨a,h⟩:=ghost13Full_decode H hd o (fun k=>marked_moment_zero ho H (tail_zero_iff.mpr hA)
    (by omega) (by have:=k.isLt;omega))
  have an:a≠0 := fun e=>hn (by rw [h,e,zero_smul])
  have gh : G=t•(X*oddSixPoly) := by rw [gt,odd6_as_oddSix]
  have dv : (oddSixPoly:K[X])∣G := by use Polynomial.C t*X;rw [gh,smul_eq_C_mul];ring
  have co : IsCoprime (oddSixPoly:K[X]) H := by rw [h];exact full13_ghost_coprime an
  have g0:G.eval 0=0 := by rw [gh,eval_smul,eval_mul,eval_X,zero_mul,smul_zero]
  have h0:H.eval 0=0 := by rw [h,eval_smul,odd5_as_poly];simp
  apply marked13_ghost_feature_contradiction ha ho S M C alg dis ghost
  intro Q R qd rd sites
  constructor
  · exact full13_ghost_head_capacity G H Q R C.meshDegree hd qd (by change R.natDegree<5 at rd;omega) g0 h0 dv co _ sites
  · intro x gx hx
    by_contra! e
    have z : (oddSixPoly:K[X]).eval x=0 := by
      rw [gh,eval_smul,smul_eq_mul,eval_mul,eval_X] at gx
      exact (mul_eq_zero.mp ((mul_eq_zero.mp gx).resolve_left tn)).resolve_left e
    obtain ⟨u,v,hv⟩:=co
    have r:=congrArg (fun T:K[X]=>T.eval x) hv
    simp only [eval_add,eval_mul,z,hx,mul_zero,add_zero,eval_one] at r
    exact zero_ne_one r

end RKCert.Paired.FiniteMidpoint

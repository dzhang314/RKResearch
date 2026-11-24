module

public import RKCert.Dirk15NonC2Orbit
public import RKCert.Dirk15NonC2SquareAlgebra

@[expose] public section

/-! # The actual forward squares have no scalar part -/
namespace RKCert.Paired
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

set_option maxHeartbeats 1400000 in
theorem order15_nonC2_square_tail (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b) (l : Fin 3) :
    ((diag (nodes A))^l.val) (h.head*h.head)∈h.orbit 7 := by
  classical
  let C' := diag (nodes A)
  let w := h.head
  let x (i : Fin 3) := (C'^i.val) (w*w)
  let G : K[X] := normalizedRightRadau7
  have H := order15_nonC2_rank_chart ha ho hq
  have paid0 : zeroSpace A 5=h.orbit 2 := h.band 0 (by decide)
  have basis := ((chain_le_iff (T:=C') (U:=nonC2Ghosts A b) (w:=w) 2).mp le_rfl).2
  have hw : w∈zeroSpace A 5 := paid0.ge (by
    change w∈chain C' (nonC2Ghosts A b) w 2
    simpa only [pow_zero,one_apply_eq_self] using basis 0 (by decide))
  have cw : C' w∈zeroSpace A 5 := paid0.ge (by
    change C' w∈chain C' (nonC2Ghosts A b) w 2
    simpa only [pow_one] using basis 1 (by decide))
  have wlast : w (Fin.last 19)=0 := h.orbit_last H 2 (paid0.le hw)
  have xlast (i : Fin 3) : x i (Fin.last 19)=0 := by
    change ((diag (nodes A))^i.val) (w*w) (Fin.last 19)=0
    rw [Clock.pow_diag_apply,Pi.mul_apply,wlast,mul_zero,mul_zero]
  have xpure (i : Fin 3) : x i∈zeroSpace A 10 := by
    fin_cases i
    · change (C'^0) (w*w)∈zeroSpace A 10
      simpa only [pow_zero,one_apply_eq_self] using zeroSpace_mul hw hw
    · change (C'^1) (w*w)∈zeroSpace A 10
      rw [pow_one,show C' (w*w)=C' w*w by
        ext j; simp only [C',diag_apply,Pi.mul_apply]; ring]
      exact zeroSpace_mul cw hw
    · change (C'^2) (w*w)∈zeroSpace A 10
      rw [show (C'^2) (w*w)=C' w*C' w by
        ext j; simp only [C',Clock.pow_diag_apply,Pi.mul_apply,diag_apply]; ring]
      exact zeroSpace_mul cw cw
  have parts (i : Fin 3) :=
    h.actual_parts ha ho hq (j:=10) (by decide) (by decide) (zeroSpace_le_treeSpace A 10 (xpure i))
  choose P dP v ov dec using parts
  have pureP (i : Fin 3) : evalNodes A (P i)∈zeroSpace A 10 := by
    have vv : v i∈zeroSpace A 10 := h.orbit_pure 10 (by decide) (ov i)
    have q : evaluateColumn A (P i)=x i-v i := by rw [dec i,add_sub_cancel_right]
    change evalNodes A (P i)=x i-v i at q
    rw [q]
    exact (zeroSpace A 10).sub_mem (xpure i) vv
  have lastP (i : Fin 3) : (P i).eval 1=0 := by
    have e := congrArg (fun z : Vec K 20 => z (Fin.last 19)) (dec i)
    simp only [xlast,Pi.add_apply,evaluateColumn_eq,evalNodes_apply,H.terminal.node_one,
      h.orbit_last H _ (ov i),add_zero] at e
    exact e.symm
  have fact (i : Fin 3) : ∃ R : K[X],R.natDegree≤6 ∧ P i=(1-X)*R := by
    have z : X-C (1:K)∣P i := dvd_iff_isRoot.mpr (lastP i)
    obtain ⟨R,e⟩ := z
    have eg : P i=(1-X)*(-R) := by rw [e,map_one]; ring
    refine ⟨-R,?_,eg⟩
    by_cases nz : (-R)=0
    · simp [nz]
    have r := dP i
    rw [eg,natDegree_mul one_sub_clock_ne nz,one_sub_clock_degree] at r
    omega
  choose J dJ eqJ using fact
  have test (i : Fin 3) (Q : K[X]) (dq : Q.natDegree≤4) :
      unitIntegral ((1-X)*J i*Q)=0 := by
    rw [←eqJ]
    exact scalar_pure_unit_pair ho (j:=10) ((dP i).trans (by decide)) (pureP i) (by omega)
  have gtest (Q : K[X]) (dq : Q.natDegree≤6) : unitIntegral ((1-X)*G*Q)=0 := by
    rw [show (1-X)*G*Q=G*((1-X)*Q) by ring]
    apply normalizedRightRadau7_zero_test _ _ (by simp)
    exact natDegree_mul_le.trans (by rw [one_sub_clock_degree]; omega)
  have step (i : Fin 2) : ∃ a : K,X*J i.castSucc-J i.succ=C a*G := by
    have xv : x i.succ=C' (x i.castSucc) := by
      change (C'^(i.val+1)) (w*w)=_
      rw [pow_succ',mul_apply_eq_comp]
      rfl
    have e : evaluateColumn A (P i.succ)+v i.succ =
        evaluateColumn A (X*P i.castSucc)+C' (v i.castSucc) := by
      calc
        _ = x i.succ := (dec i.succ).symm
        _ = C' (x i.castSucc) := xv
        _ = _ := by rw [dec i.castSucc,map_add,evaluateColumn_clock]
    have e' : evaluateColumn A (X*P i.castSucc-P i.succ)=v i.succ-C' (v i.castSucc) := by
      rw [map_sub]
      linear_combination -e
    have member : evaluateColumn A (X*P i.castSucc-P i.succ)∈h.orbit 8 := by
      rw [e',←h.orbit_step (by decide : 0<7)]
      refine (h.orbit 7⊔(h.orbit 7).map C').sub_mem
        ((le_sup_left : h.orbit 7≤_) (ov i.succ)) ?_
      exact (le_sup_right : (h.orbit 7).map C'≤_) (Submodule.mem_map_of_mem (ov i.castSucc))
    have dp : (X*P i.castSucc-P i.succ).natDegree≤8 := (natDegree_sub_le _ _).trans
      (max_le (natDegree_mul_le.trans (by rw [natDegree_X]; have := dP i.castSucc; omega))
        ((dP i.succ).trans (by decide)))
    obtain ⟨a,rel⟩ := order15_nonC2_scalar_reduces ha ho hq h dp member
    refine ⟨a,mul_left_cancel₀ one_sub_clock_ne ?_⟩
    calc
      (1-X)*(X*J i.castSucc-J i.succ) = X*P i.castSucc-P i.succ := by
        rw [eqJ,eqJ]
        ring
      _ = C a*((1-X)*G) := rel
      _ = (1-X)*(C a*G) := by ring
  have j0 := paid_three_scalar_parts_zero G normalizedRightRadau7_degree gtest J dJ test step
  have pl : P l=0 := by rw [eqJ,j0,mul_zero]
  change x l∈h.orbit 7
  rw [dec,pl,map_zero,zero_add]
  exact ov l

end
end RKCert.Paired

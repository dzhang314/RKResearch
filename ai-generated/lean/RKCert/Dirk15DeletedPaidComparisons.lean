module

public import RKCert.Dirk15DeletedPureDecomposition
public import RKCert.Dirk15FoldedScalarReduction

@[expose] public section

/-! # Adjacent scalar comparisons for all actual paid grade-ten products

The terminal remains deleted only in these numerical identities, not
in any RK pairings hypothesis. Actual rank and exact scalar separation
force the same polynomial correction at each adjacent shift.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace Order15MinimalHead.DeletedPencil
variable {h : Order15MinimalHead A b} (D : h.DeletedPencil)

def originalClockShift (A : Fin 20 → Fin 20 → K) (v : Vec K 20) (i : ℕ) : Vec K 20 :=
  ((diag (nodes A))^i) v

structure PaidShiftProfiles (v : Vec K 20) (m q n : ℕ) where
  poly : Fin (m+1) → K[X]
  tail : Fin (m+1) → Vec K 20
  degree : ∀ i,(poly i).natDegree≤q
  origin : ∀ i,(poly i).eval 0=0
  quiet : ∀ i,∀ Q : K[X],Q.natDegree≤3 → unitIntegral (poly i*((1-X)*Q))=0
  paid : ∀ i,tail i∈chain (diag (nodes A)) h.U h.w n
  decomposition : ∀ i,deleteTerminal K 19 (originalClockShift A v i.val)=
    deleteTerminal K 19 (evalNodes A (poly i)+tail i)
  adjacent : ∀ i : Fin m,∃ a : K,poly i.succ=X*poly i.castSucc+C a*D.D

set_option maxHeartbeats 1700000 in
theorem paid_shift_profiles (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    {v : Vec K 20} {m q n : ℕ} (q10 : q≤10) (n0 : 0<n) (n3 : n≤h.length+3)
    (shape : deletedTreeSpace A 10=deletedScalarOrbit A q⊔deletedHeadOrbit A h.U h.w n)
    (reduce : ∀ {P : K[X]},P.natDegree≤q+1 →
      deleteTerminal K 19 (evalNodes A P)∈deletedHeadOrbit A h.U h.w (n+1) →
        ∃ a : K,P=C a*D.D)
    (pay : ∀ i : Fin (m+1),originalClockShift A v i.val∈zeroSpace A 10) :
    Nonempty (D.PaidShiftProfiles v m q n) := by
  let d := deleteTerminal K 19
  let C' := diag (nodes A)
  let Cb := deletedClock A
  let L := deletedHeadOrbit A h.U h.w
  let e := d.comp (evaluateColumn A)
  let x (i : Fin (m+1)) := originalClockShift A v i.val
  have ex (i : Fin (m+1)) := h.pure_parts ho H (j:=10) (by decide) q10 n3 shape (pay i)
  choose P pd po pm T tpay id using ex
  have dec (i : Fin (m+1)) : d (x i)=e (P i)+d (T i) := by
    change deleteTerminal K 19 (originalClockShift A v i.val)=
      deleteTerminal K 19 (evaluateColumn A (P i))+deleteTerminal K 19 (T i)
    rw [←map_add,evaluateColumn_eq]
    exact id i
  refine ⟨⟨P,T,pd,po,fun i Q q => pm i Q (by omega),tpay,id,?_⟩⟩
  intro i
  have dc (P : K[X]) : Cb (e P)=e (X*P) := by
    change diag (deleteTerminal K 19 (nodes A)) (d (evaluateColumn A P))=d (evaluateColumn A (X*P))
    rw [←deleteTerminal_diag,evaluateColumn_clock]
  have step : d (x i.succ)=Cb (d (x i.castSucc)) := by
    change d ((C'^(i.val+1)) v)=_
    rw [pow_succ',mul_apply_eq_comp]
    rfl
  have eq : e (P i.succ)+d (T i.succ)=e (X*P i.castSucc)+Cb (d (T i.castSucc)) := by
    rw [←dec i.succ,step,dec i.castSucc,map_add,dc]
  have scalar : e (P i.succ-X*P i.castSucc)=Cb (d (T i.castSucc))-d (T i.succ) := by
    rw [map_sub]
    linear_combination eq
  have pool (j : Fin (m+1)) : d (T j)∈L n := by
    change deleteTerminal K 19 (T j)∈deletedHeadOrbit A h.U h.w n
    rw [deletedHeadOrbit_eq]
    exact Submodule.mem_map_of_mem (tpay j)
  have rel : e (P i.succ-X*P i.castSucc)∈L (n+1) := by
    have k : L n⊔(L n).map Cb=L (n+1) := deletedHeadOrbit_step h.maximal.2.1 n0
    rw [scalar,←k]
    exact (L n⊔(L n).map Cb).sub_mem
      ((le_sup_right : (L n).map Cb≤L n⊔(L n).map Cb)
        (Submodule.mem_map_of_mem (pool i.castSucc)))
      ((le_sup_left : L n≤L n⊔(L n).map Cb) (pool i.succ))
  have deg := (natDegree_sub_le (P i.succ) (X*P i.castSucc)).trans
    (max_le ((pd i.succ).trans (Nat.le_succ q)) (natDegree_mul_le.trans (by
      rw [natDegree_X,add_comm]
      exact Nat.add_le_add_right (pd i.castSucc) 1)))
  obtain ⟨a,ha⟩ := reduce deg rel
  exact ⟨a,by linear_combination ha⟩

theorem unfolded_paid_shifts (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (unfolded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∉deletedTreeSpace A 7)
    {v : Vec K 20} {m : ℕ} (pay : ∀ i : Fin (m+1),originalClockShift A v i.val∈zeroSpace A 10) :
    Nonempty (D.PaidShiftProfiles v m 7 (h.length+3)) := by
  have shape : deletedTreeSpace A 10=deletedScalarOrbit A 7⊔deletedHeadOrbit A h.U h.w (h.length+3) := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨he,_⟩|⟨_,b⟩
    · exact (unfolded he).elim
    · exact b 3 (by decide)
  exact D.paid_shift_profiles ho H (by decide) (by omega) le_rfl shape
    (D.unfolded_scalar_reduces ha ho H unfolded) pay

theorem folded_paid_shifts (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (folded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7)
    {v : Vec K 20} {m : ℕ} (pay : ∀ i : Fin (m+1),originalClockShift A v i.val∈zeroSpace A 10) :
    Nonempty (D.PaidShiftProfiles v m 10 h.length) := by
  have shape : deletedTreeSpace A 10=deletedScalarOrbit A 10⊔deletedHeadOrbit A h.U h.w h.length := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨_,b⟩|⟨he,_⟩
    · exact b 3 (by decide)
    · exact (he folded).elim
  exact D.paid_shift_profiles ho H le_rfl h.length_pos (by omega) shape
    (D.folded_scalar_reduces ha ho H folded) pay

end Order15MinimalHead.DeletedPencil
end
end RKCert.Paired

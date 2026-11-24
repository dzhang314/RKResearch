module

public import RKCert.Dirk15PaidProductScalars

@[expose] public section

/-! # A truly clock-local paid grade-ten product has no scalar part

The exact paid (1-X) moment transport kills the scalar part in both
terminal-deleted growth modes. This result itself requires no
multiplication closure of the invariant core.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

namespace Order15MinimalHead.DeletedPencil
variable {h : Order15MinimalHead A b} (D : h.DeletedPencil)

set_option maxHeartbeats 1800000 in
theorem localized_pure_tail (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    {n q : ℕ} (n0 : 0<n) (pay : n≤h.length+3) (qd : q≤10)
    (form : deletedTreeSpace A 10=deletedScalarOrbit A q⊔deletedHeadOrbit A h.U h.w n)
    (reduce : ∀ {P : K[X]},P.natDegree≤q+1 →
      deleteTerminal K 19 (evalNodes A P)∈deletedHeadOrbit A h.U h.w (n+1) →
        ∃ a : K,P=C a*D.D)
    {v : Vec K 20} (hv : v∈zeroSpace A 10) (clock : K)
    (hLocal : diag (nodes A) v=clock • v) :
    deleteTerminal K 19 v∈deletedHeadOrbit A h.U h.w n := by
  let d := deleteTerminal K 19
  let B := deletedClock A
  let e := d.comp (evaluateColumn A)
  let L := deletedHeadOrbit A h.U h.w
  obtain ⟨P,pd,p0,pq,t,ht,eq⟩ := h.pure_parts ho H (j:=10) (by decide) qd pay form hv
  have eqV : d v=e P+d t := by
    change d v=d (evaluateColumn A P)+d t
    rw [←map_add,evaluateColumn_eq]
    exact eq
  have dt : d t∈L n := by
    change deleteTerminal K 19 t∈deletedHeadOrbit A h.U h.w n
    rw [deletedHeadOrbit_eq]
    exact Submodule.mem_map_of_mem ht
  have ep : B (e P)=e (X*P) := by
    change (diag (d (nodes A))) (d (evaluateColumn A P))=d (evaluateColumn A (X*P))
    rw [←deleteTerminal_diag,evaluateColumn_clock]
  have bv : B (d v)=clock • d v := by
    change (diag (d (nodes A))) (d v)=_
    rw [←deleteTerminal_diag,hLocal,map_smul]
  rw [eqV,map_add,ep,smul_add] at bv
  have ev : e ((X-C clock)*P)=clock • d t-B (d t) := by
    rw [sub_mul,map_sub,←smul_eq_C_mul,map_smul]
    linear_combination bv
  have hP : e ((X-C clock)*P)∈L (n+1) := by
    have ex : L n⊔(L n).map B=L (n+1) := deletedHeadOrbit_step h.maximal.2.1 n0
    rw [ev,←ex]
    exact (L n⊔(L n).map B).sub_mem ((le_sup_left : L n≤_) ((L n).smul_mem clock dt))
      ((le_sup_right : (L n).map B≤_) (Submodule.mem_map_of_mem dt))
  have bound : ((X-C clock)*P).natDegree≤q+1 := natDegree_mul_le.trans (by
    rw [natDegree_X_sub_C,add_comm]; exact Nat.add_le_add_right pd 1)
  obtain ⟨a,as⟩ := reduce bound hP
  have vanish : P=0 := by
    by_cases az : a=0
    · rw [az,map_zero,zero_mul] at as
      exact (mul_eq_zero.mp as).resolve_left (monic_X_sub_C clock).ne_zero
    · by_contra pn
      have de := congrArg natDegree as
      rw [natDegree_mul (monic_X_sub_C clock).ne_zero pn,natDegree_X_sub_C,natDegree_C_mul az] at de
      have pd7 : P.natDegree≤7 := by have u := D.dmax; omega
      obtain ⟨T,et⟩ := clock_dvd_of_eval_origin p0
      obtain ⟨G,eg⟩ := clock_dvd_of_eval_origin D.origin
      have Tn : T≠0 := fun z => pn (by rw [et,z,mul_zero])
      have td : T.natDegree≤6 := by
        rw [et,natDegree_mul X_ne_zero Tn,natDegree_X] at pd7
        omega
      have r : X*T=C clock*T+C a*G := by
        apply mul_left_cancel₀ X_ne_zero
        rw [et,eg] at as
        linear_combination as
      have qT : jacobiPair T 1=0 := by
        have s := pq 1 (by simp)
        rw [et,mul_one,show X*T*(1-X)=X*(1-X)*T by ac_rfl] at s
        simpa only [jacobiPair,mul_one] using s
      have qG : JacobiQuiet G 5 := by
        intro i hi
        have s := D.quiet (X^i) (by rwa [natDegree_X_pow])
        rw [eg,show X*G*((1-X)*X^i)=X*(1-X)*G*X^i by ac_rfl] at s
        exact s
      have t0 := jacobiPair_detect T td (jacobiQuiet_extend (jacobiQuiet_local clock a r qT qG))
      exact Tn t0
  change d v∈L n
  rw [eqV,vanish,map_zero,zero_add]
  exact dt

include D in
theorem unfolded_localized_pure_tail (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (unfolded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∉deletedTreeSpace A 7)
    {v : Vec K 20} (hv : v∈zeroSpace A 10) (clock : K) (hLocal : diag (nodes A) v=clock • v) :
    deleteTerminal K 19 v∈deletedHeadOrbit A h.U h.w (h.length+3) := by
  have eq : deletedTreeSpace A 10=deletedScalarOrbit A 7⊔deletedHeadOrbit A h.U h.w (h.length+3) := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨e,_⟩|⟨_,b⟩
    · exact (unfolded e).elim
    · exact b 3 (by decide)
  exact D.localized_pure_tail ho H (by omega) le_rfl (by decide) eq
    (D.unfolded_scalar_reduces ha ho H unfolded) hv clock hLocal

include D in
theorem folded_localized_pure_tail (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (folded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7)
    {v : Vec K 20} (hv : v∈zeroSpace A 10) (clock : K) (hLocal : diag (nodes A) v=clock • v) :
    deleteTerminal K 19 v∈deletedHeadOrbit A h.U h.w h.length := by
  have eq : deletedTreeSpace A 10=deletedScalarOrbit A 10⊔deletedHeadOrbit A h.U h.w h.length := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨_,b⟩|⟨e,_⟩
    · exact b 3 (by decide)
    · exact (e folded).elim
  exact D.localized_pure_tail ho H h.length_pos (by omega) le_rfl eq
    (D.folded_scalar_reduces ha ho H folded) hv clock hLocal

end Order15MinimalHead.DeletedPencil
end
end RKCert.Paired

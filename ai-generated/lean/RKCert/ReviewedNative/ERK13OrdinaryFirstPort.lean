module

public import RKCert.ReviewedNative.NativeLiveCore
public import RKCert.ReviewedNative.NativeWeightXSixResidue

import RKCert.ReviewedNative.CausalStage
import RKCert.ReviewedNative.OddForwardBudget
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Ordinary physical first ports for the clean order-13 quartic head

The clean-square producer is upstream. This consumer needs only the
actual grade-four head and grade-seven cover that it supplies. The
cubic weight-X scalar cut is an independent scalar premise.
-/
namespace RKResearch.Certified.Graded.ERK13OrdinaryFirstPort

open RKResearch Polynomial Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
variable {G R Q : K[X]}

/-- Only data obtained on the actual original rows, with no terminal line. -/
structure CleanHead (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (G R Q : K[X]) : Prop where
  corePaid : U ≤ zeroSpace A 4
  coreStable : U.map (diag (nodes A)) ≤ U
  coreClosed : ∀ u ∈ U, ∀ v ∈ U, u*v ∈ U
  headPaid : w ∈ zeroSpace A 4
  headOffCore : ∀ i, LiveCore.live U i → w i = 0
  headAmplitude : ∀ i, w i ≠ 0 → w i = R.eval (nodes A i)
  headCover : zeroSpace A 7 ≤ chain (diag (nodes A)) U w 4
  meshPaid : evalNodes A G ∈ zeroSpace A 7
  meshDegree : G.natDegree = 7
  profileDegree : R.natDegree = 4
  complementDegree : Q.natDegree = 3
  factor : G = R*Q

private theorem degree_positive_ne_zero {P : K[X]} (h : 0 < P.natDegree) : P ≠ 0 := by
  intro p0
  simpa [p0] using h

private theorem ordinary_separation_seven (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 13 A b) (H : K[X]) (hd : H.natDegree ≤ 6)
    (ev : evalNodes A H ∈ zeroSpace A 7) : H = 0 := by
  rw [evalNodes_eq_coeffEval A H hd] at ev
  have e := coeff_separated_next (q:=6) ha ho (by decide) _ ev
  ext n
  rw [coeff_zero]
  by_cases hn : n ≤ 6
  · exact congrFun e (⟨n,by omega⟩ : Fin 7)
  · exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))

/-- Match the core exactly and match the pure head with its paid mask.
A first mismatch is a genuine original row outside both supports. -/
theorem CleanHead.first_physical_mask (L : CleanHead A U w G R Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b)
    (M : K[X]) {j : ℕ} (j4 : 4 ≤ j) (j7 : j+1 ≤ 7)
    (mn : M ≠ 0) (hd : (M*R).natDegree ≤ j)
    (wpay : weightedEval (nodes A) w M ∈ zeroSpace A j) :
    ∃ i : Fin 19, ¬LiveCore.live U i ∧ w i = 0 ∧ Q.IsRoot (nodes A i) ∧
      (M*R).eval (nodes A i) ≠ 0 ∧ (primitive (M*R)).eval (nodes A i) = 0 := by
  classical
  let H := M*R
  have hn : H ≠ 0 := mul_ne_zero mn (degree_positive_ne_zero (by rw [L.profileDegree]; decide))
  have hdeg : H.natDegree ≤ j := hd
  obtain ⟨e,he,emask⟩ := LiveCore.exists_live_indicator U L.coreClosed
  let m : Fin 19 → K := fun i => H.eval (nodes A i)*e i
  have hm : m ∈ U :=
    clock_function_mem (fun v hv => L.coreStable (Submodule.mem_map_of_mem hv)) H.eval he
  let y := weightedEval (nodes A) w M + m
  have hy : y ∈ zeroSpace A j :=
    (zeroSpace A j).add_mem wpay (zeroSpace_mono A j4 (L.corePaid hm))
  let z := evalNodes A H-y
  have zi (i : Fin 19) :
      z i = H.eval (nodes A i) - (M.eval (nodes A i)*w i+H.eval (nodes A i)*e i) := by
    simp only [z,y,m,Pi.sub_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply]
  have zn : z ≠ 0 := by
    intro zz
    have eq : evalNodes A H = y := sub_eq_zero.mp zz
    have ej : evalNodes A H ∈ zeroSpace A j := eq.symm ▸ hy
    exact hn (ordinary_separation_seven ha ho H (hdeg.trans (by omega))
      (zeroSpace_mono A (by omega : j≤7) ej))
  have existsRow : ∃ k : ℕ, ∃ i : Fin 19, i.val = k ∧ z i ≠ 0 := by
    by_contra no
    apply zn
    ext i
    exact not_not.mp (fun ni => no ⟨i.val,i,rfl,ni⟩)
  obtain ⟨i,ik,iz⟩ := Nat.find_spec existsRow
  have pre (r : Fin 19) (hr : r.val < i.val) : z r = 0 := by
    by_contra rz
    exact Nat.find_min existsRow (hr.trans_le ik.le) ⟨r,rfl,rz⟩
  have dead : ¬ LiveCore.live U i := by
    intro il
    apply iz
    simp [zi,L.headOffCore i il,emask i,il]
  have iw : w i = 0 := by
    by_contra iw
    apply iz
    rw [zi,L.headAmplitude i iw,emask i,if_neg dead]
    simp [H]
  have ip : H.eval (nodes A i) ≠ 0 := by
    simpa [zi,iw,emask i,dead] using iz
  have atRow {v : Fin 19 → K} (hv : v ∈ zeroSpace A 7) : v i = 0 := by
    obtain ⟨a,ha',S,_,eq⟩ := HeadFiber.exists_poly (L.headCover hv)
    rw [eq]
    simp only [Pi.add_apply,LiveCore.val_eq_zero_of_not_live dead ha',
      weightedEval_apply,iw,mul_zero,zero_mul,zero_add]
  have gi : G.eval (nodes A i) = 0 := atRow L.meshPaid
  have ri : R.eval (nodes A i) ≠ 0 := by
    intro rz
    exact ip (by simp [H,rz])
  have qi : Q.IsRoot (nodes A i) := by
    change Q.eval (nodes A i) = 0
    rw [L.factor,eval_mul] at gi
    exact (mul_eq_zero.mp gi).resolve_left ri
  have az : mat A z i = 0 := causal_mat ha i z (fun r hr => pre r hr)
  have d : mat A (evalNodes A H)-evalNodes A (primitive H) ∈ zeroSpace A (j+1) :=
    primitive_defect A H hdeg
  have ay : mat A y ∈ zeroSpace A (j+1) := mat_zeroSpace_charZero A j hy
  have pr : evalNodes A (primitive H)-mat A z ∈ zeroSpace A 7 := by
    apply zeroSpace_mono A j7
    rw [show evalNodes A (primitive H)-mat A z =
      mat A y-(mat A (evalNodes A H)-evalNodes A (primitive H)) by
      simp only [z,map_sub]; abel]
    exact (zeroSpace A (j+1)).sub_mem ay d
  have atPrimitive := atRow pr
  rw [Pi.sub_apply,az,sub_zero,evalNodes_apply] at atPrimitive
  exact ⟨i,dead,iw,qi,ip,atPrimitive⟩

/-- The mask 1 is already paid at grade four. It is the port used when
the origin belongs to the quartic rather than the cubic complement. -/
theorem CleanHead.first_unit_mask (L : CleanHead A U w G R Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) :
    ∃ i : Fin 19, Q.IsRoot (nodes A i) ∧ R.eval (nodes A i) ≠ 0 ∧
      (primitive R).eval (nodes A i) = 0 := by
  have eq : weightedEval (nodes A) w (1 : K[X]) = w := by
    ext i
    simp only [weightedEval_apply,eval_one,one_mul]
  have d : ((1 : K[X])*R).natDegree ≤ 4 := by rw [one_mul,L.profileDegree] <;> omega
  obtain ⟨i,_,_,qi,ip,pr⟩ := L.first_physical_mask ha ho 1 (j:=4)
    (by decide) (by decide) one_ne_zero d (eq.symm ▸ L.headPaid)
  exact ⟨i,qi,by simpa only [one_mul] using ip,by simpa only [one_mul] using pr⟩

/-- The mask X buys one clock step and advances only to grade six. -/
theorem CleanHead.first_X_mask (L : CleanHead A U w G R Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) :
    ∃ i : Fin 19, Q.IsRoot (nodes A i) ∧ (X*R).eval (nodes A i) ≠ 0 ∧
      (primitive (X*R)).eval (nodes A i) = 0 := by
  have eq : weightedEval (nodes A) w (X : K[X]) = diag (nodes A) w := by
    ext i
    simp only [weightedEval_apply,eval_X,diag_apply]
  have pay : diag (nodes A) w ∈ zeroSpace A 5 := diag_zeroSpace A 4 L.headPaid
  have rn : R ≠ 0 := degree_positive_ne_zero (by rw [L.profileDegree]; decide)
  have d : (X*R).natDegree ≤ 5 := by rw [natDegree_X_mul rn,L.profileDegree] <;> omega
  obtain ⟨i,_,_,qi,ip,pr⟩ := L.first_physical_mask ha ho X (j:=5)
    (by decide) (by decide) X_ne_zero d (eq.symm ▸ pay)
  exact ⟨i,qi,ip,pr⟩

theorem CleanHead.mesh_moments (L : CleanHead A U w G R Q) (ho : HasOrder 13 A b)
    (k : Fin 6) : (primitive (X^k.val*G)).eval 1 = 0 := by
  have hk := k.isLt
  have e := (probe_evalNodes ho G k.val (by rw [L.meshDegree]; omega)).symm
  exact e.trans (probe_zeroSpace (k:=k.val) ho (by omega) L.meshPaid)

/-- The scalar input for the cubic/cubic origin split is independent
of all tableau/rank hypotheses. -/
def CubicWeightXCut (K : Type*) [Field K] : Prop :=
  ∀ (P N : K[X]) (t : K), P.natDegree = 3 → N.natDegree = 3 → N.IsRoot t →
    (∀ k : Fin 6, (primitive (X^k.val*(X*(P*N)))).eval 1 = 0) →
    (primitive (X*P)).eval t ≠ 0

/-- This excludes the clean ordinary quartic packet, not all ordinary
radii or all original nineteen-stage tableaux. -/
theorem CleanHead.impossible_of_cubic_cut (L : CleanHead A U w G R Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b)
    (cut : CubicWeightXCut K) : False := by
  have rn : R ≠ 0 := degree_positive_ne_zero (by rw [L.profileDegree]; decide)
  have qn : Q ≠ 0 := degree_positive_ne_zero (by rw [L.complementDegree]; decide)
  by_cases h0 : R.eval 0 = 0
  · obtain ⟨P,hP⟩ : (X : K[X]) ∣ R := by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr h0
    have pn : P ≠ 0 := fun p0 => rn (by rw [hP,p0,mul_zero])
    have pd : P.natDegree = 3 := by
      have rD := L.profileDegree
      rw [hP,natDegree_X_mul pn] at rD
      omega
    have product : G = X*(P*Q) := by rw [L.factor,hP,mul_assoc]
    have tests (k : Fin 6) :
        (primitive (X^k.val*(X*(P*Q)))).eval 1 = 0 := by
      simpa only [product] using L.mesh_moments ho k
    obtain ⟨i,qi,_,pr⟩ := L.first_unit_mask ha ho
    exact (cut P Q _ pd L.complementDegree qi tests) (by simpa only [hP] using pr)
  · have nodes0 : nodes A (0 : Fin 19) = 0 := by
      change (∑ j, A 0 j*1) = 0
      exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]
    have g0 : G.eval 0 = 0 := by
      have h : evalNodes A G (0 : Fin 19) = 0 := origin_zeroSpace ha 7 L.meshPaid
      simpa only [evalNodes_apply,nodes0] using h
    have q0 : Q.eval 0 = 0 := by
      rw [L.factor,eval_mul] at g0
      exact (mul_eq_zero.mp g0).resolve_left h0
    obtain ⟨N,hN⟩ : (X : K[X]) ∣ Q := by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr q0
    have nn : N ≠ 0 := fun n0 => qn (by rw [hN,n0,mul_zero])
    have nd : N.natDegree = 2 := by
      have qD := L.complementDegree
      rw [hN,natDegree_X_mul nn] at qD
      omega
    have product : G = X*(R*N) := by rw [L.factor,hN]; ac_rfl
    have tests (k : Fin 6) :
        (primitive (X^k.val*(X*(R*N)))).eval 1 = 0 := by
      simpa only [product] using L.mesh_moments ho k
    obtain ⟨i,qi,ip,pr⟩ := L.first_X_mask ha ho
    have t0 : nodes A i ≠ 0 := by
      intro z
      exact ip (by rw [eval_mul,eval_X,z,zero_mul])
    have ni : N.IsRoot (nodes A i) := by
      change Q.eval (nodes A i) = 0 at qi
      rw [hN,eval_mul,eval_X] at qi
      exact (mul_eq_zero.mp qi).resolve_left t0
    exact NativeWeightXSix.first_primitive_nonzero_of_six_moments R N _ L.profileDegree nd
      ni tests pr

end
end RKResearch.Certified.Graded.ERK13OrdinaryFirstPort

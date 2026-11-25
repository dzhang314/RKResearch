module

public import RKCert.ReviewedNative.OptionalTerminalMark
public import RKCert.ReviewedNative.NativeLiveCore
public import RKCert.ReviewedNative.NativeWeightXSixResidue

import RKCert.ReviewedNative.CausalStage
import RKCert.ReviewedNative.OddForwardBudget
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The original-row late quartic cut at ERK order 13

This leaf takes the marked grade-six/seven geometry as raw native
submodule facts. It does not import the old mesh, staircase, ghost,
or scalar packet. Only the nonzero-origin pure quartic is consumed.
-/
namespace RKResearch.Certified.Graded.ERK13LateQuartic

open RKResearch Polynomial Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
variable {G P Q : K[X]}

private theorem unmark_before_terminal {j : ℕ} (seed : firstSeed A b = 0)
    (late : coordinate (K:=K) (Fin.last 18) ∉ treeSpace A j)
    {v : Fin 19 → K} (m : v ∈ markedDefectSpace A b j) (t : v ∈ treeSpace A j) :
    v ∈ zeroSpace A j := by
  obtain ⟨x,hx,y,hy,eq⟩ := Submodule.mem_sup.mp m
  rw [terminalMark, if_pos seed] at hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have ty : a • coordinate (Fin.last 18) ∈ treeSpace A j := by
    rw [show a • coordinate (Fin.last 18) = v-x by rw [← eq]; abel]
    exact (treeSpace A j).sub_mem t (zeroSpace_le_treeSpace A j hx)
  have za : a = 0 := by
    by_contra nz
    exact late (((treeSpace A j).smul_mem_iff_of_isUnit
      (isUnit_iff_ne_zero.mpr nz)).mp ty)
  rw [za,zero_smul,add_zero] at eq
  exact eq ▸ hx

/-- The actual marked tree chart yields the defect head cover, with the
ordinary next-grade separation at order 13, not a terminal scalar mesh. -/
theorem late_head_cover_of_tree_chart (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b = 0)
    (late : coordinate (K:=K) (Fin.last 18) ∉ treeSpace A 7)
    (chart : markedTreeSpace A b 7 =
      (coeffEval A 6).range ⊔ chain (diag (nodes A)) U w 4)
    (paid : chain (diag (nodes A)) U w 4 ≤ markedDefectSpace A b 7) :
    markedDefectSpace A b 7 ≤ chain (diag (nodes A)) U w 4 := by
  intro v hv
  have hvT : v ∈ markedTreeSpace A b 7 :=
    (sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl) hv
  rw [chart] at hvT
  obtain ⟨_,⟨a,rfl⟩,z,hz,eq⟩ := Submodule.mem_sup.mp hvT
  let F := ofFn 7 a
  have fd : F.natDegree ≤ 6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
  have ev : evalNodes A F = coeffEval A 6 a := by
    rw [evalNodes_eq_coeffEval A F fd]
    congr 1
    ext i
    exact ofFn_coeff_eq_val_of_lt _ i.isLt
  have hF : evalNodes A F ∈ markedDefectSpace A b 7 := by
    rw [ev, show coeffEval A 6 a = v-z by rw [← eq]; abel]
    exact (markedDefectSpace A b 7).sub_mem hv (paid hz)
  have hF' := unmark_before_terminal seed late hF (evalNodes_mem_treeSpace A F (by omega))
  have F0 := eval_eq_zero_of_coeff_separated
    (coeff_separated_next (q:=6) ha ho (by decide)) F fd hF'
  rw [← ev,F0,map_zero,zero_add] at eq
  exact eq ▸ hz

private theorem mat_marked_six_mem (ha : ∀ i j, i ≤ j → A i j = 0)
    (seed : firstSeed A b = 0) {v : Fin 19 → K} (hv : v ∈ markedDefectSpace A b 6) :
    mat A v ∈ zeroSpace A 7 := by
  have lastKilled : mat A (coordinate (K:=K) (Fin.last 18)) = 0 := by
    ext i
    change row (A i) (coordinate (K:=K) (Fin.last 18)) = 0
    rw [row_coordinate,ha i (Fin.last 18) (Fin.le_last i)]
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  rw [terminalMark,if_pos seed] at hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_add,map_smul,lastKilled,smul_zero,add_zero]
  exact mat_zeroSpace_charZero A 6 hx

/-- The only omitted-row mask needed by the nonzero-origin quartic.
The returned pivot is an original stage. Its primitive vanishes by
strict causality at the first nonzero residual, not by decoding a mesh. -/
theorem first_X_mask_physical (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b = 0) (last : LastActive b (Fin.last 18))
    (core : U ≤ markedDefectSpace A b 6)
    (stable : U.map (diag (nodes A)) ≤ U)
    (closed : ∀ x ∈ U, ∀ y ∈ U, x*y ∈ U)
    (off : ∀ i, LiveCore.live U i → w i = 0)
    (repr : ∀ i, w i ≠ 0 → w i = P.eval (nodes A i))
    (wpay : diag (nodes A) w ∈ markedDefectSpace A b 6)
    (mesh : evalNodes A G ∈ markedDefectSpace A b 7)
    (cover : markedDefectSpace A b 7 ≤ chain (diag (nodes A)) U w 4)
    (pd : P.natDegree = 4) :
    ∃ i : Fin 19, G.eval (nodes A i) = 0 ∧
      (X*P).eval (nodes A i) ≠ 0 ∧ (primitive (X*P)).eval (nodes A i) = 0 := by
  classical
  let H : K[X] := X*P
  have pn : P ≠ 0 := by intro z; rw [z,natDegree_zero] at pd; omega
  have hn : H ≠ 0 := mul_ne_zero X_ne_zero pn
  have hd : H.natDegree = 5 := by dsimp only [H]; rw [natDegree_X_mul pn,pd]
  obtain ⟨e,he,emask⟩ := LiveCore.exists_live_indicator U closed
  let m : Fin 19 → K := fun i => H.eval (nodes A i) * e i
  have hm : m ∈ U :=
    clock_function_mem (fun v hv => stable (Submodule.mem_map_of_mem hv)) H.eval he
  let y : Fin 19 → K := diag (nodes A) w + m
  have hy : y ∈ markedDefectSpace A b 6 :=
    (markedDefectSpace A b 6).add_mem wpay (core hm)
  let z : Fin 19 → K := evalNodes A H-y
  have zi (i : Fin 19) :
      z i = H.eval (nodes A i) - (nodes A i*w i+H.eval (nodes A i)*e i) := by
    simp only [z,y,m,Pi.sub_apply,Pi.add_apply,evalNodes_apply,diag_apply]
  have zn : z ≠ 0 := by
    intro zz
    have eq : evalNodes A H = y := sub_eq_zero.mp zz
    have eh : evalNodes A H ∈ markedDefectSpace A b 6 := eq.symm ▸ hy
    exact hn (eval_eq_zero_of_coeff_separated
      (marked_coeff_separated (q:=6) (j:=6) ha ho last (by decide) (by decide) (by decide))
      H (by omega) eh)
  have existsRow : ∃ k : ℕ, ∃ i : Fin 19, i.val = k ∧ z i ≠ 0 := by
    by_contra no
    apply zn
    ext j
    exact not_not.mp (fun nj => no ⟨j.val,j,rfl,nj⟩)
  obtain ⟨i,ik,iz⟩ := Nat.find_spec existsRow
  have pre (j : Fin 19) (hj : j.val < i.val) : z j = 0 := by
    by_contra hjz
    exact Nat.find_min existsRow (hj.trans_le ik.le) ⟨j,rfl,hjz⟩
  have dead : ¬ LiveCore.live U i := by
    intro il
    apply iz
    simp [zi,off i il,emask i,il]
  have iw : w i = 0 := by
    by_contra iw
    apply iz
    rw [zi,repr i iw,emask i,if_neg dead]
    simp [H]
  have ip : H.eval (nodes A i) ≠ 0 := by
    simpa [zi,iw,emask i,dead] using iz
  have atRow {v : Fin 19 → K} (hv : v ∈ markedDefectSpace A b 7) : v i = 0 := by
    obtain ⟨a,ha',R,_,eq⟩ := HeadFiber.exists_poly (cover hv)
    rw [eq]
    simp only [Pi.add_apply,LiveCore.val_eq_zero_of_not_live dead ha',
      weightedEval_apply,iw,mul_zero,zero_mul,zero_add]
  have az : mat A z i = 0 := causal_mat ha i z (fun j hj => pre j hj)
  have d6 : mat A (evalNodes A H)-evalNodes A (primitive H) ∈ zeroSpace A 6 :=
    primitive_defect (q:=5) A H hd.le
  have includeZero : zeroSpace A 7 ≤ markedDefectSpace A b 7 := le_sup_left
  have d7 : mat A (evalNodes A H)-evalNodes A (primitive H) ∈ markedDefectSpace A b 7 :=
    includeZero (zeroSpace_mono A (by decide : 6≤7) d6)
  have ay : mat A y ∈ markedDefectSpace A b 7 :=
    includeZero (mat_marked_six_mem ha seed hy)
  have pr : evalNodes A (primitive H)-mat A z ∈ markedDefectSpace A b 7 := by
    rw [show evalNodes A (primitive H)-mat A z =
      mat A y-(mat A (evalNodes A H)-evalNodes A (primitive H)) by
      simp only [z,map_sub]; abel]
    exact (markedDefectSpace A b 7).sub_mem ay d7
  have ini := atRow pr
  rw [Pi.sub_apply,az,sub_zero,evalNodes_apply] at ini
  exact ⟨i,atRow mesh,ip,ini⟩

/-- The actual late nonzero-origin pure quartic is excluded by exactly six
global primitive moments and the single native original-stage first port. -/
theorem late_nonorigin_quartic_impossible (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b = 0)
    (late : coordinate (K:=K) (Fin.last 18) ∉ treeSpace A 7)
    (last : LastActive b (Fin.last 18))
    (core : U ≤ markedDefectSpace A b 6)
    (stable : U.map (diag (nodes A)) ≤ U)
    (closed : ∀ x ∈ U, ∀ y ∈ U, x*y ∈ U)
    (off : ∀ i, LiveCore.live U i → w i = 0)
    (repr : ∀ i, w i ≠ 0 → w i = P.eval (nodes A i))
    (wpay : diag (nodes A) w ∈ markedDefectSpace A b 6)
    (mesh : evalNodes A G ∈ markedDefectSpace A b 7)
    (cover : markedDefectSpace A b 7 ≤ chain (diag (nodes A)) U w 4)
    (gd : G.natDegree = 7) (pd : P.natDegree = 4)
    (fit : G = P*Q) (p0 : P.eval 0 ≠ 0) : False := by
  have paid : evalNodes A G ∈ zeroSpace A 7 :=
    unmark_before_terminal seed late mesh (evalNodes_mem_treeSpace A G gd.le)
  have g0 : G.eval 0 = 0 := by
    have h := origin_zeroSpace ha 7 paid
    change evalNodes A G (0 : Fin 19) = 0 at h
    have nodes0 : nodes A (0 : Fin 19) = 0 := by
      change (∑ j, A 0 j*1) = 0
      exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]
    simpa only [evalNodes_apply,nodes0] using h
  have q0 : Q.eval 0 = 0 := by
    rw [fit,eval_mul] at g0
    exact (mul_eq_zero.mp g0).resolve_left p0
  obtain ⟨N,hN⟩ : (X : K[X]) ∣ Q := by
    simpa using (dvd_iff_isRoot (a:=(0:K))).mpr q0
  have product : G = X*(P*N) := by rw [fit,hN]; ring
  have pn : P ≠ 0 := by intro z; rw [z,natDegree_zero] at pd; omega
  have gn : G ≠ 0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have nn : N ≠ 0 := fun z => gn (by rw [product,z,mul_zero,mul_zero])
  have nd : N.natDegree = 2 := by
    have gd' := gd
    rw [product,natDegree_X_mul (mul_ne_zero pn nn),natDegree_mul pn nn,pd] at gd'
    omega
  have tests (j : Fin 6) : (primitive (X^j.val*(X*(P*N)))).eval 1 = 0 := by
    have hj := j.isLt
    have e := (probe_evalNodes ho G j.val (by omega)).symm.trans
      (probe_zeroSpace (k:=j.val) ho (by omega) paid)
    simpa only [product] using e
  obtain ⟨i,gi,pi,ti⟩ :=
    first_X_mask_physical ha ho seed last core stable closed off repr wpay mesh cover pd
  have ni : N.IsRoot (nodes A i) := by
    have product' : G = (X*P)*N := by rw [product,mul_assoc]
    rw [product',eval_mul] at gi
    exact (mul_eq_zero.mp gi).resolve_left pi
  exact NativeWeightXSix.first_primitive_nonzero_of_six_moments P N (nodes A i)
    pd nd ni tests ti

end
end RKResearch.Certified.Graded.ERK13LateQuartic

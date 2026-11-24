module

public import RKCert.ReviewedNative.ERKCharZero
public import RKCert.ReviewedNative.TerminalCapacity
public import RKCert.ReviewedNative.NativeFlatClockHead

public section

/-! # Native order-twelve saturation with at most seventeen stages

The dimensions are measured on the original strict tableau. The published
native grade-five surplus removes every rank premise from the entrance.
A prefix is used solely to rule out a zero final physical weight.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Module Reverse RKCert.OneEscape
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}

structure Saturation (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K) : Prop where
  size : s+1=17
  f5 : finrank K (zeroSpace A 5)=5
  f6 : finrank K (zeroSpace A 6)=6
  e6 : finrank K (treeSpace A 6)=13
  firstZero : firstSeed A b=0
  backExact : ∀ n ≤ 4, finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n
  back4 : back A b 4=annih (treeSpace A 6)
  caps : ∀ j ≤ 10, finrank K (treeSpace A j)≤j+7
  terminal : LastActive b (Fin.last s)
  terminalClock : nodes A (Fin.last s)=1
  terminalColumn : coordinate (K:=K) (Fin.last s)∈treeSpace A 6

variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- The measured reverse rank exactly fills a paid annihilator whenever
the forward and reverse dimensions total the original stage count. -/
theorem back_eq_annih_of_rank (ho : HasOrder 12 A b) {j n : ℕ}
    (pay : j+n+2≤12) (count : finrank K (treeSpace A j)+finrank K (back A b n)=s+1) :
    back A b n=annih (treeSpace A j) := by
  have d := finrank_annih (treeSpace A j)
  rw [Fintype.card_fin] at d
  exact Submodule.eq_of_le_of_finrank_le (back_annih ho j n pay) (by omega)

section CharZero
variable [CharZero K]

/-- All ranks, reverse saturation, and the live last coordinate are
forced by reviewed order and the physical stage cap alone. -/
theorem saturation_of_order (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b)
    (cap : s+1≤17) : Saturation A b := by
  have five := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have grow := erk_paid_rank_interval ha ho (a:=5) (q:=6) (by decide) (by decide) (by decide)
  have room := erk_even_midpoint_budget ha ho (q:=6) (by decide) (by decide)
  have mid := erk_midpoint_tree_rank ha ho (q:=6) (by decide) (by decide)
  simp only [Nat.reduceSub,Nat.reduceMul,Nat.reduceAdd] at grow room mid
  have size : s+1=17 := by omega
  have f5 : finrank K (zeroSpace A 5)=5 := by omega
  have f6 : finrank K (zeroSpace A 6)=6 := by omega
  have e6 : finrank K (treeSpace A 6)=13 := by omega
  obtain ⟨z,hb,phb⟩ := reverse_capacity_paid ha ho (j:=6) (n:=4) (by decide) (by omega)
  have pd : finrank K (primitiveBack A b 4)=4 := by
    rw [phb]
    have d := finrank_annih (treeSpace A 6)
    rw [Fintype.card_fin,e6] at d
    omega
  have backN (n : ℕ) (hn : n≤4) :
      finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n := by
    have g := primitiveBack_interval ha ho n (4-n) (by omega)
    rw [show n+(4-n)=4 by omega,pd] at g
    have lo := back_finrank ha ho n (by omega)
    rw [first_dim_zero z,zero_add] at lo
    have inc := back_le_primitiveBack (A:=A) (b:=b) n
    have hi := Submodule.finrank_mono inc
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩
  have caps (j : ℕ) (hj : j≤10) : finrank K (treeSpace A j)≤j+7 := by
    have h := backward_count ha ho j (10-j) (by omega)
    omega
  have live : b (Fin.last s)≠0 := by
    intro zero
    have tail (i : Fin (s+1)) (hi : s ≤ i.val) : b i=0 := by
      have e : i=Fin.last s := Fin.ext (by change i.val=s; have := i.isLt; omega)
      rwa [e]
    let len : s≤s+1 := Nat.le_succ s
    have pref := prefix_hasOrder_of_suffix_zero ha ho len tail
    have lo := pref.erk_grade_five_charZero_stages_field (prefix_strict_lower ha len) (by decide)
    omega
  have L : LastActive b (Fin.last s) :=
    ⟨live,fun i hi => (not_lt_of_ge (Fin.le_last i) hi).elim⟩
  obtain ⟨_,one,_,t⟩ := reverse_capacity_terminal ha ho (j:=6) (n:=4)
    (by decide) (by omega) L
  exact ⟨size,f5,f6,e6,z,backN,hb,caps,L,one,t _ le_rfl⟩

/-- The native intrinsic single head at the exact F₅→F₆ step, with the
outgoing Hermite gain enforcing length at least two. -/
theorem exists_order_twelve_head (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) : ∃ r U w, 2≤r ∧ FlatClockHead A 5 1 r U w := by
  have sep := explicit_coeff_separated ha ho (q:=6) (by decide)
  obtain ⟨r,U,w,H⟩ := flat_clock_head ha (j:=5) (d:=1) sep (by decide) (by decide)
    (by simp only [Nat.reduceAdd,S.f5,S.f6,le_refl])
  have pol : PolySeparated A 6 := PolySeparated.of_coeff sep
  have gain := clock_invariant_outgoing ha (pol.mono (by decide : 5≤6))
    H.coreInside H.coreStable
  have rank := H.baseRank
  simp only [Nat.reduceAdd,Nat.reduceDiv,S.f6] at gain
  rw [S.f5] at rank
  exact ⟨r,U,w,by omega,H⟩

end CharZero

/-- Native product payment makes the actual live terminal coordinate
annihilate the entire grade-five defect space. -/
theorem grade_five_zero_at_terminal (ho : HasOrder 12 A b) (S : Saturation A b)
    {v : Fin (s+1) → K} (hv : v∈zeroSpace A 5) : v (Fin.last s)=0 := by
  have z := probe_zeroSpace (k:=0) ho (by decide : 0+(5+6)+1≤12)
    (zeroSpace_mul_treeSpace ho (by decide : 6+1≤12) hv S.terminalColumn)
  change row (fun i => b i * (nodes A i)^0) (diag v (coordinate (Fin.last s)))=0 at z
  rw [←row_diag,row_coordinate,diag_apply] at z
  simp only [pow_zero,mul_one] at z
  exact (mul_eq_zero.mp z).resolve_right S.terminal.live

/-- The same physical row annihilates the next homogeneous grade. The
actual one-rank clock growth, not a separate moment at order thirteen,
justifies the pass from grade five to grade six. -/
theorem grade_six_zero_at_terminal [CharZero K] (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 12 A b) (S : Saturation A b) {v : Fin (s+1) → K}
    (hv : v∈zeroSpace A 6) : v (Fin.last s)=0 := by
  have sep : PolySeparated A 5 := PolySeparated.of_coeff (explicit_coeff_separated ha ho (by decide))
  have esc : ¬ (zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5 := by
    intro inv
    have g := clock_invariant_outgoing ha sep le_rfl inv
    simp only [Nat.reduceAdd,Nat.reduceDiv,S.f5,S.f6] at g
    omega
  have eq := zeroSpace_clock_step_of_unit (A:=A) (n:=5)
    (by simp only [Nat.reduceAdd,S.f5,S.f6,le_refl]) esc
  rw [show zeroSpace A 6=zeroSpace A 5 ⊔ (zeroSpace A 5).map (diag (nodes A)) from eq] at hv
  obtain ⟨x,hx,_,⟨y,hy,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hv
  simp only [Pi.add_apply,diag_apply,grade_five_zero_at_terminal ho S hx,
    grade_five_zero_at_terminal ho S hy,mul_zero,zero_add]

end RKResearch.Certified.Graded.ERK12

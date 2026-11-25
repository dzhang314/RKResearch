module

public import RKCert.ReviewedNative.ERK13NativeMarkedEscapeChart

import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Original grade-seven/eight marked purity and the degree-six refund

The mark is first removed at an actually paid grade, not identified with
an entire clock-one fibre. The degree-six alias earns one refund by a
nonzero genuine probe, rather than by declaring the seventh defect flag pure. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape MarkedAdjacent
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w x : Fin 19 → K} {r a : ℕ} {G : K[X]}

/-- Adjacent purity of the actual marked chart, prior to the refund. -/
theorem NativeMarkedEscapeChart.adjacent_marked_band
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {j : ℕ} (grade : j=7 ∨ j=8)
    (shifts : ∀ i≤j-6, ((diag (nodes A))^i) x∈markedDefectSpace A b j) :
    ∀ i≤j-6, ((diag (nodes A))^i) x∈markedEscapeHeadBand A b U w (r+2+(j-(a+1))) := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  let m := j-(a+1)
  have jm : a+1+m=j := by dsimp [m]; omega
  let Z := markedEscapeHeadBand A b U w (r+2+m)
  let W := markedEscapeHeadBand A b U w (r+2+(m+1))
  have chart := H.chart m (by omega)
  rw [jm] at chart
  have cover : markedDefectSpace A b j ≤ (coeffEval A a).range⊔Z :=
    (sup_le_sup (zeroSpace_le_treeSpace A j) le_rfl).trans chart.le
  have bandPaid : Z≤markedDefectSpace A b (7+m) :=
    sup_le_sup (escapeHeadBand_paid_from_seven H.head m) le_rfl
  have next : Z⊔Z.map (diag (nodes A))≤W := by
    have step := (markedEscapeHeadBand_clock_step (b:=b) (w:=w)
      H.head.head.coreStable (n:=r+2+m) (by omega)).le
    change markedEscapeHeadBand A b U w (r+2+m) ⊔ _ ≤
      markedEscapeHeadBand A b U w (r+2+(m+1))
    rw [show r+2+(m+1)=r+2+m+1 by omega]
    exact step
  have gd : evalNodes A G∈markedEscapeHeadBand A b U w (r+2) := first_alias_mem_markedEscapeHeadBand H.head H.first
  have extend : markedEscapeHeadBand A b U w (r+2) ≤ W :=
    sup_le_sup (escapeHeadBand_mono (A:=A) (U:=U) (w:=w)
      (by omega : r+2 ≤ r+2+(m+1))) le_rfl
  have gW : evalNodes A G∈W := extend gd
  have mesh := (H.mesh_moments ha ho).2.2
  have mom : ∀ k<(a+6-j)+(j-6)-1, endpointMoment K k G=0 :=
    fun k hk=>mesh k (by omega)
  exact pure_of_paid_marked_adjacent_clocks (h:=7+m) (j:=j) (a:=a) (n:=a+6-j) (m:=j-6)
    ha ho H.head.paidRanks.lastActive (by decide) (by omega) (by omega)
    (by omega) (by omega) (by omega) cover bandPaid next
    (H.separated (m+1) (by omega)) H.first.degree gW mom shifts

/-- A vector already in the unmarked native defect flag cannot borrow a
literal mark in a head band whose grade still pays the zero-th probe. -/
theorem escapeHeadBand_strip_terminal
    (ho : HasOrder 13 A b) (L : LastActive b (Fin.last 18))
    (seed : firstSeed A b=0) {j h n : ℕ} (jh : j≤h) (paid : h+1≤13)
    (head : escapeHeadBand A U w n≤zeroSpace A h)
    (hx : x∈zeroSpace A j) (tagged : x∈markedEscapeHeadBand A b U w n) :
    x∈escapeHeadBand A U w n := by
  obtain ⟨v,hv,m,hm,e⟩ := Submodule.mem_sup.mp tagged
  rw [terminalMark,ite_eq_left seed] at hm
  obtain ⟨factor,rfl⟩ := Submodule.mem_span_singleton.mp hm
  have paidMark : factor • coordinate (K:=K) (Fin.last 18) ∈ zeroSpace A h := by
    rw [show factor • coordinate (K:=K) (Fin.last 18)=x-v by rw [←e]; abel]
    exact (zeroSpace A h).sub_mem (zeroSpace_mono A jh hx) (head hv)
  have factorZero : factor=0 := by
    by_contra nz
    exact last_coordinate_not_defect ho L paid
      (((zeroSpace A h).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nz)).mp paidMark)
  rw [factorZero,zero_smul,add_zero] at e
  exact e ▸ hv

private theorem probe_clock_powers (v : Fin 19 → K) (m k : ℕ) :
    probe A b k (((diag (nodes A))^m) v)=probe A b (k+m) v := by
  induction m generalizing k with
  | zero => simp only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply,Nat.add_zero]
  | succ m ih =>
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply,probe_clock_shift,
      ih (k+1),show k+1+m=k+(m+1) by omega]

private theorem degree_six_next_moment_ne
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    unitMoment K 6 G≠unitMoment K 0 G := by
  have pay := H.mesh_moments ha ho
  have dg : G.natDegree=6 := H.first.degree
  intro z
  have out := NativeMoments.endpoint_moments_detect dg.le pay.1 (fun k => by
    rw [←endpointMoment_apply]
    change unitMoment K k.val G-unitMoment K (k.val+1) G=0
    have lo := pay.2.1 k.val (by have := k.isLt; omega)
    have hi : unitMoment K (k.val+1) G=unitMoment K 0 G := by
      by_cases e : k.val+1=6
      · rwa [e]
      · exact pay.2.1 _ (by have := k.isLt; omega)
    rw [lo,hi,sub_self])
  rw [out,natDegree_zero] at dg
  omega

/-- Exact one-slot refund in the actual degree-six first escape. The
proof uses the native probe of index `6-m`, so the refund is available
for every `m≤6`, whether or not F7 has its extra mode. -/
theorem NativeMarkedEscapeChart.refund_one_head_slot
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {m : ℕ} (mo : m≤6)
    (hx : x∈zeroSpace A (6+m)) (long : x∈escapeHeadBand A U w (r+2+m)) :
    x∈escapeHeadBand A U w (r+1+m) := by
  have diff := degree_six_next_moment_ne H ha ho
  have dg : G.natDegree=6 := H.first.degree
  have gZ : evalNodes A G∈markedEscapeHeadBand A b U w (r+2) := first_alias_mem_markedEscapeHeadBand H.head H.first
  obtain ⟨d,hd,t,ht,eq⟩ := Submodule.mem_sup.mp gZ
  have p0 : probe A b 0 d=0 := probe_zeroSpace ho (by decide)
    (escapeHeadBand_paid_from_seven H.head 0 (by simpa only [Nat.add_zero] using hd))
  have t0 : probe A b 0 t=unitMoment K 0 G := by
    have e := congrArg (probe A b 0) eq
    rw [map_add,p0,zero_add,probe_evalNodes ho G 0 (by omega)] at e
    exact e
  have t6 : probe A b 6 t=unitMoment K 0 G :=
    (probe_terminalMark_equal ha H.head.paidRanks.lastActive ht 6).trans t0
  have d6 : probe A b 6 d≠0 := by
    intro z
    have e := congrArg (probe A b 6) eq
    rw [map_add,z,zero_add,t6,probe_evalNodes ho G 6 (by omega)] at e
    exact diff e.symm
  let D := diag (nodes A)
  have dShift (k : ℕ) : (D^k) d∈escapeHeadBand A U w (r+2+k) := by
    induction k with
    | zero => simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply,Nat.add_zero] using hd
    | succ k ih =>
      rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply,show r+2+(k+1)=r+2+k+1 by omega]
      exact escapeHeadBand_map_succ H.head.head.coreStable (by omega) (Submodule.mem_map_of_mem ih)
  let B := escapeHeadBand A U w (r+1+m)
  let v := (D^(r+1+m)) w
  let k := 6-m
  have bp (u : Fin 19 → K) (hu : u∈B) : probe A b k u=0 :=
    probe_zeroSpace ho (by dsimp [k]; omega) (escapeHeadBand_paid_from_six H.head m hu)
  have longEq : escapeHeadBand A U w (r+2+m)=B⊔(K ∙ v) := by
    rw [show r+2+m=(r+1+m)+1 by omega] <;> rfl
  have fresh : probe A b k ((D^m) d)≠0 := by
    change probe A b (6-m) (((diag (nodes A))^m) d)≠0
    rw [probe_clock_powers,show 6-m+m=6 by omega]
    exact d6
  have dv := dShift m
  rw [longEq] at dv
  have vp : probe A b k v≠0 := by
    intro z
    obtain ⟨u,hu,f,hf,ev⟩ := Submodule.mem_sup.mp dv
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hf
    apply fresh
    rw [←ev,map_add,map_smul,bp u hu,z,smul_zero,add_zero]
  rw [longEq] at long
  obtain ⟨u,hu,f,hf,ev⟩ := Submodule.mem_sup.mp long
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hf
  have px : probe A b k x=0 := probe_zeroSpace ho (by dsimp [k]; omega) hx
  rw [←ev,map_add,map_smul,bp u hu,zero_add,smul_eq_mul] at px
  have scaleZero : t=0 := (mul_eq_zero.mp px).resolve_right vp
  rw [scaleZero,zero_smul,add_zero] at ev
  exact ev ▸ hu

/-- The actual unmarked band before the optional degree-six refund. -/
theorem NativeMarkedEscapeChart.adjacent_unmarked_band
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {j : ℕ} (grade : j=7 ∨ j=8)
    (shifts : ∀ i≤j-6, ((diag (nodes A))^i) x∈zeroSpace A j) :
    ∀ i≤j-6, ((diag (nodes A))^i) x∈escapeHeadBand A U w (r+2+(j-(a+1))) := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  have marked := H.adjacent_marked_band ha ho grade
    (fun i hi => Submodule.mem_sup_left (shifts i hi))
  intro i hi
  exact escapeHeadBand_strip_terminal ho H.head.paidRanks.lastActive H.seed
    (h:=7+(j-(a+1))) (by omega) (by omega)
    (escapeHeadBand_paid_from_seven H.head _) (shifts i hi) (marked i hi)

/-- Both early forks pay the same actual head length for a run of one
or two shifts. The a=5 spill is paid by the nonzero refund probe. -/
theorem NativeMarkedEscapeChart.adjacent_unmarked_pure
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {j : ℕ} (grade : j=7 ∨ j=8)
    (shifts : ∀ i≤j-6, ((diag (nodes A))^i) x∈zeroSpace A j) :
    ∀ i≤j-6, ((diag (nodes A))^i) x∈escapeHeadBand A U w (r+j-5) := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  intro i hi
  have paid := H.adjacent_unmarked_band ha ho grade shifts i hi
  rcases aw with five | six
  · subst a
    have short := H.refund_one_head_slot ha ho (m:=j-6) (x:=((diag (nodes A))^i) x) (by omega)
      (by simpa only [show 6+(j-6)=j by omega] using shifts i hi)
      (by simpa only [show 5+1=6 by decide] using paid)
    rwa [show r+1+(j-6)=r+j-5 by omega] at short
  · rwa [six,show r+2+(j-(6+1))=r+j-5 by omega] at paid

/-- Single true-clock support in F7 or F8 is absorbed by the original
unmarked invariant core, even when that clock equals one. -/
theorem NativeMarkedEscapeChart.one_clock_local
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {j : ℕ} (grade : j=7 ∨ j=8) (hx : x∈zeroSpace A j)
    {t : K} (localAt : ∀ i, nodes A i≠t → x i=0) : x∈U := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  have shifts (k : ℕ) : ((diag (nodes A))^k) x∈zeroSpace A j := by
    have eq : ((diag (nodes A))^k) x=t^k • x := by
      ext i
      by_cases h : nodes A i=t
      · simp [HeadFiber.clock_power_value,h,smul_eq_mul]
      · simp [HeadFiber.clock_power_value,localAt i h]
    rw [eq]
    exact (zeroSpace A j).smul_mem _ hx
  have cut := H.adjacent_unmarked_band ha ho grade (fun i _=>shifts i) 0 (by omega)
  simp only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] at cut
  exact HeadFiber.localized_mem H.head.head.coreStable
    (H.more_head_clocks ha ho (m:=j-(a+1)) (by omega)) cut localAt

end
end RKResearch.Certified.Graded.ERK13NativeFirst

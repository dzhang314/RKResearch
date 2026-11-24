module
public import RKCert.ERKOrderFifteenChart

@[expose] public section

/-! # Exact original-array terminal/alias distinction at grade eight -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d a r : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

theorem unmarked_grade_eight_rigid (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 15) (hs : s≠0)
    (P : K[X]) (pd : P.natDegree≤7) (hp : evalNodes A P∈zeroSpace A 8) : P=0 := by
  have h : evalNodes A P∈defectPlus A 0 8 := (show zeroSpace A 8≤defectPlus A 0 8 from le_sup_left) hp
  obtain ⟨t,e⟩:=meshOddFull7_decode P (by omega) (marked_eval_origin ha hs P h)
    (fun k=>marked_moment_zero ho P h (by omega) (by have := k.isLt; omega))
  by_contra pn
  have q := (mesh_line_degree e pn).trans odd7_degree
  omega

omit [CharZero K] in
theorem terminal_component_vanishes {y : Vec K (s+1)} {j : ℕ}
    (ht : y∈tailPlane K s d) (hE : y∈treeSpace A j)
    (h : d=0 ∨ terminal (K:=K) s∉treeSpace A j) : y=0 := by
  by_cases d0 : d=0
  · simpa [tailPlane,d0] using ht
  rw [tailPlane,ite_eq_right d0] at ht
  obtain ⟨u,rfl⟩:=Submodule.mem_span_singleton.mp ht
  have uz : u=0 := by
    by_contra nz
    exact (h.resolve_left d0) (((treeSpace A j).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nz)).mp hE)
  rw [uz,zero_smul]

theorem alias_forces_terminal_eight (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d)
    (C : OddSevenChart A d a r U w G) (aliased : a=6) :
    terminal (K:=K) s∈treeSpace A 8 ∧ terminal (K:=K) s∉treeSpace A 7 := by
  have d1 : d=1 := (C.chartType.resolve_left (by omega)).2
  have gd : G.natDegree=7 := by have := C.meshDegree; omega
  have be : terminal (K:=K) s∈tailPlane K s d := by
    rw [tailPlane,ite_eq_right (by omega : d≠0)]
    exact Submodule.mem_span_singleton_self _
  have early : terminal (K:=K) s∉treeSpace A 7 := by
    intro h
    have e := Submodule.mem_inf.mpr ⟨h,be⟩
    rw [M.noTail] at e
    exact terminal_ne ((Submodule.mem_bot K).mp e)
  refine ⟨?_,early⟩
  by_contra absent
  obtain ⟨z,hz,t,ht,e⟩:=Submodule.mem_sup.mp (firstEscape_defect C.meshPaid)
  have g8 : evalNodes A G∈treeSpace A 8 := evalNodes_mem_treeSpace A G (by omega)
  have t8 : t∈treeSpace A 8 := by
    have te : t=evalNodes A G-z := by rw [←e]; abel
    rw [te]
    exact (treeSpace A 8).sub_mem g8 (zeroSpace_le_treeSpace A _ hz)
  have tz := terminal_component_vanishes ht t8 (Or.inr absent)
  have z8 : evalNodes A G∈zeroSpace A 8 := by rw [←e,tz,add_zero]; exact hz
  have g0 := unmarked_grade_eight_rigid ha ho (by have := S.size; omega) G gd.le z8
  rw [g0,natDegree_zero] at gd
  omega

theorem no_early_terminal_unmarked_eight (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1)
    (C : OddSevenChart A d 7 r U w G)
    (absent : d=0 ∨ terminal (K:=K) s∉treeSpace A 8) :
    zeroSpace A 8=firstEscape A 0 7 := by
  have c : treePlus A d 8=polyBand A 7⊔firstEscape A d 7 := by
    rw [C.chart 8 (by decide) (by decide),C.marked.edge]
    rfl
  have sharp : firstEscape A 0 7≤zeroSpace A 8 := by
    intro v hv
    exact tail_zero_iff.mp (firstEscape_defect hv)
  apply le_antisymm _ sharp
  intro v hv
  have he : v∈treePlus A d 8 := (show treeSpace A 8≤treePlus A d 8 from le_sup_left) (zeroSpace_le_treeSpace A 8 hv)
  rw [c] at he
  obtain ⟨pv,hpv,z,hz,e⟩ := Submodule.mem_sup.mp he
  obtain ⟨x,hx⟩ := hpv
  let P : K[X] := ofFn 8 x
  have xd : P.natDegree≤7 :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) x)
  have xx : evalNodes A P=pv := (evalNodes_ofFn A 7 x).trans hx
  have x8 : pv∈treeSpace A 8 := xx ▸ evalNodes_mem_treeSpace A P (by omega)
  obtain ⟨z0,hz0,t,ht,ez⟩ := Submodule.mem_sup.mp hz
  have z8 : z0∈zeroSpace A 8 := sharp ((show zeroSpace A 7⊔(zeroSpace A 7).map (diag (nodes A))≤firstEscape A 0 7 from le_sup_left) hz0)
  have htEq : t=(v-pv)-z0 := by rw [←e,←ez]; abel
  have t8 : t∈treeSpace A 8 := by
    rw [htEq]
    exact (treeSpace A 8).sub_mem ((treeSpace A 8).sub_mem (zeroSpace_le_treeSpace A _ hv) x8)
      (zeroSpace_le_treeSpace A _ z8)
  have t0 := terminal_component_vanishes ht t8 absent
  have ze : z=z0 := by rw [←ez,t0,add_zero]
  rw [ze] at e
  have px : evalNodes A P∈zeroSpace A 8 := by
    have ep : pv=v-z0 := by rw [←e]; abel
    rw [xx,ep]
    exact (zeroSpace A _).sub_mem hv z8
  have p0 := unmarked_grade_eight_rigid ha ho (by have := S.size; omega) P xd px
  have v0 : pv=0 := by rw [←xx,p0]; ext i; simp [evalNodes]
  rw [←e,v0,zero_add]
  exact (show zeroSpace A 7⊔(zeroSpace A 7).map (diag (nodes A))≤firstEscape A 0 7 from le_sup_left) hz0

omit [CharZero K] in
/-- An actual terminal column by grade nine forces every grade-five physical
defect to vanish at the last stage, regardless of which marked branch led here. -/
theorem terminal_by_nine_zero_five (ho : HasTreeOrderAtLeast A b 15)
    (lastLive : b (Fin.last s)≠0) {j : ℕ} (hj : j≤9)
    (ht : terminal (K:=K) s∈treeSpace A j) :
    ∀ v∈zeroSpace A 5,v (Fin.last s)=0 := by
  intro v hv
  have hprod := zeroSpace_mul_treeSpace ho (m:=5) (n:=j) (by omega) hv ht
  have hp := probe_zeroSpace ho (k:=0) (by omega) hprod
  change probe A b 0 (v*terminal s)=0 at hp
  rw [mul_comm,terminal_mul,map_smul,smul_eq_mul] at hp
  have pe : probe A b 0 (terminal s)=b (Fin.last s) := by
    rw [show probe A b 0 (terminal s)=row b (terminal s) by simp [probe],row_terminal]
  rw [pe] at hp
  exact (mul_eq_zero.mp hp).resolve_right lastLive

end RKCert.Paired.FiniteMidpoint

module
public import RKCert.ERKOrder13MarkedCore

@[expose] public section
/-! # Genuine ordinary lifting before terminal coordinate entry
An augmented equality paid at grade j is a true ordinary defect exactly
when the terminal coordinate has not entered the actual tree space at
that grade and the column is an actual tree-space element. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Module Polynomial
variable {K:Type*} [Field K] {s p a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2700000

theorem unmark_before_tail {j:ℕ} (late:(terminal s:Vec K (s+1))∉treeSpace A j)
    {v:Vec K (s+1)} (h:v∈defectPlus A 1 j) (paid:v∈treeSpace A j) :
    v∈zeroSpace A j := by
  obtain ⟨x,hx,y,hy,e⟩:=Submodule.mem_sup.mp h
  rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)] at hy
  obtain ⟨q,rfl⟩:=Submodule.mem_span_singleton.mp hy
  have yF : q • (terminal s:Vec K (s+1))∈treeSpace A j := by
    have e' : q • (terminal s:Vec K (s+1))=v-x := by rw [←e];abel
    rw [e']
    exact (treeSpace A j).sub_mem paid (zeroSpace_le_treeSpace A j hx)
  have q0:q=0 := by
    by_contra ne
    exact late (((treeSpace A j).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr ne)).mp yF)
  rw [q0,zero_smul,add_zero] at e
  rwa [←e]

theorem actual_terminal_vanishes [CharZero K] (ho:HasTreeOrderAtLeast A b p)
    (hb:b (Fin.last s)≠0) {j k:ℕ} (hk:j+k+1≤p)
    (ht:(terminal s:Vec K (s+1))∈treeSpace A j) {v:Vec K (s+1)} (hv:v∈zeroSpace A k) :
    v (Fin.last s)=0 := by
  have paid:=zeroSpace_mul_treeSpace ho (by omega) hv ht
  have e : v*(terminal s:Vec K (s+1))=v (Fin.last s) • (terminal s:Vec K (s+1)) := by
    ext i
    by_cases z:i=Fin.last s
    · subst i
      simp
    · simp [terminal_at_ne z]
  have h:=probe_zeroSpace ho (k:=0) (by omega) paid
  change probe A b 0 (v*(terminal s:Vec K (s+1)))=0 at h
  have pr : probe A b 0 (terminal s)=row b (terminal s) := by simp [probe,row_apply]
  rw [e,map_smul,smul_eq_mul,pr,row_terminal] at h
  exact (mul_eq_zero.mp h).resolve_right hb

theorem ordinary_when_augmented_terminal_zero {j:ℕ}
    (van:∀v∈zeroSpace A j,v (Fin.last s)=0)
    {v:Vec K (s+1)} (hv:v∈defectPlus A 1 j) (last:v (Fin.last s)=0) :
    v∈zeroSpace A j := by
  obtain ⟨x,hx,y,hy,e⟩:=Submodule.mem_sup.mp hv
  rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)] at hy
  obtain ⟨q,rfl⟩:=Submodule.mem_span_singleton.mp hy
  have eq:=congrFun e (Fin.last s)
  simp [van x hx,last,terminal_at_last] at eq
  rw [eq,zero_smul,add_zero] at e
  rwa [←e]

theorem weighted_thirteen_ordinary [CharZero K] (ho:HasTreeOrderAtLeast A b 13)
    {j k:ℕ} {x:Vec K (s+1)} (hx:x∈zeroSpace A j)
    (P:K[X]) (pay:P.natDegree+1≤13) (bound:j+P.natDegree≤k) :
    weightedEval (nodes A) x P∈zeroSpace A k := by
  have e : weightedEval (nodes A) x P=x*evalNodes A P := by
    ext i
    simp [weightedEval_apply,evalNodes,mul_comm]
  rw [e]
  exact zeroSpace_mono A bound (zeroSpace_mul_treeSpace ho pay hx (evalNodes_mem_treeSpace A P le_rfl))

theorem late13_mesh [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (C:Chart13 A 1 a r U w G)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7) :
    a=6∧∃ t:K,t≠0∧G=t•odd6 := by
  have gd : G.natDegree≤7 := by have:=C.width;rw [C.meshDegree];omega
  have aug : evalNodes A G∈defectPlus A 1 7 := firstEscape_defect C.meshPaid
  have hx := unmark_before_tail late aug (evalNodes_mem_treeSpace A G gd)
  have h0 := marked_eval_origin ha (by have:=S.size;omega) G aug
  obtain ⟨t,eq⟩:=mesh13Full_decode G gd h0 (fun k=>marked_moment_zero ho G
    (tail_zero_iff.mpr hx) gd (by have:=k.isLt;omega))
  have gn:G≠0 := by intro h;have E:=C.meshDegree;rw [h,natDegree_zero] at E;omega
  have deg := mesh_line_degree eq gn
  rw [C.meshDegree,odd6_degree] at deg
  exact ⟨by omega,t,fun hz=>gn (by rw [eq,hz,zero_smul]),eq⟩

theorem late13_exact_marked_F7 [LinearOrder K] [IsStrictOrderedRing K]
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (C:Chart13 A 1 6 r U w G)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7) :
    defectPlus A 1 7=Band13 A 6 r U w 7 := by
  classical
  have hb : Band13 A 6 r U w 7≤defectPlus A 1 7 := band13_paid C (by decide)
  apply le_antisymm _ hb
  intro u hu
  have hTree : u∈treePlus A 1 7 := (sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl) hu
  rw [C.chart 7 (by decide) (by decide)] at hTree
  obtain ⟨v,⟨a,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp hTree
  let P:=ofFn 7 a
  have hd:P.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have ev:evalNodes A P=polyEval A 6 a := evalNodes_ofFn A 6 a
  have hP : evalNodes A P∈defectPlus A 1 7 := by
    rw [ev,show polyEval A 6 a=u-z by rw [←eq];abel]
    exact (defectPlus A 1 7).sub_mem hu (hb hz)
  have h0 := unmark_before_tail late hP (evalNodes_mem_treeSpace A P (by omega))
  have hzP:=RKCert.OrderedGram.ordered_anchored_separation ha ho P (by omega) (by omega) h0
  have zz : (0:Vec K (s+1))=polyEval A 6 a := by
    rw [←ev,hzP]
    ext i
    simp only [Pi.zero_apply,evalNodes_apply,eval_zero]
  rwa [←eq,←zz,zero_add]

end RKCert.Paired.FiniteMidpoint

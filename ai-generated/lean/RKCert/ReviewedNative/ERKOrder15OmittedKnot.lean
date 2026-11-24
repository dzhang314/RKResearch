module

public import RKCert.ReviewedNative.ERKOrder15TerminalDivisor

@[expose] public section

/-! # The omitted physical knot supplies the exact two final primitives -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G P : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

/-- In the rank-two chart, grade six pays precisely the window needed by
the final omitted-knot primitive tests. -/
theorem Order15TerminalDivisor.paid_knot (B : Order15TerminalDivisor A b a U w G P)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (Q : K[X]) (qn : Q≠0) (qd : Q.natDegree≤2) :
    ∃ k : Fin (s+1), ¬LiveCore.live U k ∧ w k=0 ∧ G.eval (nodes A k)=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R : K[X], R.natDegree+Q.natDegree≤2 →
        (formalPrimitive (R*(Q*P))).eval (nodes A k)=0 := by
  let S := B.chart
  have ab := S.base_degree
  have closed (u : Fin (s+1)→K) (hu : u∈U) (v : Fin (s+1)→K) (hv : v∈U) :
      u*v∈U := S.core_times_five ha ho (S.earlyCore hv) hu
  have core : U≤markedDefectSpace A b 6 :=
    S.earlyCore.trans (sup_le_sup (zeroSpace_mono A (by decide)) le_rfl)
  have f6 : markedDefectSpace A b 6=chain (diag (nodes A)) U w 3 := S.early 1 (by decide)
  have f7 : markedDefectSpace A b 7=chain (diag (nodes A)) U w 4 := S.early 2 (by decide)
  have paid (F : K[X]) (deg : F.natDegree≤2) :
      weightedEval (nodes A) w F∈markedDefectSpace A b 6 := by
    apply weighted_eval_mem_of_powers (m:=2) ?_ F deg
    intro k hk
    rw [f6]
    exact ((clock_chain_le_iff _).mp le_rfl).2 k (by omega)
  have sep : ∀ F : K[X], F.natDegree≤6 → evalNodes A F∈markedDefectSpace A b 6 → F=0 :=
    eval_eq_zero_of_coeff_separated (marked_coeff_separated ha ho S.frame.lastActive
      (by have := S.frame.size;omega) (q:=6) (j:=6) (by decide) (by decide))
  have de := B.degree
  apply physical_head_knot (j:=6) (n:=4) (N:=5) ha S.stable closed B.disjoint B.repr B.nonzero
    (by omega) core paid sep ?_ ?_ (S.escape ▸ S.first.paid) Q qn qd
  · rw [←f7]
    exact marked_defect_mat ha 6
  · rw [←f7]
    exact le_sup_left

/-- A head vanishing at the origin would give the same two physical
3+2 primitive windows for a cubic. The common cubic rule excludes it. -/
theorem Order15TerminalDivisor.origin_nonzero (B : Order15TerminalDivisor A b a U w G P)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b) : P.eval 0≠0 := by
  intro p0
  have z0 : P.coeff 0=0 := by rwa [coeff_zero_eq_eval_zero]
  obtain ⟨R,e⟩ := Polynomial.X_dvd_iff.mpr z0
  have rn : R≠0 := fun z=>B.nonzero (by rw [e,z,mul_zero])
  have rd : R.natDegree≤3 := by
    have d := B.degree
    have a7 := B.chart.base_degree
    rw [e,natDegree_X_mul rn] at d
    omega
  obtain ⟨i,_,_,_,hn,first⟩ := B.paid_knot ha ho 1 one_ne_zero (by simp)
  let u := nodes A i
  have fn : u*R.eval u≠0 := by simpa [e,u] using hn
  have un : u≠0 := fun z=>fn (by rw [z,zero_mul])
  let Q : K[X] := X-C u
  have qd : Q.natDegree=1 := natDegree_X_sub_C u
  obtain ⟨j,_,_,_,hm,second⟩ := B.paid_knot ha ho Q (X_sub_C_ne_zero u) (by omega)
  let v := nodes A j
  have eq : Q*P=X*(X-C u)*R := by rw [e]; dsimp only [Q];ring
  have sn : v*(v-u)*R.eval v≠0 := by simpa [eq,v] using hm
  have vn : v≠0 := fun z=>sn (by rw [z,zero_mul,zero_mul])
  have ve : v≠u := fun z=>sn (by rw [z,sub_self,mul_zero,zero_mul])
  apply rn (RKCert.EndpointPhysical.cubic_eq_zero_of_primitives rd un vn ve ?_)
  constructor
  · intro T td
    simpa [e,u] using first T (by simpa using td)
  · intro T td
    simpa only [eq,v] using second T (by omega)

/-- These are the actual clock, omitted-support condition, and two
native primitive values needed by the frozen scalar exclusions. -/
theorem Order15TerminalDivisor.omitted_knot (B : Order15TerminalDivisor A b a U w G P)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b) :
    ∃ k : Fin (s+1), ¬LiveCore.live U k ∧ w k=0 ∧ nodes A k≠0 ∧ G.eval (nodes A k)=0 ∧
      P.eval (nodes A k)≠0 ∧ (formalPrimitive (X*P)).eval (nodes A k)=0 ∧
      (formalPrimitive (X*(X*P))).eval (nodes A k)=0 := by
  obtain ⟨k,no,w0,g0,h,test⟩ := B.paid_knot ha ho X X_ne_zero (by simp)
  have z : nodes A k*P.eval (nodes A k)≠0 := by simpa using h
  exact ⟨k,no,w0,fun e=>z (by rw [e,zero_mul]),g0,fun e=>z (by rw [e,mul_zero]),
    by simpa only [one_mul] using test 1 (by simp),test X (by simp)⟩

end
end RKResearch.Certified.Graded

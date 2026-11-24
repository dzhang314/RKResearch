module

public import RKCert.ReviewedNative.ERKOrder15TerminalEight

@[expose] public section

/-! # Actual terminal mass on the first three head-square readings -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial Module RKCert.Endpoint RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

private theorem mul_terminal (x : Fin (s+1)→K) :
    x*coordinate (Fin.last s)=x (Fin.last s) • coordinate (Fin.last s) := by
  ext i
  by_cases h : i=Fin.last s
  · subst i; simp [coordinate]
  · simp [coordinate,h]

private theorem probe_terminal :
    probe A b 0 (coordinate (K:=K) (Fin.last s))=b (Fin.last s) := by
  change row (fun i => b i*(nodes A i)^0) (coordinate (Fin.last s))=b (Fin.last s)
  rw [row_coordinate,pow_zero,mul_one]

/-- Actual presence of the terminal column in E8 removes the last
coordinate of every ordinary defect through grade six. -/
theorem terminal_eight_zeros_defects (ho : HasOrder 15 A b) (L : LastActive b (Fin.last s))
    (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    {j : ℕ} (pay : j+9≤15) {x : Fin (s+1)→K} (hx : x∈zeroSpace A j) : x (Fin.last s)=0 := by
  have h := probe_zeroSpace (k:=0) ho (by omega)
    (zeroSpace_mul_treeSpace ho (n:=8) (by decide) hx term)
  change probe A b 0 (x*coordinate (Fin.last s))=0 at h
  rw [mul_terminal,map_smul,probe_terminal,smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right L.live

theorem marked_five_parts (ho : HasOrder 15 A b) (L : LastActive b (Fin.last s))
    (seed : firstSeed A b=0) (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    {x : Fin (s+1)→K} (hx : x∈markedDefectSpace A b 5) :
    ∃ y∈zeroSpace A 5,x=y+x (Fin.last s) • coordinate (Fin.last s) := by
  obtain ⟨y,hy,t,ht,e⟩ := Submodule.mem_sup.mp hx
  rw [terminalMark,ite_eq_left seed] at ht
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp ht
  have last := congrFun e (Fin.last s)
  have ye := terminal_eight_zeros_defects ho L term (by decide : 5+9≤15) hy
  have cs : c=x (Fin.last s) := by
    simpa [coordinate,ye] using last
  exact ⟨y,hy,cs ▸ e.symm⟩

theorem marked_five_terminal_probe (ho : HasOrder 15 A b) (L : LastActive b (Fin.last s))
    (seed : firstSeed A b=0) (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    {x : Fin (s+1)→K} (hx : x∈markedDefectSpace A b 5) :
    probe A b 0 x=b (Fin.last s)*x (Fin.last s) := by
  obtain ⟨y,hy,e⟩ := marked_five_parts ho L seed term hx
  conv_lhs => rw [e]
  rw [map_add,probe_zeroSpace ho (by decide) hy,zero_add,map_smul,probe_terminal,smul_eq_mul,mul_comm]

/-- The clean rank-two head and its first power lie in the ordinary F5,
not only in the marked band. -/
theorem Order15PaidStaircase.terminal_head_first_powers (S : Order15PaidStaircase A b a G 2 U w)
    (ho : HasOrder 15 A b) (seed : firstSeed A b=0)
    (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    (dis : ∀ i, LiveCore.live U i → w i=0) :
    w (Fin.last s)=0 ∧ ∀ k≤1,(diag (nodes A)^k) w∈zeroSpace A 5 := by
  have last : LiveCore.live U (Fin.last s) := by
    refine ⟨coordinate (Fin.last s),S.early_two_head_payment.2.2 ?_,?_⟩
    · rw [terminalMark,ite_eq_left seed]
      exact Submodule.mem_span_singleton_self _
    · simp [coordinate]
  have w0 := dis _ last
  have f5 : markedDefectSpace A b 5=chain (diag (nodes A)) U w 2 := S.early 0 (by decide)
  refine ⟨w0,fun k hk => ?_⟩
  have m : (diag (nodes A)^k) w∈markedDefectSpace A b 5 := by
    rw [f5]
    exact ((clock_chain_le_iff _).mp le_rfl).2 k (by omega)
  obtain ⟨y,hy,e⟩ := marked_five_parts ho S.frame.lastActive seed term m
  rw [HeadFiber.clock_power_value,w0,mul_zero,zero_smul,add_zero] at e
  exact e.symm ▸ hy

/-- Both actual grade-five powers pay exactly the first three ordinary
grade-ten square shifts, with zero terminal coordinate. -/
theorem square_shifts_of_ordinary_head
    (w0 : w (Fin.last s)=0) (wp : ∀ k≤1,(diag (nodes A)^k) w∈zeroSpace A 5) :
    ∀ k≤2, (diag (nodes A)^k) (w*w)∈zeroSpace A 10 ∧
      ((diag (nodes A)^k) (w*w)) (Fin.last s)=0 := by
  intro k hk
  let D := diag (nodes A)
  let i := min k 1
  let j := k-i
  have le : i≤k := min_le_left _ _
  have il : i≤1 := min_le_right _ _
  have jl : j≤1 := by dsimp [j,i];omega
  have ij : i+j=k := by dsimp [j];omega
  have eq : (D^k) (w*w)=((D^i) w)*((D^j) w) := by
    ext l
    simp only [D,HeadFiber.clock_power_value,Pi.mul_apply]
    rw [←ij,pow_add]
    ring
  constructor
  · rw [eq]
    exact zeroSpace_mul (wp i il) (wp j jl)
  · simp only [HeadFiber.clock_power_value,Pi.mul_apply,w0,mul_zero]

/-- The native grade-ten head band has a genuine terminal mass. -/
theorem Order15PaidStaircase.ten_head_band_terminal_probe (S : Order15PaidStaircase A b a G 2 U w)
    (ho : HasOrder 15 A b) (seed : firstSeed A b=0)
    (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    (w0 : w (Fin.last s)=0) (w5 : w∈zeroSpace A 5)
    {v : Fin (s+1)→K} (hv : v∈order15HeadBand A a 2 10 U w) :
    probe A b 0 v=b (Fin.last s)*v (Fin.last s) := by
  obtain ⟨x,hx,Q,qd,rfl⟩ := HeadFiber.exists_poly hv
  have qb : Q.natDegree≤7 := by
    by_cases z : Q=0
    · simp [z]
    · have q := (natDegree_lt_iff_degree_lt z).mpr qd
      have ab := S.base_degree
      unfold order15HeadLength at q
      omega
  have qpay : weightedEval (nodes A) w Q∈zeroSpace A 12 := by
    have eq : weightedEval (nodes A) w Q=w*evalNodes A Q := by ext i; simp [mul_comm]
    rw [eq]
    exact zeroSpace_mul_treeSpace ho (n:=7) (by decide) w5 (evalNodes_mem_treeSpace A Q qb)
  rw [map_add,probe_zeroSpace ho (by decide) qpay,add_zero,Pi.add_apply,weightedEval_apply,w0,mul_zero,add_zero]
  exact marked_five_terminal_probe ho S.frame.lastActive seed term (S.earlyCore hx)

/-- The ordinary square's ghost has the extra actual terminal value
equation in addition to its charged probe differences. -/
theorem Order15PaidStaircase.terminal_ghost_decompose (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (seed : firstSeed A b=0) (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    (w0 : w (Fin.last s)=0) (w5 : w∈zeroSpace A 5)
    {v : Fin (s+1)→K} (hv : v∈zeroSpace A 10) (vl : v (Fin.last s)=0) :
    ∃ P : K[X], P.natDegree≤a ∧ P.coeff 0=0 ∧
      v-evalNodes A P∈order15HeadBand A a 2 10 U w ∧
      (∀ k≤a-4,chargedProbe A b k (evalNodes A P)=0) ∧
      (formalPrimitive P).eval 1=b (Fin.last s)*P.eval 1 := by
  obtain ⟨P,pd,p0,corr,paid⟩ := S.ten_poly_decompose ha ho (Submodule.mem_sup_left hv)
  refine ⟨P,pd,p0,corr,fun k hk => paid k (by simp [terminalDebit,seed];omega),?_⟩
  have eq := S.ten_head_band_terminal_probe ho seed term w0 w5 corr
  have l1 := S.frame.lastActive.node_eq_one ha seed
  rw [Pi.sub_apply,vl,evalNodes_apply,l1,zero_sub] at eq
  have p := probe_zeroSpace (k:=0) ho (by decide) hv
  rw [map_sub,p,zero_sub,probe_evalNodes ho P 0 (by have :=S.base_degree;omega),
    pow_zero,one_mul,←formalPrimitive_eq_native,mul_neg,neg_inj] at eq
  exact eq

end
end RKResearch.Certified.Graded

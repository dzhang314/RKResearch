module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERKEvenHorizon
public import RKCert.ReviewedNative.ERK8PaidOneOffPrefixSelectors
public import RKCert.ReviewedNative.ReverseInvariantBudget

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Paid chart for activated Fin 10 one-off inputs;
no census, four-off case, or substitute order-nine hypothesis. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open RKResearch Module Reverse
open scoped Classical Matrix

section GenericPrefix
variable {K : Type*} [Field K] [EightUnits K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

omit [EightUnits K] in
theorem firstChartBefore_cast {a d : K} (hs : 4≤s) (q : Fin 4)
    (h : ∀ l : Fin 4, l < q → nodes A (Fin.castLE hs l)=chartNode a d l ∧
      g A (Fin.castLE hs l)=chartDefect a l) :
    FirstChartBefore A a d (Fin.castLE hs q) := by
  intro r rq
  have lt : r.val < q.val := rq
  let l : Fin 4 := ⟨r.val,lt.trans q.isLt⟩
  have eq : Fin.castLE hs l=r := Fin.ext rfl
  exact ⟨l,rfl,eq ▸ h l lt⟩

structure FirstFour (A : Matrix (Fin s) (Fin s) K) (a d : K) (hs : 4≤s) : Prop where
  features : ∀ l : Fin 4,
    nodes A (Fin.castLE hs l)=chartNode a d l ∧
    g A (Fin.castLE hs l)=chartDefect a l ∧
    h A (Fin.castLE hs l)=chartH a d l

theorem normHe_doubled (a d : K) (dn : d≠0) : normHe a d (2*d)=a*d^2 := by
  unfold normHe
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,dn]
  eight_ring K

theorem four_chart_features {a d : K} {l : Fin 4} (dn : d≠0) :
    NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d))
      (chartNode a d l) (chartDefect a l) (chartH a d l) := by
  rw [normHe_doubled a d dn]
  fin_cases l <;> simp [NormalFour,ThreeFeatures,chartNode,chartDefect,chartH]

omit [EightUnits K] in
theorem firstChartBefore_four {a d : K} {r : Fin s} (size : 4≤s)
    (r4 : r.val=4) (F : FirstFour A a d size) : FirstChartBefore A a d r := by
  intro u ur
  have lt : u.val < 4 := r4 ▸ ur
  let l : Fin 4 := ⟨u.val,lt⟩
  have eq : Fin.castLE size l=u := Fin.ext rfl
  have f := F.features l
  rw [eq] at f
  exact ⟨l,rfl,f.1,f.2.1⟩

/-- Evaluation by the physical stages strictly before `j) is independent
on `U`, in the full-coordinate annihilator formulation. -/
def IndependentBefore (U : Submodule K (Fin s → K)) (j : Fin s) : Prop :=
  ∀ r ∈ annih U, (∀ i, j ≤ i → r i=0) → r=0

end GenericPrefix

variable {K : Type*} [Field K] [EightUnits K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem no_duplicate (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    {i j : Fin 10} (ij : i < j) (eq : ∀ k, A i k = A j k) : False := by
  obtain ⟨B,c,hB,ord⟩ := exists_merge_equal_rows ha ho ij eq
  have bound := erk_even_midpoint_floor hB ord (q:=4) (by decide) (by decide)
  omega

theorem earnedNormal (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (mid : ERKEvenHorizon A b 4) (off : (offKnots A).card=1) :
    ∃ a d : K, ∃ i j : Fin 10, GlobalNormal A a d i j := by
  have cap : finrank K (treeSpace A 4) ≤ 8 := by
    have bound := mid.treeRank
    norm_num at bound
    omega
  obtain ⟨r3,r4,_,_⟩ := forward_minimal_ranks ha ho (by decide) cap
  have sep : PolySeparated A 4 :=
    PolySeparated.of_coeff (explicit_coeff_separated ha ho (q:=4) (by decide))
  obtain ⟨a,d,i,j,D⟩ :=
    constant_amplitude_of_single_off_of_capacity ha ho (by decide) off cap
  exact ⟨a,d,i,j,global_normal_from_amplitude ha sep r3 r4 D⟩

theorem gradeFiveCap (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 8 A b) :
    finrank K (treeSpace A 5) ≤ 9 := by
  have back := backward_count ha ho 5 1 (by decide)
  omega

/-- Only F3 is paid against the physical terminal coordinate in E4. -/
theorem terminalDefectZero (ho : HasOrder 8 A b) (mid : ERKEvenHorizon A b 4)
    {u : Fin 10 → K} (hu : u∈zeroSpace A 3) : u (Fin.last 9)=0 := by
  obtain ⟨t,all,live,clock,term⟩ := mid.terminal
  have eq : t=Fin.last 9 := le_antisymm (Fin.le_last t) (all _)
  subst t
  let j : Fin 10 := Fin.last 9
  let v : Fin 10 → K := coordinate j
  have hm : u*v ∈ zeroSpace A 7 :=
    zeroSpace_mul_treeSpace ho (by decide : 4+1≤8) hu term
  have paid : probe A b 0 (u*v)=0 := probe_zeroSpace ho (by decide) hm
  have e : u*v=(u j) • v := by
    ext l
    by_cases z : l=j
    · simp [v,coordinate,z]
    · simp [v,coordinate,z]
  have out : probe A b 0 v=b j := by
    change row _ (coordinate j)=_
    rw [row_coordinate,pow_zero,mul_one]
  rw [e,map_smul,smul_eq_mul,out] at paid
  exact (mul_eq_zero.mp paid).resolve_right live.live

theorem firstFour (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (hs : 4≤10) (sep : PolySeparated A 4) (rk3 : finrank K (zeroSpace A 3)=2)
    (rk4 : finrank K (zeroSpace A 4)=3)
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) :
    FirstFour A a d hs := by
  let e : Fin 4→Fin (10) := Fin.castLE hs
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have no_dup {x y : Fin (10)} (xy : x < y) (pr : FirstChartBefore A a d y)
      (cx : nodes A x=nodes A y) (gx : g A x=g A y) (hx : h A x=h A y) : False :=
    no_duplicate ha ho xy
      (prefix_equal_physical_rows ha an dn D.base.q2 xy pr cx gx hx)
  have mat0 (v : Fin (10) → K) : mat A v (e 0)=0 := by
    apply causal_mat ha
    intro k kh
    change k.val < 0 at kh
    omega
  have c0 : nodes A (e 0)=0 := by
    simpa [mat_apply,nodes] using mat0 (1:Fin (10) → K)
  have g0 : g A (e 0)=0 := by rw [g_apply,c0,mat0]; simp
  have h0 : h A (e 0)=0 := mat0 (g A)
  have pre1 : FirstChartBefore A a d (e 1) := by
    apply firstChartBefore_cast hs (1:Fin 4)
    intro l ll
    have eq : l=0 := Fin.ext (show l.val=0 by have : l.val < 1 := ll; omega)
    subst l
    simpa [e,chartNode,chartDefect] using And.intro c0 g0
  have i0 : i≠e 0 := by
    intro eq
    apply an
    calc a = nodes A i := D.base.origin.node.symm
         _ = 0 := by rw [eq,c0]
  have i1 : i=e 1 := by
    by_contra ne
    have gt : e 1 < i := by
      have nz : i.val≠0 := fun h=>i0 (Fin.ext h)
      have no : i.val≠1 := fun h=>ne (Fin.ext h)
      change 1 < i.val
      omega
    have c1 := D.base.origin.earlier_node (e 1) gt
    have g1 := D.base.origin.earlier_defect (e 1) gt
    have h1 : h A (e 1)=0 := by
      apply causal_mat ha
      intro k kk
      change k < e 1 at kk
      exact D.base.origin.earlier_defect k (kk.trans gt)
    exact no_dup (show e 0 < e 1 by change (0:ℕ) < 1; decide) pre1
      (c0.trans c1.symm) (g0.trans g1.symm) (h0.trans h1.symm)
  have c1 : nodes A (e 1)=a := i1 ▸ D.base.origin.node
  have g1 : g A (e 1)=baseAmp a := i1 ▸ D.base.origin.defect
  have h1 : h A (e 1)=0 := by
    apply causal_mat ha
    intro k kk
    change k < e 1 at kk
    exact D.base.origin.earlier_defect _ (i1.symm ▸ kk)
  have pre2 : FirstChartBefore A a d (e 2) := by
    apply firstChartBefore_cast hs (2:Fin 4)
    intro l ll
    have cases : l=0 ∨ l=1 := by
      have : l.val < 2 := ll
      rcases show l.val=0 ∨ l.val=1 by omega with eq|eq
      · exact Or.inl (Fin.ext eq)
      · exact Or.inr (Fin.ext eq)
    rcases cases with rfl|rfl
    · simpa [e,chartNode,chartDefect] using And.intro c0 g0
    · simpa [e,chartNode,chartDefect] using And.intro c1 g1
  have j2 : j=e 2 := by
    by_contra ne
    have j0 : j.val≠0 := fun eq=>D.base.first_h.nonzero (by rw [(Fin.ext eq : j=e 0),h0])
    have j1 : j.val≠1 := fun eq=>D.base.first_h.nonzero (by rw [(Fin.ext eq : j=e 1),h1])
    have j2 : j.val≠2 := fun eq=>ne (Fin.ext eq)
    have gt : e 2 < j := by change 2 < j.val; omega
    have hh := D.base.first_h.earlier (e 2) gt
    rcases D.base.first_h.prefix_features (e 2) gt with ⟨c,g⟩|⟨c,g⟩
    · exact no_dup (show e 0 < e 2 by change (0:ℕ) < 2; decide) pre2
        (c0.trans c.symm) (g0.trans g.symm) (h0.trans hh.symm)
    · exact no_dup (show e 1 < e 2 by change (1:ℕ) < 2; decide) pre2
        (c1.trans c.symm) (g1.trans g.symm) (h1.trans hh.symm)
  have c2 : nodes A (e 2)=d := j2 ▸ D.base.node
  have g2 : g A (e 2)=0 := j2 ▸ D.base.clean
  have h2 : h A (e 2)=twoHd a d := j2 ▸ D.base.hj
  have pre3 : FirstChartBefore A a d (e 3) := by
    apply firstChartBefore_cast hs (3:Fin 4)
    intro l ll
    fin_cases l
    · simpa [e,chartNode,chartDefect] using And.intro c0 g0
    · simpa [e,chartNode,chartDefect] using And.intro c1 g1
    · simpa [e,chartNode,chartDefect] using And.intro c2 g2
    · exact (lt_irrefl _ ll).elim
  obtain ⟨r,rg,rc,rh,hpre⟩ := first_doubled_clean_clock ha sep rk3 rk4 D
  have r3 : r=e 3 := by
    by_contra ne
    have Hr : h A r≠0 := by rw [rh]; exact mul_ne_zero an (pow_ne_zero 2 dn)
    have r0 : r.val≠0 := fun eq=>Hr (by rw [(Fin.ext eq : r=e 0),h0])
    have r1 : r.val≠1 := fun eq=>Hr (by rw [(Fin.ext eq : r=e 1),h1])
    have r2 : r.val≠2 := by
      intro eq
      have h : nodes A r=d := by rw [(Fin.ext eq : r=e 2),c2]
      apply dn
      linear_combination (norm := eight_ring K) h-rc
    have r3 : r.val≠3 := fun eq=>ne (Fin.ext eq)
    have gt : e 3 < r := by change 3 < r.val; omega
    rcases hpre (e 3) gt with ⟨c,g,h⟩|⟨c,g,h⟩|⟨c,g,h⟩
    · exact no_dup (show e 0 < e 3 by change (0:ℕ) < 3; decide) pre3
        (c0.trans c.symm) (g0.trans g.symm) (h0.trans h.symm)
    · exact no_dup (show e 1 < e 3 by change (1:ℕ) < 3; decide) pre3
        (c1.trans c.symm) (g1.trans g.symm) (h1.trans h.symm)
    · exact no_dup (show e 2 < e 3 by change (2:ℕ) < 3; decide) pre3
        (c2.trans c.symm) (g2.trans g.symm) (h2.trans h.symm)
  subst r
  constructor
  intro l
  fin_cases l
  · simpa [e,chartNode,chartDefect,chartH] using And.intro c0 (And.intro g0 h0)
  · simpa [e,chartNode,chartDefect,chartH] using And.intro c1 (And.intro g1 h1)
  · simpa [e,chartNode,chartDefect,chartH] using And.intro c2 (And.intro g2 h2)
  · simpa [e,chartNode,chartDefect,chartH] using And.intro rc (And.intro rg rh)

/-- gh is the earned low-top kernel step in PROOF.md, not an extra
endpoint hypothesis. This helper only consumes the intermediate. -/
theorem fifthFeature (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (sep : PolySeparated A 4) (h3 : finrank K (zeroSpace A 3)=2)
    (h4 : finrank K (zeroSpace A 4)=3) (gh : g A*h A=0)
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) :
    nodes A (4:Fin 10)=2*d ∧ g A (4:Fin 10)=0 ∧ h A (4:Fin 10)≠a*d^2 := by
  let e : Fin 4→Fin 10 := Fin.castLE (by decide)
  let r : Fin 10 := 4
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C : FirstChartBefore A a d r := firstChartBefore_four (by decide) rfl F
  have no_dup : ∀ l : Fin 4,
      nodes A (e l)=nodes A r → g A (e l)=g A r → h A (e l)=h A r → False := by
    intro l cn cg ch
    have lt : e l < r := l.isLt
    exact no_duplicate ha ho lt
      (prefix_equal_physical_rows ha an dn D.base.q2 lt C cn cg ch)
  have p : ∀ l, l < r → NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d))
      (nodes A l) (g A l) (h A l) := by
    intro l lr
    obtain ⟨u,eq,cu,gu⟩ := C l lr
    have eu : e u=l := Fin.ext eq
    have fu := F.features u
    change nodes A (e u)=_ ∧ g A (e u)=_ ∧ h A (e u)=_ at fu
    rw [eu] at fu
    rw [cu,gu,fu.2.2]
    exact four_chart_features dn
  obtain ⟨x,cal⟩ := normal_clock_calibration ha sep h3 h4 D.base
  have xx := normal_clock_doubles ha sep D.base cal
  subst x
  obtain ⟨ra,rq⟩ := four_feature_residuals ha D.base cal r p
  have f0 : nodes A (e 0)=0 ∧ g A (e 0)=0 ∧ h A (e 0)=0 := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 0
  have f1 : nodes A (e 1)=a ∧ g A (e 1)=baseAmp a ∧ h A (e 1)=0 := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 1
  have f2 : nodes A (e 2)=d ∧ g A (e 2)=0 ∧ h A (e 2)=twoHd a d := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 2
  have f3 : nodes A (e 3)=2*d ∧ g A (e 3)=0 ∧ h A (e 3)=a*d^2 := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 3
  have gr : g A r=0 := by
    by_contra off
    have Prod := congrFun gh r
    change g A r*h A r=0 at Prod
    have hr := (mul_eq_zero.mp Prod).resolve_left off
    exact no_dup 1 (f1.1.trans (D.base.origin.off_support r off).symm)
      (f1.2.1.trans (amplitude_value D.base.amplitude off).symm)
      (f1.2.2.trans hr.symm)
  rw [gr] at ra rq
  rcases normal_clean_clocks a d (2*d) _ _ an dn cal.dNorm ra rq with c0|c2|c3
  · rw [c0] at ra rq
    exact (no_dup 0 (f0.1.trans c0.symm) (f0.2.1.trans gr.symm)
      (f0.2.2.trans (normal_clean_at_zero _ _ _ _ dn cal.en ra rq).symm)).elim
  · rw [c2] at ra rq
    exact (no_dup 2 (f2.1.trans c2.symm) (f2.2.1.trans gr.symm)
      (f2.2.2.trans (normal_clean_at_d _ _ _ _ dn cal.dNorm ra rq).symm)).elim
  · exact ⟨c3,gr,fun same=>no_dup 3 (f3.1.trans c3.symm) (f3.2.1.trans gr.symm)
      (f3.2.2.trans same.symm)⟩

/-- Same-clock causal contrast at the actual p8 capacity n=1, not a
borrowed p9 n=2 rank. The rank-five equality is earned in PROOF.md. -/
theorem noCausalClockContrast (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rank : finrank K (treeSpace A 5)=9) {w : Fin 10 → K} {j : Fin 10}
    (pre : IndependentBefore (treeSpace A 4) j)
    (wa : w∈annih (treeSpace A 5)) (wn : w≠0)
    (supportEnd : ∀ i, j < i → w i=0)
    (on : ∀ i, w i≠0 → nodes A i=nodes A j) : False := by
  have wt : mat A.transpose w ∈ annih (treeSpace A 4) :=
    annih_map_transpose (mat_treeSpace A 4) (Submodule.mem_map_of_mem wa)
  have a0 : mat A.transpose w=0 := pre _ wt (fun _ hi => transpose_tail_zero ha supportEnd hi)
  have d : diag (reflectedClock A) w=(1-nodes A j) • w := by
    ext i
    by_cases e : w i=0
    · simp [e]
    · simp [reflectedClock,on i e]
  let U : Submodule K (Fin 10 → K) := Submodule.span K {w}
  have aw : U≤annih (treeSpace A 5) := (Submodule.span_singleton_le_iff_mem ..).mpr wa
  have hij : 10 ≤ finrank K (treeSpace A 5)+1 := by omega
  have eq := no_joint_invariant_of_paid_capacity ha ho (j:=5) (n:=1) (by decide)
    hij U aw
    (fun v hv => by
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,a0,smul_zero]
      exact U.zero_mem)
    (fun v hv => by
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,d]
      exact U.smul_mem _ (U.smul_mem _ (Submodule.mem_span_singleton_self _)))
  have wm : w∈U := Submodule.mem_span_singleton_self _
  rw [eq,Submodule.mem_bot] at wm
  exact wn wm

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight

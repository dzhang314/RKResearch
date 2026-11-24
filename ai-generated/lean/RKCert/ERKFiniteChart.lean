module
public import RKCert.ERKFiniteMesh
public import RKCert.OrderTwelveLeakage

@[expose] public section

/-! # First actual band, all later ranks, and the effective site census -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s q ε d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

def headLen (q a r j : ℕ) := r+(q-4)+(j-(a+1))

noncomputable def forwardBand (A:Fin (s+1)→Fin (s+1)→K) (q a r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (j:ℕ) :=
  chain (diag (nodes A)) U w (headLen q a r j)

structure Chart (A:Fin (s+1)→Fin (s+1)→K) (q ε d a r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (G:K[X]) : Prop where
  marked : MarkedHead A q d r U w
  chartType : a=q ∨ a+1=q ∧ d=1
  mesh : Mesh G q ε d
  meshDegree : G.natDegree=a+1
  meshPaid : evalNodes A G∈firstEscape A d q
  chart : ∀j,a+1≤j→j≤2*q+ε-3→
    treePlus A d j=polyBand A a⊔forwardBand A q a r U w j
  rich : ∀j,a+1≤j→j≤2*q+ε-3→finrank K (treePlus A d j)=q+j+1+d

omit [CharZero K] in
theorem Chart.aLe {G:K[X]} (C:Chart A q ε d a r U w G) : a≤q := by
  rcases C.chartType with h|h <;> omega

omit [CharZero K] in
theorem Chart.aLo {G:K[X]} (C:Chart A q ε d a r U w G) : q≤a+1 := by
  rcases C.chartType with h|h <;> omega

theorem actual_chart (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d) :
    ∃ a r U w G,Chart A q ε d a r U w G := by
  classical
  obtain ⟨r,U,w,H⟩:=marked_head ha ho (by omega) he S M
  have finalize (a:ℕ) (ht:a=q∨a+1=q∧d=1) (G:K[X]) (gd:G.natDegree=a+1)
      (gp:evalNodes A G∈firstEscape A d q)
      (eq:treePlus A d (a+1)=polyBand A a⊔firstEscape A d q)
      (rr:finrank K (treePlus A d (a+1))=q+(a+1)+1+d)
      (rp:finrank K (treePlus A d ((a+1)-1))=
        if a+1=q then 2*q-1+d else q+(a+1)+d) :
      Chart A q ε d a r U w G := by
    have aLe : a≤q := by rcases ht with h|h <;> omega
    have aLo : q≤a+1 := by rcases ht with h|h <;> omega
    have stairs := band_staircase ha ho (by omega) M aLo
      (show 0<r+(q-4) by have := H.rTwo;omega) H.stable (by rwa [←H.edge]) rr rp
    have all (j:ℕ) (hj:a+1≤j) (hmax:j≤2*q+ε-3) :
        treePlus A d j=polyBand A a⊔forwardBand A q a r U w j ∧
        finrank K (treePlus A d j)=q+j+1+d := by
      have hx := stairs (j-(a+1)) (by omega)
      rw [show a+1+(j-(a+1))=j by omega] at hx
      exact ⟨hx.1,hx.2.1⟩
    exact ⟨H,ht,get_mesh ha ho hq he S M G (by omega) gp,gd,gp,
      fun j hj hm=>(all j hj hm).1,fun j hj hm=>(all j hj hm).2⟩
  by_cases h : ∀ P:K[X],P.natDegree≤q→evalNodes A P∈firstEscape A d q→P=0
  · obtain ⟨eq,rr,G,gd,gp⟩:=band_start_noalias ho (by omega) M H h
    refine ⟨q,r,U,w,G,finalize q (Or.inl rfl) G gd gp eq (by omega) ?_⟩
    rw [ite_eq_right (by omega),show q+1-1=q by omega,M.eMid];omega
  · push Not at h
    obtain ⟨G,gd,gp,gn⟩:=h
    obtain ⟨d1,gdeg⟩:=mesh_alias (get_mesh ha ho hq he S M G (by omega) gp) gd gn
    have low (P:K[X]) (hd:P.natDegree≤q-1) (hp:evalNodes A P∈firstEscape A d q) : P=0 := by
      by_contra hn
      have h := (mesh_alias (get_mesh ha ho hq he S M P (by omega) hp) (by omega) hn).2
      omega
    have eq1 : q-1+1=q := by omega
    have eq := band_start_alias ho (by omega) M he S H low G gdeg gp
    refine ⟨q-1,r,U,w,G,finalize (q-1) (Or.inr ⟨eq1,d1⟩) G (gdeg.trans eq1.symm)
      (gp) (by rwa [eq1]) (by rw [eq1,M.eMid];omega) ?_⟩
    rw [eq1,ite_eq_left rfl,M.ePrev]

omit [CharZero K] in
theorem chart_band_paid {G:K[X]} (C:Chart A q ε d a r U w G)
    {j:ℕ} (hj:a+1≤j) : forwardBand A q a r U w j≤defectPlus A d (j+(q-a)) := by
  have base : ∀k,chain (diag (nodes A)) U w (r+(q-4)+k)≤defectPlus A d (q+1+k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero,←C.marked.edge]
      exact firstEscape_defect
    | succ k ih =>
      rw [show r+(q-4)+(k+1)=r+(q-4)+k+1 by omega,←chain_sup_map (w:=w) C.marked.stable
        (by have := C.marked.rTwo;omega)]
      exact sup_le (ih.trans (Fplus_mono A d (by omega)))
        (((Submodule.map_mono ih).trans (Fplus_clock A d (q+1+k))).trans (Fplus_mono A d (by omega)))
  unfold forwardBand headLen
  exact (base (j-(a+1))).trans (Fplus_mono A d (by have := C.aLe;omega))

omit [CharZero K] in
theorem chart_band_sep {G:K[X]} (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) {j:ℕ} (hj:a+1≤j) (hmax:j≤2*q+ε-3)
    (P:K[X]) (hd:P.natDegree≤a) (hP:evalNodes A P∈forwardBand A q a r U w j) :
    P=0 := by
  classical
  have aLe := C.aLe
  have hEval : Function.Injective (polyEval A a) := (injective_iff_map_eq_zero _).mpr fun t ht=>by
    have h := evalNodes_ofFn A a t
    have hd : (ofFn (a+1) t).natDegree≤q := by have := ofFn_natDegree_lt (show 1≤a+1 by omega) t;omega
    have he : ofFn (a+1) t=0 :=
      separated_plus S M _ hd (by rw [h,ht];exact (defectPlus A d q).zero_mem)
    ext i
    have hz:=congrArg (fun P:K[X]=>P.coeff i.val) he
    rwa [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] at hz
  have pRank : finrank K (polyBand A a)=a+1 := by
    unfold polyBand
    rw [LinearMap.finrank_range_of_inj hEval]
    simp
  let B := forwardBand A q a r U w j
  have cap : finrank K B≤finrank K U+headLen q a r j :=
    RKCert.Paired.OrderTwelve.chain_rank_cap _
  have hr := Submodule.finrank_sup_add_finrank_inf_eq (polyBand A a) B
  have he := C.chart j hj hmax
  change treePlus A d j=polyBand A a⊔B at he
  rw [←he,C.rich j hj hmax,pRank] at hr
  have zero : finrank K ↥(polyBand A a⊓B)=0 := by
    have hq : 8≤q := by cases C.mesh <;> decide
    have := C.marked.rank
    unfold headLen at cap
    omega
  have hbot := Submodule.finrank_eq_zero.mp zero
  have h := Submodule.mem_inf.mpr ⟨eval_polyBand (A:=A) hd,hP⟩
  have vh : evalNodes A P=0 := (Submodule.mem_bot K).mp (hbot ▸ h)
  apply separated_plus S M P (by omega)
  rw [vh]
  exact (defectPlus A d q).zero_mem

omit [CharZero K] in
theorem chart_sites {G:K[X]} (hq:8≤q) (C:Chart A q ε d a r U w G) :
    headLen q a r (2*q+ε-3)≤(headSites (nodes A) w).card := by
  let j := 2*q+ε-4
  let n := headLen q a r j
  have aLe := C.aLe
  have i1 : a+1≤j := by dsimp [j];omega
  have i2 : j≤2*q+ε-3 := by dsimp [j];omega
  have i3 : j+1=2*q+ε-3 := by dsimp [j];omega
  have eOld := C.chart j i1 i2
  have eNew := C.chart (j+1) (by omega) (by omega)
  have hr1 := C.rich j i1 i2
  have hr2 := C.rich (j+1) (by omega) (by omega)
  have len : headLen q a r (j+1)=n+1 := by unfold n headLen;omega
  let D := diag (nodes A)
  have base : chain D U w n≤treePlus A d j := le_sup_right.trans (le_of_eq eOld.symm)
  have old := (chain_le_iff n).mp base
  have hnot : (D^n) w∉treePlus A d j := by
    intro hp
    have hc : forwardBand A q a r U w (j+1)≤treePlus A d j := by
      unfold forwardBand
      rw [len]
      exact (chain_le_iff _).mpr ⟨old.1, fun k hk => by
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with e|e
        · exact e ▸ hp
        · exact old.2 _ e⟩
    have hh : treePlus A d (j+1)≤treePlus A d j := by
      rw [eNew]
      exact sup_le (le_sup_left.trans (le_of_eq eOld.symm)) hc
    have rr := Submodule.finrank_mono hh
    omega
  have cnt := more_sites_than_paid old.2 hnot
  rw [←i3,len]
  omega

end RKCert.Paired.FiniteMidpoint


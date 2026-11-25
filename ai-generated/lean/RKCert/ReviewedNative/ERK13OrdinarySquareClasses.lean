module

public import RKCert.ReviewedNative.NativeCoordinateClassAlgebra
public import RKCert.ReviewedNative.NativeLiveCore
public import RKCert.ReviewedNative.ERK13OrdinarySquareTransport
public import RKCert.ReviewedNative.NativeQuadraticClassSelector
public import RKCert.ReviewedNative.HyperplanePhysicalLabels
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual coordinate classes of the ordinary order-13 square chart

The paid clock-stable E10 is its full unital coordinate algebra. The
core's class masks remain literal paid F4 columns. The only stage
compression is the existing checked physical-label hyperplane cut.
-/
namespace RKResearch.Certified.Graded.ERK13OrdinarySquare

open RKResearch Polynomial Module Reverse PhysicalCensus RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {U : Submodule K (Fin s→K)}
variable {w : Fin s→K}
set_option maxHeartbeats 1600000
set_option maxRecDepth 2200

def coreTrace (U : Submodule K (Fin s→K)) (i : Fin s) : U→K :=
  fun u => u.val i

def coreLabels (U : Submodule K (Fin s→K)) : Finset (U→K) :=
  (Finset.univ.filter (LiveCore.live U)).image (coreTrace U)

theorem mem_coreLabels {t : U→K} :
    t∈coreLabels U ↔ ∃ i, LiveCore.live U i ∧ coreTrace U i=t := by
  simp only [coreLabels,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

def headPair (A : Matrix (Fin s) (Fin s) K) (w : Fin s→K) (i : Fin s) : K×K :=
  (nodes A i,w i)

def phaseLabel (A : Matrix (Fin s) (Fin s) K)
    (U : Submodule K (Fin s→K)) (w : Fin s→K) (i : Fin s) :
    (U→K) ⊕ (K×K) :=
  if LiveCore.live U i then Sum.inl (coreTrace U i) else Sum.inr (headPair A w i)

def noncorePairs (A : Matrix (Fin s) (Fin s) K)
    (U : Submodule K (Fin s→K)) (w : Fin s→K) : Finset (K×K) :=
  (Finset.univ.filter (fun i => ¬LiveCore.live U i)).image (headPair A w)

theorem mem_noncorePairs {a : K×K} :
    a∈noncorePairs A U w ↔ ∃ i, ¬LiveCore.live U i ∧ headPair A w i=a := by
  simp only [noncorePairs,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem stage_chart_repr {j n : ℕ}
    (chart : treeSpace A j=(coeffEval A 6).range⊔chain (diag (nodes A)) U w n)
    (pos : 0<n) {v : Fin s→K} (hv : v∈treeSpace A j) :
    ∃ H J : K[X], ∃ z∈U, H.natDegree≤6 ∧ J.natDegree<n ∧
      v=evalNodes A H+weightedEval (nodes A) w J+z := by
  rw [chart] at hv
  obtain ⟨_,⟨a,rfl⟩,x,hx,e⟩ := Submodule.mem_sup.mp hv
  let H := ofFn 7 a
  have d : H.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
  have form : evalNodes A H=coeffEval A 6 a := by
    rw [evalNodes_eq_coeffEval A H d]
    congr 1
    ext i
    exact ofFn_coeff_eq_val_of_lt _ i.isLt
  obtain ⟨z,hz,J,jd,split⟩ := HeadFiber.exists_poly hx
  have bj : J.natDegree<n := by
    by_cases j0 : J=0
    · simpa only [j0,natDegree_zero] using pos
    · exact (natDegree_lt_iff_degree_lt j0).mpr jd
  refine ⟨H,J,z,hz,d,bj,?_⟩
  rw [←e,←form,split]
  abel

private theorem eval_mul_mem {V : Submodule K (Fin s→K)}
    (stable : V.map (diag (nodes A))≤V) (H : K[X]) {x : Fin s→K} (hx : x∈V) :
    evalNodes A H*x∈V := by
  have eq : evalNodes A H*x=(fun i=>H.eval (nodes A i)*x i) := by
    funext i
    simp only [Pi.mul_apply,evalNodes_apply]
  rw [eq]
  exact clock_function_mem (fun y (hy : y∈V)=>stable (Submodule.mem_map_of_mem hy)) H.eval hx

private theorem label_phase_match {i j : Fin s} (eq : phaseLabel A U w i=phaseLabel A U w j) :
    (LiveCore.live U i ∧ LiveCore.live U j ∧ coreTrace U i=coreTrace U j) ∨
    (¬LiveCore.live U i ∧ ¬LiveCore.live U j ∧ headPair A w i=headPair A w j) := by
  by_cases hi : LiveCore.live U i <;> by_cases hj : LiveCore.live U j
  · exact Or.inl ⟨hi,hj,Sum.inl.inj (by simpa only [phaseLabel,if_pos hi,if_pos hj] using eq)⟩
  · simp [phaseLabel,hi,hj] at eq
  · simp [phaseLabel,hi,hj] at eq
  · exact Or.inr ⟨hi,hj,Sum.inr.inj (by simpa only [phaseLabel,if_neg hi,if_neg hj] using eq)⟩

private theorem label_image_split {e : Fin s→K} (mask : ∀i,e i=if LiveCore.live U i then 1 else 0) :
    Finset.univ.image (phaseLabel A U w)=
      (activeLabels (coreTrace U) e).disjSum (noncorePairs A U w) := by
  ext a
  cases a with
  | inl t =>
    rw [Finset.inl_mem_disjSum,mem_activeLabels]
    constructor
    · intro hz
      obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hz
      by_cases live : LiveCore.live U i
      · exact ⟨i,by simp [mask i,live],
          Sum.inl.inj (by simpa only [phaseLabel,if_pos live] using eq)⟩
      · simp [phaseLabel,live] at eq
    · rintro ⟨i,ni,eq⟩
      have live : LiveCore.live U i := by
        by_contra dead
        exact ni (by rw [mask,if_neg dead])
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,by rw [phaseLabel,if_pos live,eq]⟩
  | inr t =>
    rw [Finset.inr_mem_disjSum,mem_noncorePairs]
    constructor
    · intro hz
      obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hz
      by_cases live : LiveCore.live U i
      · simp [phaseLabel,live] at eq
      · exact ⟨i,live,Sum.inr.inj (by simpa only [phaseLabel,if_neg live] using eq)⟩
    · rintro ⟨i,dead,eq⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,by rw [phaseLabel,if_neg dead,eq]⟩

/-- Measured ordinary class geometry. Core indicators are paid vectors,
not signed representatives chosen by a clock quadrature. -/
structure SquareClassGeometry (A : Matrix (Fin s) (Fin s) K)
    (U : Submodule K (Fin s→K)) (w : Fin s→K) : Prop where
  ambientCount : (Finset.univ.image (phaseLabel A U w)).card=17
  coreCount : (coreLabels U).card=3
  noncoreCount : (noncorePairs A U w).card=14
  same : ∀v∈treeSpace A 10, ∀i j, phaseLabel A U w i=phaseLabel A U w j → v i=v j
  clock : ∀i j, phaseLabel A U w i=phaseLabel A U w j → nodes A i=nodes A j
  coreIndicator : ∀i, LiveCore.live U i →
    labelIndicator (phaseLabel A U w) (phaseLabel A U w i)∈U
  closed : ∀x∈treeSpace A 10, ∀y∈treeSpace A 10, x*y∈treeSpace A 10
  full : labelOrbit (phaseLabel A U w) (1:Fin s→K)=treeSpace A 10

/-- The actual measured chart closes as a unital algebra, and its
whole-class ranks split as the three actual core atoms and fourteen
distinct (clock, head amplitude) classes on the complement. -/
theorem square_geometry_of_clock_stability
    (cU : U.map (diag (nodes A))≤U) (uClosed : ∀ x∈U, ∀ y∈U, x*y∈U)
    (clean : ∀i,LiveCore.live U i → w i=0)
    (cE : (treeSpace A 10).map (diag (nodes A))≤treeSpace A 10)
    (chart : treeSpace A 10=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 7)
    (uRank : finrank K U=3) (eRank : finrank K (treeSpace A 10)=17)
    (squarePay : w*w∈treeSpace A 10) :
    SquareClassGeometry A U w := by
  let E := treeSpace A 10
  let lab := phaseLabel A U w
  have band : chain (diag (nodes A)) U w 7≤E := by change _≤treeSpace A 10; rw [chart]; exact le_sup_right
  have chainPay := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 7).mp le_rfl
  have uE : U≤E := chainPay.1.trans band
  have wE : w∈E := band (by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using chainPay.2 0 (by decide))
  have one : (1:Fin s→K)∈E := one_mem_treeSpace A 10
  have nodesE : nodes A∈E := by
    have h := cE (Submodule.mem_map_of_mem one)
    have eq : diag (nodes A) (1:Fin s→K)=nodes A := by ext i; simp
    rwa [eq] at h
  have no {u : Fin s→K} (hu : u∈U) (i : Fin s) : u i*w i=0 := by
    by_cases nz : u i=0
    · rw [nz,zero_mul]
    · rw [clean i ⟨u,hu,nz⟩,mul_zero]
  have wTimes (v : Fin s→K) (hv : v∈E) : w*v∈E := by
    obtain ⟨H,J,x,hx,_,_,eq⟩ := stage_chart_repr chart (by decide) hv
    have eq' : w*v=evalNodes A H*w+evalNodes A J*(w*w) := by
      rw [eq]
      ext i
      simp only [Pi.mul_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply]
      have wz : w i*x i=0 := by rw [mul_comm]; exact no hx i
      rw [mul_add,mul_add,wz,add_zero]
      ring
    rw [eq']
    exact E.add_mem (eval_mul_mem cE H wE) (eval_mul_mem cE J squarePay)
  have uTimes (u : Fin s→K) (hu : u∈U) (v : Fin s→K) (hv : v∈E) : u*v∈U := by
    obtain ⟨H,J,x,hx,_,_,eq⟩ := stage_chart_repr chart (by decide) hv
    have eq' : u*v=evalNodes A H*u+u*x := by
      rw [eq]
      ext i
      simp only [Pi.mul_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply]
      rw [mul_add,mul_add,show u i*(J.eval (nodes A i)*w i)=0 by
        rw [mul_left_comm,no hu i,mul_zero],add_zero]
      ring
    rw [eq']
    exact U.add_mem (eval_mul_mem cU H hu) (uClosed u hu x hx)
  have closed (x : Fin s→K) (hx : x∈E) (y : Fin s→K) (hy : y∈E) : x*y∈E := by
    obtain ⟨H,J,v,hv,_,_,shape⟩ := stage_chart_repr chart (by decide) hx
    have form : x*y=evalNodes A H*y+evalNodes A J*(w*y)+v*y := by
      rw [shape]
      ext i
      simp only [Pi.mul_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply]
      ring
    rw [form]
    exact E.add_mem (E.add_mem (eval_mul_mem cE H hy) (eval_mul_mem cE J (wTimes y hy)))
      (uE (uTimes v hv y hy))
  obtain ⟨e,he,mask⟩ := LiveCore.exists_live_indicator U uClosed
  have eOn (i : Fin s) : e i≠0 ↔ LiveCore.live U i := by
    by_cases li : LiveCore.live U i <;> simp [mask i,li]
  have coreAgree (v : Fin s→K) (hv : v∈U) (i j : Fin s) (_ : e i≠0) (_ : e j≠0)
      (eij : coreTrace U i=coreTrace U j) : v i=v j :=
    congrFun eij (⟨v,hv⟩ : U)
  have coreSep (i j : Fin s) (_ : e i≠0) (_ : e j≠0) (ne : coreTrace U i≠coreTrace U j) :
      ∃v∈U,v i≠v j := by
    obtain ⟨v,hv⟩ := Function.ne_iff.mp ne
    exact ⟨v.val,v.property,hv⟩
  have coreOrbit : labelOrbit (coreTrace U) e=U :=
    labelOrbit_eq_of_coordinate_separation uClosed he
      (fun i nz => by rw [mask,if_pos ((eOn i).mp nz)])
      (fun v hv i z => LiveCore.val_eq_zero_of_not_live (fun li=>((eOn i).mpr li) z) hv)
      coreAgree coreSep
  have coreCount : (activeLabels (coreTrace U) e).card=3 := by
    rw [←labelOrbit_rank (coreTrace U) e,coreOrbit,uRank]
  have coreLabelCount : (coreLabels U).card=3 := by
    have sameSets : coreLabels U=activeLabels (coreTrace U) e := by
      ext label
      simp only [mem_coreLabels,mem_activeLabels,eOn]
    rwa [sameSets]
  have ce : diag (nodes A) e∈U := cU (Submodule.mem_map_of_mem he)
  have reading (i j : Fin s) (eq : lab i=lab j) :
      nodes A i=nodes A j ∧ w i=w j ∧ ∀v∈U,v i=v j := by
    rcases label_phase_match eq with ⟨hi,hj,tr⟩|⟨hi,hj,pr⟩
    · have cq := congrFun tr (⟨diag (nodes A) e,ce⟩ : U)
      change (diag (nodes A) e) i=(diag (nodes A) e) j at cq
      have cs : nodes A i=nodes A j := by
        simpa only [diag_apply,mask i,mask j,if_pos hi,if_pos hj,mul_one] using cq
      exact ⟨cs,(clean i hi).trans (clean j hj).symm,fun v hv=>congrFun tr (⟨v,hv⟩ : U)⟩
    · exact ⟨congrArg Prod.fst pr,congrArg Prod.snd pr,fun v hv=>
        (LiveCore.val_eq_zero_of_not_live hi hv).trans (LiveCore.val_eq_zero_of_not_live hj hv).symm⟩
  have same (v : Fin s→K) (hv : v∈E) (i j : Fin s) (eq : lab i=lab j) : v i=v j := by
    obtain ⟨H,J,z,hz,_,_,form⟩ := stage_chart_repr chart (by decide) hv
    obtain ⟨cs,ws,us⟩ := reading i j eq
    rw [form]
    simp only [Pi.add_apply,evalNodes_apply,weightedEval_apply,cs,ws,us z hz]
  have separate (i j : Fin s) (ne : lab i≠lab j) : ∃v∈E,v i≠v j := by
    by_cases hi : LiveCore.live U i
    · by_cases hj : LiveCore.live U j
      · have notTr : coreTrace U i≠coreTrace U j := by
          intro eq
          exact ne (by simp only [lab,phaseLabel,if_pos hi,if_pos hj,eq])
        obtain ⟨v,hv,nz⟩ := coreSep i j ((eOn i).mpr hi) ((eOn j).mpr hj) notTr
        exact ⟨v,uE hv,nz⟩
      · refine ⟨e,uE he,?_⟩
        rw [mask,mask,if_pos hi,if_neg hj]
        exact one_ne_zero
    · by_cases hj : LiveCore.live U j
      · refine ⟨e,uE he,?_⟩
        rw [mask,mask,if_neg hi,if_pos hj]
        exact zero_ne_one
      · by_cases cs : nodes A i=nodes A j
        · exact ⟨w,wE,fun ws=>ne (by simp only [lab,phaseLabel,if_neg hi,if_neg hj,headPair,cs,ws])⟩
        · exact ⟨nodes A,nodesE,cs⟩
  have full : labelOrbit lab (1:Fin s→K)=E :=
    labelOrbit_eq_of_coordinate_separation closed one (fun _ _=>rfl)
      (fun _ _ _ nz=>(one_ne_zero nz).elim)
      (fun v hv i j _ _=>same v hv i j) (fun i j _ _=>separate i j)
  have ambient : (Finset.univ.image lab).card=17 := by
    have h := labelOrbit_rank lab (1:Fin s→K)
    rw [full,show E=treeSpace A 10 from rfl,eRank] at h
    have all : activeLabels lab (1:Fin s→K)=Finset.univ.image lab := by
      ext a
      rw [mem_activeLabels,Finset.mem_image]
      constructor
      · rintro ⟨i, _, hi⟩
        exact ⟨i, Finset.mem_univ _, hi⟩
      · rintro ⟨i, _, hi⟩
        exact ⟨i, (one_ne_zero : (1 : K) ≠ 0), hi⟩
    rw [all] at h
    exact h.symm
  have noncore : (noncorePairs A U w).card=14 := by
    have h := congrArg Finset.card (label_image_split (A:=A) (U:=U) (w:=w) mask)
    change (Finset.univ.image lab).card=
      ((activeLabels (coreTrace U) e).disjSum (noncorePairs A U w)).card at h
    rw [ambient,Finset.card_disjSum,coreCount] at h
    omega
  have coreMask (i : Fin s) (hi : LiveCore.live U i) : labelIndicator lab (lab i)∈U := by
    have s := labelSlice_mem_of_coordinate_separation uClosed he coreAgree coreSep i ((eOn i).mpr hi)
    have eq : labelIndicator lab (lab i)=labelSlice (coreTrace U) e (coreTrace U i) := by
      ext j
      rw [labelSlice_apply,mask j]
      by_cases hj : LiveCore.live U j
      · by_cases tr : coreTrace U j=coreTrace U i <;>
          simp [labelIndicator,lab,phaseLabel,hi,hj,tr]
      · simp [labelIndicator,lab,phaseLabel,hi,hj]
    rwa [eq]
  exact ⟨ambient,coreLabelCount,noncore,same,fun i j eq=>(reading i j eq).1,coreMask,closed,full⟩

/-- The aggregate weight of an entire live core atom, on the original
rows, vanishes by a single paid homogeneous-defect probe. -/
theorem core_class_mass_zero {j p : ℕ} {b : Fin s→K} (ho : HasOrder p A b)
    (core : U≤zeroSpace A j) (pay : j+1≤p)
    (S : SquareClassGeometry A U w) {i : Fin s} (li : LiveCore.live U i) :
    (∑ a ∈ Finset.univ.filter (fun a=>phaseLabel A U w a=phaseLabel A U w i), b a)=0 := by
  let f := phaseLabel A U w
  have test : probe A b 0 (labelIndicator f (f i))=0 :=
    probe_zeroSpace (k:=0) ho (by simpa only [Nat.zero_add] using pay) (core (S.coreIndicator i li))
  change (∑ a, (b a*(nodes A a)^0)*(labelIndicator f (f i)) a)=0 at test
  change (∑ a ∈ Finset.univ.filter (fun a=>f a=f i), b a)=0
  calc
    _ = ∑ a,(b a*(nodes A a)^0)*(labelIndicator f (f i)) a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases eq : f a=f i <;> simp [labelIndicator,eq]
    _ = 0 := test

section OrderThirteen
variable [CharZero K]
variable {T : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U₀ : Submodule K (Fin 19→K)} {w₀ u v : Fin 19→K} {G P R Q : K[X]}

private theorem paid_seven_eval_one_ne (ha : ∀ i j,i≤j → T i j=0) (ho : HasOrder 13 T b)
    (degree : G.natDegree=7) (paid : evalNodes T G∈zeroSpace T 7) : G.eval 1≠0 := by
  apply HyperplaneTerminal.seven_paid_not_one degree
  · have orig := origin_zeroSpace ha 7 paid
    have nodes0 : nodes T (0:Fin 19)=0 := by
      change (∑ j,T 0 j*1)=0
      exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
    change G.eval (nodes T (0:Fin 19))=0 at orig
    rwa [nodes0] at orig
  · intro i
    have hi := i.isLt
    exact (probe_evalNodes ho G i.val (by omega)).symm.trans
      (probe_zeroSpace (k:=i.val) ho (by omega) paid)

/-- No 17-class ambient algebra can arise from a noncancelled leading
square profile in the genuine ordinary grade-nine/ten charts. The
terminal exclusion uses only the paid root clock 1, and only the
actual aggregated weights at original label classes. -/
theorem ordinary_clock_top_impossible (ha : ∀ i j,i≤j → T i j=0) (ho : HasOrder 13 T b)
    (cU : U₀.map (diag (nodes T))≤U₀) (closed : ∀ x∈U₀, ∀ y∈U₀, x*y∈U₀)
    (clean : ∀i,LiveCore.live U₀ i → w₀ i=0)
    (coreFour : U₀≤zeroSpace T 4) (headFour : w₀∈zeroSpace T 4)
    (uRank : finrank K U₀=3) (r₉ : finrank K (treeSpace T 9)=16)
    (r₁₀ : finrank K (treeSpace T 10)=17)
    (chart₉ : treeSpace T 9=(coeffEval T 6).range⊔chain (diag (nodes T)) U₀ w₀ 6)
    (chart₁₀ : treeSpace T 10=(coeffEval T 6).range⊔chain (diag (nodes T)) U₀ w₀ 7)
    (hu : u∈U₀) (hv : v∈U₀)
    (square : w₀*w₀=evalNodes T P+weightedEval (nodes T) w₀ R+u)
    (mesh : evalNodes T G=weightedEval (nodes T) w₀ Q+v)
    (gd : G.natDegree=7) (pd : P.natDegree≤6) (rd : R.natDegree≤4) (qd : Q.natDegree≤3)
    (gPaid : evalNodes T G∈zeroSpace T 7) : (G-R*Q).coeff 7=0 := by
  by_contra top
  have law := transport cU clean hu hv square mesh
  have stable := clock_stable_of_top_ne cU chart₁₀ gd pd qd rd law top
  have s₈ : w₀*w₀∈zeroSpace T 8 := zeroSpace_mul headFour headFour
  have s₁₀ := treeSpace_mono T (by decide : 8≤10) (zeroSpace_le_treeSpace T 8 s₈)
  have S := square_geometry_of_clock_stability cU closed clean stable chart₁₀ uRank r₁₀ s₁₀
  let f := phaseLabel T U₀ w₀
  let D := noncorePairs T U₀ w₀
  have frame : finrank K (treeSpace T 9)+1=(Finset.univ.image f).card := by
    change finrank K (treeSpace T 9)+1=(Finset.univ.image (phaseLabel T U₀ w₀)).card
    rw [r₉,S.ambientCount]
  have refl (i j : Fin 19) (eq : f i=f j) : reflectedClock T i=reflectedClock T j := by
    simp only [reflectedClock,Pi.sub_apply,Pi.one_apply,S.clock i j eq]
  have gOne := paid_seven_eval_one_ne ha ho gd gPaid
  apply HyperplaneTerminal.physical_label_grade_impossible (j:=9) ha ho f refl frame S.same (by decide)
  intro h mass at0 selector
  have dead : ¬LiveCore.live U₀ h := fun li=>mass (core_class_mass_zero ho coreFour (by decide) S li)
  have atOne : nodes T h=1 := by
    change (1:K)-nodes T h=0 at at0
    exact (sub_eq_zero.mp at0).symm
  have representative (p : K×K) (hp : p∈D) : ∃i,¬LiveCore.live U₀ i ∧ headPair T w₀ i=p :=
    mem_noncorePairs.mp hp
  have meshP (p : K×K) (hp : p∈D) : G.eval p.1=Q.eval p.1*p.2 := by
    obtain ⟨i,di,rfl⟩ := representative p hp
    have z := congrFun mesh i
    simpa only [headPair,evalNodes_apply,weightedEval_apply,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live di hv,add_zero] using z
  have squareP (p : K×K) (hp : p∈D) : p.2^2=R.eval p.1*p.2+P.eval p.1 := by
    obtain ⟨i,di,rfl⟩ := representative p hp
    have z := congrFun square i
    simpa only [headPair,pow_two,Pi.mul_apply,evalNodes_apply,weightedEval_apply,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live di hu,add_zero,zero_add,add_comm] using z
  obtain ⟨H,J,z,hz,dH,dJ,form⟩ := stage_chart_repr chart₉ (by decide) selector
  have inside : headPair T w₀ h∈D := mem_noncorePairs.mpr ⟨h,dead,rfl⟩
  have witness : G.eval (headPair T w₀ h).1≠0 := by
    change G.eval (nodes T h)≠0
    rwa [atOne]
  have size : 14≤D.card := S.noncoreCount.ge
  have fit (p : K×K) (hp : p∈D) :
      H.eval p.1+J.eval p.1*p.2=(if p=headPair T w₀ h then 1 else 0) := by
    obtain ⟨i,di,rfl⟩ := representative p hp
    have z := congrFun form i
    by_cases pair : headPair T w₀ i=headPair T w₀ h
    · have cls : f i=f h := by simp only [f,phaseLabel,if_neg di,if_neg dead,pair]
      rw [if_pos pair]
      simpa only [headPair,evalNodes_apply,weightedEval_apply,Pi.add_apply,
        LiveCore.val_eq_zero_of_not_live di hz,add_zero,if_pos cls] using z.symm
    · have cls : f i≠f h := by
        intro fe
        apply pair
        exact Sum.inr.inj (by simpa only [f,phaseLabel,if_neg di,if_neg dead] using fe)
      rw [if_neg pair]
      simpa only [headPair,evalNodes_apply,weightedEval_apply,Pi.add_apply,
        LiveCore.val_eq_zero_of_not_live di hz,add_zero,if_neg cls] using z.symm
  exact NativeQuadraticClassSelector.no_grade_nine_selector_of_mesh_nonzero
    size meshP squareP gd.le qd dH (Nat.le_of_lt_succ dJ) inside witness fit

end OrderThirteen

end
end RKResearch.Certified.Graded.ERK13OrdinarySquare

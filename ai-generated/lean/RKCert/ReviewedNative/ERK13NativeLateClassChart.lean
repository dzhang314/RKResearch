module

public import RKCert.ReviewedNative.ERK13OrdinarySquareClasses
public import RKCert.ReviewedNative.ERK13NativeLatePhysicalLabels
public import RKCert.ReviewedNative.ERK13NativeMarkedStaircase
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The exact two charts consumed by the late mass theorem

The observer is the unmarked grade-nine band, not necessarily the whole
grade nine. The unmarked coordinate algebra is likewise a summand inside
genuine grade ten. The last original coordinate is adjoined explicitly. -/

namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Reverse Polynomial Module PhysicalCensus ERK13OrdinarySquare RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators

noncomputable section

variable {K α : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
variable {P R Q G : K[X]}
set_option maxHeartbeats 1000000

abbrev unmarkedClasses (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) :=
  labelOrbit (phaseLabel A U w) (1 : Fin 19 → K)

abbrev observerBand (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) :=
  (coeffEval A 6).range ⊔ chain (diag (nodes A)) U w 6

def lateLabel (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (i : Fin 19) :=
  (phaseLabel A U w i, decide (i = Fin.last 18))

structure MassClassChart (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (P R Q G : K[X]) : Prop where
  coreStable : U.map (diag (nodes A)) ≤ U
  coreClosed : ∀ u ∈ U, ∀ v ∈ U, u*v ∈ U
  clean : ∀ i, LiveCore.live U i → w i = 0
  coreFour : U ≤ zeroSpace A 4
  headFour : w ∈ zeroSpace A 4
  eightInside : treeSpace A 8 ≤ unmarkedClasses A U w
  observerInside : observerBand A U w ≤ unmarkedClasses A U w
  observerPay : observerBand A U w ≤ treeSpace A 9
  observerRank : finrank K (observerBand A U w) = 16
  unmarkedPay : unmarkedClasses A U w ≤ treeSpace A 10
  unmarkedRank : finrank K (unmarkedClasses A U w) = 17
  terminalOutside : coordinate (K:=K) (Fin.last 18) ∉ unmarkedClasses A U w
  noncoreCount : (noncorePairs A U w).card = 14
  square : ∃ u ∈ U, w*w = evalNodes A P + weightedEval (nodes A) w R + u
  mesh : ∃ v ∈ U, evalNodes A G = weightedEval (nodes A) w Q + v
  pDegree : P.natDegree ≤ 6
  rDegree : R.natDegree ≤ 4
  qDegree : Q.natDegree ≤ 3
  gDegree : G.natDegree = 7
  leading : (G - R*Q).coeff 7 ≠ 0

/-- For the unit support the existing native label orbit is exactly the
original-coordinate columns constant on the actual label fibers. -/
theorem label_orbit_one_iff {s : ℕ} (f : Fin s → α) (u : Fin s → K) :
    u ∈ labelOrbit f (1 : Fin s → K) ↔ ∀ i j, f i=f j → u i=u j := by
  classical
  constructor
  · rintro ⟨v,rfl⟩ i j eq
    rw [labelCombination_eval_of_live f (1 : Fin s → K) v (i:=i) (by simp),
      labelCombination_eval_of_live f (1 : Fin s → K) v (i:=j) (by simp)]
    have fi : f i ∈ activeLabels f (1 : Fin s → K) :=
      mem_activeLabels.mpr ⟨i, by simp, rfl⟩
    have fj : f j ∈ activeLabels f (1 : Fin s → K) :=
      mem_activeLabels.mpr ⟨j, by simp, rfl⟩
    have lab : (⟨f i, fi⟩ : activeLabels f (1 : Fin s → K)) = ⟨f j,fj⟩ :=
      Subtype.ext eq
    simpa only [Pi.one_apply,mul_one] using congrArg v lab
  · intro same
    let rep (a : activeLabels f (1 : Fin s → K)) : Fin s :=
      Classical.choose (mem_activeLabels.mp a.property)
    have hp (a : activeLabels f (1 : Fin s → K)) : f (rep a) = a.val :=
      (Classical.choose_spec (mem_activeLabels.mp a.property)).2
    let v (a : activeLabels f (1 : Fin s → K)) := u (rep a)
    refine ⟨v,funext (fun i => ?_)⟩
    rw [labelCombination_eval_of_live f (1 : Fin s → K) v (i:=i) (by simp)]
    let a : activeLabels f (1 : Fin s → K) := ⟨f i, mem_activeLabels.mpr ⟨i,by simp,rfl⟩⟩
    change v a*(1:K)=u i
    rw [mul_one]
    exact same (rep a) i (hp a)

theorem phase_const_of_mem {u : Fin 19 → K} (hu : u ∈ unmarkedClasses A U w)
    {i j : Fin 19} (eq : phaseLabel A U w i = phaseLabel A U w j) : u i=u j :=
  (label_orbit_one_iff (phaseLabel A U w) u).mp hu i j eq

theorem phase_indicator_mem (t : Fin 19) :
    (labelIndicator (phaseLabel A U w) (phaseLabel A U w t) : Fin 19 → K) ∈
      unmarkedClasses A U w := by
  apply (label_orbit_one_iff _ _).mpr
  intro i j eq
  by_cases atJ : phaseLabel A U w j=phaseLabel A U w t
  · have atI := eq.trans atJ
    simp [labelIndicator,atI,atJ]
  · have atI : phaseLabel A U w i≠phaseLabel A U w t := fun h=>atJ (eq.symm.trans h)
    simp [labelIndicator,atI,atJ]

theorem dead_pair_label_iff {i j : Fin 19} (hi : ¬LiveCore.live U i)
    (hj : ¬LiveCore.live U j) :
    phaseLabel A U w i = phaseLabel A U w j ↔ headPair A w i = headPair A w j := by
  simp only [phaseLabel,if_neg hi,if_neg hj,Sum.inr.injEq]

theorem phase_clock_head (S : MassClassChart A U w P R Q G)
    {i j : Fin 19} (eq : phaseLabel A U w i=phaseLabel A U w j) :
    nodes A i=nodes A j ∧ w i=w j := by
  by_cases hi : LiveCore.live U i <;> by_cases hj : LiveCore.live U j
  · obtain ⟨u,hu,h⟩ := LiveCore.exists_live_indicator U S.coreClosed
    have ce : diag (nodes A) u ∈ U := S.coreStable (Submodule.mem_map_of_mem hu)
    have tr : coreTrace U i=coreTrace U j :=
      Sum.inl.inj (by simpa only [phaseLabel,if_pos hi,if_pos hj] using eq)
    have test := congrFun tr (⟨diag (nodes A) u,ce⟩ : U)
    change diag (nodes A) u i=diag (nodes A) u j at test
    exact ⟨by simpa only [diag_apply,h i,h j,if_pos hi,if_pos hj,mul_one] using test,
      (S.clean i hi).trans (S.clean j hj).symm⟩
  · simp [phaseLabel,hi,hj] at eq
  · simp [phaseLabel,hi,hj] at eq
  · have hp := (dead_pair_label_iff hi hj).mp eq
    exact ⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩

theorem phase_core_indicator (S : MassClassChart A U w P R Q G)
    {t : Fin 19} (live : LiveCore.live U t) :
    labelIndicator (phaseLabel A U w) (phaseLabel A U w t) ∈ U := by
  obtain ⟨u,hu,mask⟩ := LiveCore.exists_live_indicator U S.coreClosed
  have uOn (i : Fin 19) : u i≠0 ↔ LiveCore.live U i := by
    by_cases hi : LiveCore.live U i <;> simp [mask i,hi]
  have same (v : Fin 19 → K) (hv : v ∈ U) (i j : Fin 19)
      (_ : u i≠0) (_ : u j≠0) (eq : coreTrace U i=coreTrace U j) : v i=v j :=
    congrFun eq (⟨v,hv⟩ : U)
  have sep (i j : Fin 19) (_ : u i≠0) (_ : u j≠0)
      (ne : coreTrace U i≠coreTrace U j) : ∃ v ∈ U, v i≠v j := by
    obtain ⟨v,hv⟩ := Function.ne_iff.mp ne
    exact ⟨v.val,v.property,hv⟩
  have paid := labelSlice_mem_of_coordinate_separation S.coreClosed hu same sep t ((uOn t).mpr live)
  have eq : labelIndicator (phaseLabel A U w) (phaseLabel A U w t) =
      labelSlice (coreTrace U) u (coreTrace U t) := by
    ext j
    rw [labelSlice_apply,mask j]
    by_cases hj : LiveCore.live U j
    · by_cases tr : coreTrace U j=coreTrace U t <;> simp [labelIndicator,phaseLabel,live,hj,tr]
    · simp [labelIndicator,phaseLabel,live,hj]
  rw [eq]
  exact paid

theorem late_label_off_last {i j : Fin 19} (hi : i ≠ Fin.last 18) (hj : j ≠ Fin.last 18) :
    lateLabel A U w i = lateLabel A U w j ↔ phaseLabel A U w i = phaseLabel A U w j := by
  constructor
  · intro eq
    exact congrArg Prod.fst eq
  · intro eq
    have iBit : decide (i=Fin.last 18)=false := decide_eq_false_iff_not.mpr hi
    have jBit : decide (j=Fin.last 18)=false := decide_eq_false_iff_not.mpr hj
    change (phaseLabel A U w i,decide (i=Fin.last 18))=
      (phaseLabel A U w j,decide (j=Fin.last 18))
    rw [iBit,jBit,eq]

/-- There is a real earlier row at the terminal's clock and unmarked label.
This follows from the measured line's absence, not a signed weight claim. -/
theorem exists_terminal_twin (S : MassClassChart A U w P R Q G) :
    ∃ j : Fin 19, j ≠ Fin.last 18 ∧ phaseLabel A U w j=phaseLabel A U w (Fin.last 18) := by
  classical
  by_contra none
  let L := Fin.last 18
  have eq : (labelIndicator (phaseLabel A U w) (phaseLabel A U w L) : Fin 19 → K)
      = coordinate L := by
    ext i
    by_cases h : i=L
    · subst i
      simp [labelIndicator,coordinate]
    · have off : phaseLabel A U w i≠phaseLabel A U w L :=
        fun z=>none ⟨i,h,z⟩
      simp [labelIndicator,off,coordinate,Ne.symm h]
  exact S.terminalOutside (eq ▸ phase_indicator_mem L)

theorem late_union_marked (S : MassClassChart A U w P R Q G)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    {rad : ℕ} {V : Submodule K (Fin 19→K)} {v : Fin 19→K}
    (H : ERK13NativeFirst.NativePaidHead A b rad V v) :
    markedTreeSpace A b 10 = unmarkedClasses A U w ⊔ K∙coordinate (Fin.last 18) := by
  have rk := (ERK13NativeFirst.marked_staircase_ranks13 ha ho H seed).1 10 (by decide) (by decide)
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · change _ ≤ treeSpace A 10 ⊔ terminalMark A b
    rw [terminalMark,if_pos seed]
    exact sup_le_sup S.unmarkedPay le_rfl
  · rw [rk,Submodule.finrank_sup_span_singleton S.terminalOutside,S.unmarkedRank] <;> decide

/-- The marked algebra is the unmarked algebra plus the one literal
coordinate. In particular no extra (unpaid) marked masks are input. -/
theorem late_label_orbit (S : MassClassChart A U w P R Q G) :
    labelOrbit (lateLabel A U w) (1 : Fin 19 → K) =
      unmarkedClasses A U w ⊔ K∙coordinate (Fin.last 18) := by
  classical
  let L := Fin.last 18
  obtain ⟨j,jL,jLab⟩ := exists_terminal_twin S
  ext z
  constructor
  · intro hz
    have same := (label_orbit_one_iff (lateLabel A U w) z).mp hz
    let z0 := z - (z L-z j) • (coordinate (K:=K) L)
    have atL : z0 L=z j := by
      change z L-(z L-z j)*coordinate (K:=K) L L=z j
      rw [show coordinate (K:=K) L L=1 by simp [coordinate],mul_one]
      ring
    have offL (i : Fin 19) (iL : i≠L) : z0 i=z i := by
      change z i-(z L-z j)*coordinate (K:=K) L i=z i
      simp [coordinate,Ne.symm iL]
    have zB : z0 ∈ unmarkedClasses A U w := by
      apply (label_orbit_one_iff _ _).mpr
      intro x y xy
      by_cases xL : x=L <;> by_cases yL : y=L
      · rw [xL,yL]
      · subst x
        rw [atL,offL y yL]
        exact same j y ((late_label_off_last jL yL).mpr (jLab.trans xy))
      · subst y
        rw [offL x xL,atL]
        exact same x j ((late_label_off_last xL jL).mpr (xy.trans jLab.symm))
      · rw [offL x xL,offL y yL]
        exact same x y ((late_label_off_last xL yL).mpr xy)
    refine Submodule.mem_sup.mpr ⟨z0,zB,(z L-z j) • coordinate L,?_,?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · dsimp only [z0]
      abel
  · intro hz
    obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    apply (label_orbit_one_iff _ _).mpr
    intro i k eq
    have ue := phase_const_of_mem hu (congrArg Prod.fst eq)
    have ce : coordinate (K:=K) L i=coordinate L k := by
      have bit := congrArg Prod.snd eq
      change decide (i=L)=decide (k=L) at bit
      by_cases hi : i=L <;> by_cases hk : k=L
      · simp [coordinate,hi,hk]
      · simp [hi,hk] at bit
      · simp [hi,hk] at bit
      · simp [coordinate,Ne.symm hi,Ne.symm hk]
    change u i+c*coordinate (K:=K) L i=u k+c*coordinate (K:=K) L k
    rw [ue,ce]

theorem marked_label_card_and_masks (S : MassClassChart A U w P R Q G)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    {rad : ℕ} {V : Submodule K (Fin 19→K)} {v : Fin 19→K}
    (H : ERK13NativeFirst.NativePaidHead A b rad V v) :
    (Finset.univ.image (lateLabel A U w)).card = 18 ∧
      ∀ t : Fin 19, (fun i => if lateLabel A U w i=lateLabel A U w t then (1:K) else 0) ∈
        markedTreeSpace A b 10 := by
  classical
  have orb : labelOrbit (lateLabel A U w) (1 : Fin 19 → K)=markedTreeSpace A b 10 :=
    (late_label_orbit S).trans (late_union_marked S ha ho seed H).symm
  constructor
  · have markedRank : finrank K (markedTreeSpace A b 10) = 18 :=
      (ERK13NativeFirst.marked_staircase_ranks13 ha ho H seed).1 10 (by decide) (by decide)
    have rankActive : (activeLabels (lateLabel A U w) (1 : Fin 19 → K)).card = 18 := by
      rw [← labelOrbit_rank (lateLabel A U w) (1 : Fin 19 → K), orb]
      exact markedRank
    have sets : activeLabels (lateLabel A U w) (1 : Fin 19 → K) =
        Finset.univ.image (lateLabel A U w) := by
      ext t
      rw [mem_activeLabels, Finset.mem_image]
      constructor
      · rintro ⟨i, _, hi⟩
        exact ⟨i, Finset.mem_univ _, hi⟩
      · rintro ⟨i, _, hi⟩
        exact ⟨i, one_ne_zero, hi⟩
    exact (congrArg Finset.card sets).symm.trans rankActive
  · intro t
    rw [←orb]
    apply (label_orbit_one_iff _ _).mpr
    intro i j eq
    rw [eq]

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

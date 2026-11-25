module

public import RKCert.ReviewedNative.ERK13NativeLateClassChart
public import RKCert.ReviewedNative.NativeQuadraticPairBound
import RKCert.ReviewedNative.BufferedClockLeakage
import Mathlib.Data.Finset.Sum
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Rank sandwich on the actual, unmarked late square

The counted clock eliminant bounds the distinct physical pairs even at
common mesh roots. The bounded head-polynomial space reads only the phase
label. Its measured rank 17 therefore fills the phase orbit; no unmarked
tree-space equality, prior pointwise closure, or true terminal timing at
grade nine or ten is used. -/
namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Polynomial Module Reverse PhysicalCensus ERK13OrdinarySquare RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {U : Submodule K (Fin 19 → K)}
variable {w : Fin 19 → K} {P R Q G : K[X]}
set_option maxHeartbeats 1200000

abbrev lateSection (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (n : ℕ) :=
  (coeffEval A 6).range ⊔ chain (diag (nodes A)) U w n

private theorem raw_phase_match {i j : Fin 19} (eq : phaseLabel A U w i=phaseLabel A U w j) :
    (LiveCore.live U i ∧ LiveCore.live U j ∧ coreTrace U i=coreTrace U j) ∨
    (¬LiveCore.live U i ∧ ¬LiveCore.live U j ∧ headPair A w i=headPair A w j) := by
  by_cases hi : LiveCore.live U i <;> by_cases hj : LiveCore.live U j
  · exact Or.inl ⟨hi,hj,Sum.inl.inj (by simpa only [phaseLabel,if_pos hi,if_pos hj] using eq)⟩
  · simp [phaseLabel,hi,hj] at eq
  · simp [phaseLabel,hi,hj] at eq
  · exact Or.inr ⟨hi,hj,Sum.inr.inj (by simpa only [phaseLabel,if_neg hi,if_neg hj] using eq)⟩

private theorem raw_image_split {e : Fin 19→K} (mask : ∀i,e i=if LiveCore.live U i then 1 else 0) :
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

/-- Count all components of the unmarked phase without first identifying
it with any true graded tree space. -/
theorem late_phase_census (cU : U.map (diag (nodes A)) ≤ U)
    (uClosed : ∀ x∈U, ∀ y∈U, x*y∈U) (clean : ∀ i, LiveCore.live U i → w i=0)
    (n : ℕ) :
    lateSection A U w n ≤ unmarkedClasses A U w ∧
      finrank K (unmarkedClasses A U w) = finrank K U + (noncorePairs A U w).card := by
  let lab := phaseLabel A U w
  obtain ⟨e,he,mask⟩ := LiveCore.exists_live_indicator U uClosed
  have eOn (i : Fin 19) : e i≠0 ↔ LiveCore.live U i := by
    by_cases li : LiveCore.live U i <;> simp [mask i,li]
  have coreAgree (v : Fin 19→K) (hv : v∈U) (i j : Fin 19) (_ : e i≠0) (_ : e j≠0)
      (eij : coreTrace U i=coreTrace U j) : v i=v j :=
    congrFun eij (⟨v,hv⟩ : U)
  have coreSep (i j : Fin 19) (_ : e i≠0) (_ : e j≠0) (ne : coreTrace U i≠coreTrace U j) :
      ∃v∈U,v i≠v j := by
    obtain ⟨v,hv⟩ := Function.ne_iff.mp ne
    exact ⟨v.val,v.property,hv⟩
  have coreOrbit : labelOrbit (coreTrace U) e=U :=
    labelOrbit_eq_of_coordinate_separation uClosed he
      (fun i nz => by rw [mask,if_pos ((eOn i).mp nz)])
      (fun v hv i z => LiveCore.val_eq_zero_of_not_live (fun li=>((eOn i).mpr li) z) hv)
      coreAgree coreSep
  have ce : diag (nodes A) e∈U := cU (Submodule.mem_map_of_mem he)
  have reading (i j : Fin 19) (eq : lab i=lab j) :
      nodes A i=nodes A j ∧ w i=w j ∧ ∀v∈U,v i=v j := by
    rcases raw_phase_match eq with ⟨hi,hj,tr⟩|⟨hi,hj,pr⟩
    · have cq := congrFun tr (⟨diag (nodes A) e,ce⟩ : U)
      change (diag (nodes A) e) i=(diag (nodes A) e) j at cq
      have cs : nodes A i=nodes A j := by
        simpa only [diag_apply,mask i,mask j,if_pos hi,if_pos hj,mul_one] using cq
      exact ⟨cs,(clean i hi).trans (clean j hj).symm,fun v hv=>congrFun tr (⟨v,hv⟩ : U)⟩
    · exact ⟨congrArg Prod.fst pr,congrArg Prod.snd pr,fun v hv=>
        (LiveCore.val_eq_zero_of_not_live hi hv).trans (LiveCore.val_eq_zero_of_not_live hj hv).symm⟩
  constructor
  · intro y hy
    apply (label_orbit_one_iff (phaseLabel A U w) y).mpr
    intro i j same
    obtain ⟨v,hv,d,hd,eq⟩ := Submodule.mem_sup.mp hy
    obtain ⟨H,_,rfl⟩ := exists_polynomial_of_coeff_range hv
    obtain ⟨t,ht,J,_,form⟩ := HeadFiber.exists_poly hd
    obtain ⟨clock,head,core⟩ := reading i j same
    rw [←eq,form]
    simp only [Pi.add_apply,evalNodes_apply,weightedEval_apply,clock,head,core t ht]
  · have all : activeLabels lab (1 : Fin 19 → K) = Finset.univ.image lab := by
      ext t
      rw [mem_activeLabels,Finset.mem_image]
      constructor
      · rintro ⟨i,_,hi⟩
        exact ⟨i,Finset.mem_univ _,hi⟩
      · rintro ⟨i,_,hi⟩
        exact ⟨i,(one_ne_zero : (1:K) ≠ 0),hi⟩
    have partition : Finset.univ.image lab =
        (activeLabels (coreTrace U) e).disjSum (noncorePairs A U w) :=
      raw_image_split mask
    have coreCount : (activeLabels (coreTrace U) e).card = finrank K U := by
      rw [←labelOrbit_rank (coreTrace U) e,coreOrbit]
    change finrank K (labelOrbit lab (1 : Fin 19 → K)) = _
    rw [labelOrbit_rank,all,partition,Finset.card_disjSum,coreCount]

/-- Nonzero leading term forces both the exact count and equality to
the rank-17 orbit, including zero-head pairs and Q equal to zero. -/
theorem late_section_full_of_leading
    (cU : U.map (diag (nodes A)) ≤ U) (closed : ∀ x∈U, ∀ y∈U, x*y∈U)
    (clean : ∀ i, LiveCore.live U i → w i=0)
    (uRank : finrank K U=3) (bandRank : finrank K (lateSection A U w 7)=17)
    {u v : Fin 19 → K} (hu : u∈U) (hv : v∈U)
    (sq : w*w=evalNodes A P+weightedEval (nodes A) w R+u)
    (me : evalNodes A G=weightedEval (nodes A) w Q+v)
    (gd : G.natDegree=7) (pd : P.natDegree≤6) (rd : R.natDegree≤4) (qd : Q.natDegree≤3)
    (top : (G-R*Q).coeff 7≠0) :
    lateSection A U w 7 = unmarkedClasses A U w ∧ (noncorePairs A U w).card=14 := by
  let T := noncorePairs A U w
  have meshP (p : K×K) (hp : p∈T) : G.eval p.1=Q.eval p.1*p.2 := by
    obtain ⟨i,di,rfl⟩ := mem_noncorePairs.mp hp
    have z := congrFun me i
    simpa only [headPair,evalNodes_apply,weightedEval_apply,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live di hv,add_zero] using z
  have squareP (p : K×K) (hp : p∈T) : p.2^2=R.eval p.1*p.2+P.eval p.1 := by
    obtain ⟨i,di,rfl⟩ := mem_noncorePairs.mp hp
    have z := congrFun sq i
    simpa only [headPair,pow_two,Pi.mul_apply,evalNodes_apply,weightedEval_apply,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live di hu,add_zero,zero_add,add_comm] using z
  have cap : (noncorePairs A U w).card≤14 :=
    NativeQuadraticClassSelector.leading_pair_count_le_fourteen T meshP squareP gd qd rd pd top
  obtain ⟨inside,count⟩ := late_phase_census cU closed clean 7
  have low := Submodule.finrank_mono inside
  have up : finrank K (unmarkedClasses A U w)≤17 := by rw [count,uRank]; omega
  have exactCount : (noncorePairs A U w).card=14 := by
    rw [bandRank,count,uRank] at low
    omega
  exact ⟨Submodule.eq_of_le_of_finrank_le inside (bandRank.symm ▸ up),exactCount⟩

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

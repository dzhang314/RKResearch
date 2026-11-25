module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoClasses
public import RKCert.ReviewedNative.ERK13NativeLatePairSpine
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # End of the entire early degree-six branch

The high square pays the support and ratio hypotheses of the existing
physical final-three obstruction. The pure exits and the high-square exit
dispatch from the same actual marked chart; no F7 rank is assumed. -/

namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Module Reverse PhysicalCensus HyperplaneTerminal NativeFinalThree
open ERK13NativeLatePhysicalFold ERK13OrdinarySquare
open RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w v : Fin 19→K}
variable {G P R Q : K[X]}
variable {e : Fin 18→Fin 19} {r : Fin 19→Fin 18} {m : Fin 19}
set_option maxHeartbeats 1800000
set_option maxRecDepth 2300

private theorem lift_coordinate_eq_label
    (fibres : ∀ i t,r i=t ↔ lobattoClass A U v i=lobattoClass A U v (e t)) (t : Fin 18) :
    (fun i=>coordinate (K:=K) t (r i))=
      labelIndicator (lobattoClass A U v) (lobattoClass A U v (e t)) := by
  funext i
  by_cases eq : r i=t
  · have point : coordinate (K:=K) t (r i)=1 := by
      rw [eq]
      simp only [coordinate,Pi.single_eq_same]
    simp only [point,labelIndicator,ite_eq_left ((fibres i t).mp eq)]
  · have ne : lobattoClass A U v i≠lobattoClass A U v (e t) :=
      fun h=>eq ((fibres i t).mpr h)
    have point : coordinate (K:=K) t (r i)=0 :=
      @Pi.single_eq_of_ne (Fin 18) (fun _=>K) _ (Classical.decEq _) t (r i) eq 1
    simp only [point,labelIndicator,ite_eq_right ne]

private theorem fold_eval_on_label
    (fibres : ∀ i t,r i=t ↔ lobattoClass A U v i=lobattoClass A U v (e t))
    (x : Fin 19→K) (t : Fin 18) :
    foldLinear r x t=row x (labelIndicator (lobattoClass A U v) (lobattoClass A U v (e t))) := by
  change folded r x t=_
  rw [←row_coordinate (folded r x) t,folded_pair,lift_coordinate_eq_label fibres t]

private theorem early_head_covector_paid (S : LobattoCleanHead A b 2 U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    (fun i=>b i*v i)∈primitiveBack A b 3 := by
  let τ : Fin 19→K := fun i=>b i*v i
  have paid : τ∈annih (treeSpace A 8) := by
    apply mem_annih.mpr
    intro z hz
    have prod : v*z∈zeroSpace A 12 :=
      zeroSpace_mul_treeSpace ho (m:=4) (n:=8) (by decide) S.headFour hz
    have test : probe A b 0 (v*z)=0 :=
      LinearMap.mem_ker.mp (probe_zeroSpace (j:=12) (k:=0) ho (by decide) prod)
    simpa only [τ,probe,pow_zero,mul_one,row_apply,dotProduct,Pi.mul_apply,mul_assoc] using test
  have ranks := (marked_staircase_ranks13 ha ho S.original.head S.original.seed).1
  have eq := (exact_marked_reverse13 ha ho S.original.head.paidRanks.lastActive
    S.original.seed (by decide : 8≤11) (ranks 8 (by decide) (by decide))).1
  rw [S.original.degree_six_tree_eq_marked ha ho (by decide : 7≤8)] at eq
  change primitiveBack A b 3=annih (treeSpace A 8) at eq
  exact eq.symm ▸ paid

private theorem fold_multiplier (x : Fin 19→K) (f : Fin 18→K) (t : Fin 18) :
    foldLinear r (fun i=>x i*f (r i)) t=foldLinear r x t*f t := by
  change (∑ i∈Finset.univ.filter (fun i=>r i=t),x i*f (r i))=
    (∑ i∈Finset.univ.filter (fun i=>r i=t),x i)*f t
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem LobattoSquareSection.impossible_of_high_delta
    (L : LobattoSquareSection A b U w v G P R Q)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (top : (G-R*Q).coeff 8≠0) : False := by
  let f := lobattoClass A U v
  have seed := L.head.original.seed
  obtain ⟨count,p14,full⟩ := L.class_geometry ha ho top
  have masks (t : Fin 19) : (fun i=>if f i=f t then (1:K) else 0)∈markedTreeSpace A b 10 := by
    rw [L.head.original.degree_six_tree_eq_marked ha ho (by decide : 7≤10),full]
    apply (label_orbit_one_iff f _).mpr
    intro i j eq
    rw [eq]
  have clock (i j : Fin 19) (eq : f i=f j) :
      reflectedClock A i=reflectedClock A j := by
    have same := (L.head.class_reads eq).1
    simp only [reflectedClock,Pi.sub_apply,Pi.one_apply,same]
  obtain ⟨e,r,m,pair,fibres,cy,live,off,tail,lifts⟩ :=
    actual_pair_of_marked_labels ha ho seed f count clock masks
  obtain ⟨dmem,cover⟩ :=
    covers_of_marked_staircase pair ha ho seed L.head.original.head cy live off tail lifts
  let D := rowDelta A e r m
  let ρ := reflectedStageRow A b 1
  let ell := foldLinear r D
  let β := foldLinear r b
  let y : Fin 18→K := fun t=>reflectedClock A (e t)
  let lift (t : Fin 18) : Fin 19→K := labelIndicator f (f (e t))
  have dP : D∈annih (treeSpace A 9) := primitiveBack_annih ho 9 2 (by decide) dmem
  have ranks := (marked_staircase_ranks13 ha ho L.head.original.head seed).1
  have eq₂ := (exact_marked_reverse13 ha ho L.head.original.head.paidRanks.lastActive
    seed (by decide : 9≤11) (ranks 9 (by decide) (by decide))).1
  rw [L.head.original.degree_six_tree_eq_marked ha ho (by decide : 7≤9)] at eq₂
  change primitiveBack A b 2=annih (treeSpace A 9) at eq₂
  have foldD (t : Fin 18) : ell t=row D (lift t) :=
    fold_eval_on_label fibres D t
  have foldB (t : Fin 18) : β t=row b (lift t) :=
    fold_eval_on_label fibres b t
  have foldρ (t : Fin 18) : foldLinear r ρ t=0 := fold_first_paid ha ho seed lifts t
  have ell_support (t : Fin 18) (tL : e t≠Fin.last 18) (dead : ¬LiveCore.live U (e t)) :
      ell t≠0 := by
    intro z
    apply L.regular_selector_not_nine ha ho top p14 tL dead
    change lift t∈treeSpace A 9
    rw [←annih_annih (treeSpace A 9)]
    apply mem_annih.mpr
    intro x hx
    have inTwo : x∈primitiveBack A b 2 := eq₂.symm ▸ hx
    obtain ⟨a,p,form⟩ := cover.second x inTwo
    have repr : x=a • ρ+p • D := by
      funext i
      change x i = a * reflectedStageRow A b 1 i + p * rowDelta A e r m i
      have fi := form i
      rw [mul_comm (rowDelta A e r m i) p] at fi
      exact fi
    have ff : foldLinear r x t=0 := by
      have zD : foldLinear r D t=0 := z
      simp only [repr,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        foldρ,zD,mul_zero,add_zero]
    calc
      row (lift t) x = row x (lift t) := by
        simpa only [row_apply] using dotProduct_comm (lift t) x
      _ = 0 := (fold_eval_on_label fibres x t).symm.trans ff
  have ell_core (t : Fin 18) (lt : ell t≠0) : ¬LiveCore.live U (e t) := by
    intro live
    have u := L.head.core_selector ha ho live
    have E : lift t∈treeSpace A 9 := zeroSpace_le_treeSpace A 9
      (zeroSpace_mono A (by decide : 4≤9) (L.head.coreFour u))
    exact lt ((foldD t).trans (mem_annih.mp dP _ E))
  have lastY : reflectedClock A (Fin.last 18)=0 := by
    change 1-nodes A (Fin.last 18)=0
    rw [L.head.original.head.paidRanks.lastActive.node_eq_one ha seed,sub_self]
  have mass (t : Fin 18) (zero : ell t=0) : β t*y t=0 := by
    by_cases tL : e t=Fin.last 18
    · change β t*reflectedClock A (e t)=0
      rw [tL,lastY,mul_zero]
    · by_cases lt : LiveCore.live U (e t)
      · have pay : lift t∈zeroSpace A 4 := L.head.coreFour (L.head.core_selector ha ho lt)
        have test : probe A b 0 (lift t)=0 :=
          LinearMap.mem_ker.mp (probe_zeroSpace (j:=4) (k:=0) ho (by decide) pay)
        have mass0 : row b (lift t)=0 := by
          simpa only [probe,pow_zero,mul_one] using test
        rw [(foldB t).trans mass0,zero_mul]
      · exact (ell_support t tL lt zero).elim
  have loc (i : Fin 19) : f i=f (e (r i)) := (fibres i (r i)).mp rfl
  have supportCard : 3≤(unionSupport β y ell).card := by
    have rep : lobattoRegularPairs A U v ⊆
        (unionSupport β y ell).image (fun t=>headPair A v (e t)) := by
      intro p hp
      obtain ⟨i,iL,di,rfl⟩ := mem_lobattoRegularPairs.mp hp
      have cls : lobattoClass A U v i=lobattoClass A U v (e (r i)) := loc i
      have keep := (lobatto_class_not_last_iff (A:=A) (U:=U) (v:=v) iL).mp cls
      have dark : ¬LiveCore.live U (e (r i)) := by
        intro h
        have clash := keep.2
        simp [phaseLabel,di,h] at clash
      refine Finset.mem_image.mpr ⟨r i,?_,?_⟩
      · exact mem_unionSupport.mpr (Or.inl (ell_support (r i) keep.1 dark))
      · exact ((lobatto_class_regular_iff iL keep.1 di dark).mp cls).symm
    have bound : (lobattoRegularPairs A U v).card≤(unionSupport β y ell).card :=
      (Finset.card_le_card rep).trans Finset.card_image_le
    rw [p14] at bound
    omega
  have ampRow (i : Fin 19) : v i=v (e (r i)) := (L.head.class_reads (loc i)).2.1
  have affine : ∃ q s : K, ∀ t, β t*v (e t)=ell t*(q+s*y t) := by
    let τ : Fin 19→K := fun i=>b i*v i
    obtain ⟨a,q,s,fit⟩ := cover.third τ (early_head_covector_paid L.head ha ho)
    have tau1 : τ=(fun i=>b i*v (e (r i))) := by
      funext i
      exact congrArg (fun z=>b i*z) (ampRow i)
    have tau2 : τ=a • ρ+(fun i=>D i*(q+s*y (r i))) := by
      funext i
      change τ i=a*ρ i+D i*(q+s*reflectedClock A (e (r i)))
      rw [cy i]
      exact fit i
    refine ⟨q,s,fun t=>?_⟩
    have lhs : foldLinear r τ t=β t*v (e t) := by
      rw [tau1]
      exact fold_multiplier b (fun j=>v (e j)) t
    rw [←lhs,tau2,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,foldρ,mul_zero,zero_add]
    exact fold_multiplier D (fun j=>q+s*y j) t
  have ratios : DistinguishedRatios β y ell := by
    intro i j ne ni nj yc yn fne feq
    obtain ⟨q,s,law⟩ := affine
    have temp (t : Fin 18) (nz : ell t≠0) :
        (β t*y t/ell t)*v (e t)=(q+s*y t)*y t := by
      have h := law t
      calc
        _ = (β t*v (e t))/ell t*y t := by ring
        _ = (ell t*(q+s*y t))/ell t*y t := by rw [h]
        _ = _ := by rw [mul_div_cancel_left₀ _ nz]
    have amp : v (e i)=v (e j) := by
      apply mul_left_cancel₀ fne
      calc
        _ = (q+s*y i)*y i := temp i ni
        _ = (q+s*y j)*y j := by rw [yc]
        _ = (β j*y j/ell j)*v (e j) := (temp j nj).symm
        _ = (β i*y i/ell i)*v (e j) := by rw [feq]
    have ynj : y j≠0 := fun zero=>yn (yc.trans zero)
    have read : (1:K)-nodes A (e i)=1-nodes A (e j) := yc
    have sameC : nodes A (e i)=nodes A (e j) := by
      linear_combination -read
    have before (t : Fin 18) (nz : y t≠0) : e t≠Fin.last 18 := by
      intro tl
      apply nz
      change reflectedClock A (e t)=0
      rw [tl,lastY]
    have sameP : headPair A v (e i)=headPair A v (e j) := Prod.ext sameC amp
    have eq := (lobatto_class_regular_iff (before i yn) (before j ynj)
      (ell_core i ni) (ell_core j nj)).mpr sameP
    exact ne (((fibres (e i) i).mpr rfl).symm.trans ((fibres (e i) j).mpr eq))
  exact impossible_of_original pair ha ho seed cy live off tail lifts dmem cover supportCard mass ratios

/-- All r=2 and r=3 native charts in the degree-six marked fork close.
No square purity or rank-seven F7 premise is added. -/
theorem NativeMarkedEscapeChart.degree_six_impossible_of_cut {rad : ℕ}
    (H : NativeMarkedEscapeChart A b 5 G rad U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (cut : LobattoPureFirstCut K) : False := by
  obtain ⟨_,rr,_⟩ := H.first_grades_of_degree_six ha ho
  obtain ⟨v,S⟩ := H.clean_lobatto_head ha ho
  rcases rr with h2|h3
  · have S2 : LobattoCleanHead A b 2 U w v G := h2 ▸ S
    obtain ⟨P,R,Q,F⟩ := S2.radius_two_square_section ha ho
    by_cases low : (G-R*Q).coeff 8=0
    · exact F.impossible_of_low_delta ha ho cut low
    · exact F.impossible_of_high_delta ha ho low
  · have S3 : LobattoCleanHead A b 3 U w v G := h3 ▸ S
    exact S3.radius_three_impossible ha ho cut

/-- Dispatch directly from the paid first escape on the original rows. -/
theorem no_marked_first_escape_degree_six_of_cut {rad : ℕ}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (paid : NativePaidHead A b rad U w) (first : FirstEscape A b 5 G)
    (cut : LobattoPureFirstCut K) : False :=
  (native_marked_escape_chart ha ho seed paid first).degree_six_impossible_of_cut ha ho cut

end
end RKResearch.Certified.Graded.ERK13NativeFirst

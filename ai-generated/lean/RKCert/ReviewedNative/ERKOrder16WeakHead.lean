module

public import RKCert.ReviewedNative.PaidClockCore
public import RKCert.ReviewedNative.ERKOrder16WeakFiveCensus

@[expose] public section

/-! # The ordinary weak head before the five-contrast split

The same-grade two-iterate visibility test identifies the genuine
core. If the selected head were hidden as well, the ordinary weak
strip would make every F7 vector hidden. Three incoming Hermite
directions would then force nine blind rows on top of fifteen
actual seed rows and the terminal, exceeding width 24. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

theorem width24_seed_rows_ge_fifteen (ha : ∀ i l, i≤l → A i l=0)
    (ho : HasOrder 16 A b) : 15≤(Hidden.activeRows (quadraticSeed A b)).card := by
  let : DecidableEq K := fun a b=>Classical.propDecidable (a=b)
  let S := weightedSites (reflectedClock A) (quadraticSeed A b)
  have eight : 8≤S.card := width24_quadratic_eight_sites ha ho
  by_cases many : 15≤S.card
  · exact many.trans (Finset.card_image_le
      (f:=reflectedClock A) (s:=Hidden.activeRows (quadraticSeed A b)))
  · have twice := quadratic_seed_double_rows ho (by change S.card+2≤16;omega)
    change 2*S.card≤_ at twice
    omega

/-- This uses the genuine marked-E8 cover, without any F7 shape or rank. -/
theorem width24_twice_paid_F5_le_carrier (ha : ∀ i l, i≤l → A i l=0)
    (ho : HasOrder 16 A b) :
    core (diag (nodes A)) (zeroSpace A 5) 2 ≤ width24WeakFiveCarrier A b := by
  have cover := width24_quadratic_cover ha ho
  have y0 : reflectedClock A (Fin.last 23)=0 := by
    change (1:K)-nodes A (Fin.last 23)=0
    rw [cover.frame.lastClock,sub_self]
  exact paid_clock_core_le_carrier (m:=8) (h:=5) (j:=5) (k:=2) ha ho y0 cover.lastSeed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by exact cover.sites) (fun _ h => cover.poly_cover h)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Two applications of the existing quotient-rank step pay at least
three dimensions of actual grade-five defects with both shifts paid. -/
theorem width24_two_paid_core_rank
    (five : finrank K (zeroSpace A 5)=5) (six : finrank K (zeroSpace A 6)=6) :
    3≤finrank K (core (diag (nodes A)) (zeroSpace A 5) 2) := by
  let F := zeroSpace A 5
  let D := diag (nodes A)
  have inc : F⊔F.map D≤zeroSpace A 6 := sup_le (zeroSpace_mono A (by decide))
    (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 5))
  have bound : finrank K ↥(F⊔F.map D)≤6 := (Submodule.finrank_mono inc).trans six.le
  have first := core_rank_step D F 0
  have second := core_rank_step D F 1
  change finrank K F+finrank K F≤finrank K (core D F 1)+finrank K ↥(F⊔F.map D) at first
  change finrank K (core D F 1)+finrank K F≤
    finrank K (core D F 2)+finrank K ↥(F⊔F.map D) at second
  change 3≤finrank K (core D F 2)
  have f : finrank K F=5 := five
  omega

/-- If F7 were wholly hidden, three incoming directions in the original
blind carrier, together with every rank-six defect, would pay nine
physical blind rows. The quadratic seed and terminal already use
at least sixteen other original rows. -/
theorem width24_seven_not_all_hidden (ha : ∀ i l, i≤l → A i l=0) (ho : HasOrder 16 A b)
    (six : finrank K (zeroSpace A 6)=6) :
    ¬zeroSpace A 7≤width24WeakFiveCarrier A b := by
  let : DecidableEq K := fun a b=>Classical.propDecidable (a=b)
  intro hidden
  let H := width24WeakFiveCarrier A b
  let c := nodes A
  let y := reflectedClock A
  let d := quadraticSeed A b
  let S := weightedSites y d
  let T := S.erase 1
  let V := zeroSpace A 6
  let t := Fin.last 23
  have cover := width24_quadratic_cover ha ho
  have inc : V≤H := (zeroSpace_mono A (by decide : 6≤7)).trans hidden
  have inv : H.map (diag c)≤H := Hidden.carrier_invariant cover.frame.lastClock
  have blocks : MaskInvariant c H :=
    clock_mask_invariant (fun f hf=>inv (Submodule.mem_map_of_mem hf))
  have strict : StrictlyCausal (mat A) := by
    intro i f g pre
    have h := causal_mat ha i (f-g) (fun k hk=>sub_eq_zero.mpr (pre k hk))
    simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using h
  have supply : 3≤(failedNodes c (1 : Fin 24→K) H 24).card := by
    have some : 8≤S.card := width24_quadratic_eight_sites ha ho
    have erase : S.card-1≤T.card := Finset.pred_card_le_card_erase
    have inj : Function.Injective (fun k : K=>1-k) := by
      intro a a' e
      linear_combination -e
    have sub : T.image (fun k : K=>1-k) ⊆ failedNodes c (1 : Fin 24→K) H 24 := by
      intro a ha'
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha'
      obtain ⟨ne,site⟩ := Finset.mem_erase.mp hx
      obtain ⟨i,di,yi⟩ := mem_weightedSites.mp site
      have ci : c i=1-x := by
        rw [←yi]
        change nodes A i=1-(1-nodes A i)
        ring
      refine mem_failedNodes.mpr ⟨sub_ne_zero.mpr (Ne.symm ne),?_⟩
      rintro ⟨g,hg,agree⟩
      have gi : g i=0 := Hidden.carrier_zero_on_active cover.lastSeed hg di
      have e := agree i i.isLt ci
      exact zero_ne_one (by simpa only [gi,Pi.one_apply] using e)
    rw [←Finset.card_image_of_injective T inj] at erase
    have bound := Finset.card_le_card sub
    omega
  have moves (f : Fin 24→K) (hf : f∈V) : mat A f∈H :=
    hidden (mat_zeroSpace_charZero A 6 hf)
  have eval (P : K[X]) : weightedEval c (1 : Fin 24→K) P=evalNodes A P := by
    ext i
    simp [c]
  have prim (P : K[X]) (pay : P.natDegree+1≤2*3) :
      mat A (weightedEval c (1 : Fin 24→K) P)-
        weightedEval c (1 : Fin 24→K) (formalPrimitive P)∈H := by
    rw [eval,eval,formalPrimitive_eq_native]
    exact inc (primitive_defect A P (q:=5) (by omega))
  have growth := incoming_nodal_gain c (1 : Fin 24→K) V H (mat A)
    strict blocks inc moves 3 supply prim
  change finrank K V+3≤finrank K H at growth
  have a : finrank K V=6 := six
  have n := width24_seed_rows_ge_fifteen ha ho
  have budget := Hidden.carrier_contrast_budget
    (c:=c) (b:=b) (d:=d) (o:=0) (t:=t) (w:=(0 : Fin 24→K))
    cover.frame.lastLive.live cover.lastSeed (by simp) (by simp) (by simp)
  have noContrast : (Hidden.activeRows (0 : Fin 24→K)).card=0 := by simp [Hidden.activeRows]
  rw [noContrast,add_zero] at budget
  change finrank K H+(Hidden.activeRows (quadraticSeed A b)).card+1≤24 at budget
  omega

/-- The actual nonzero two-power weak trace, before counting contrasts. -/
structure Width24OrdinaryWeakHead (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24→K)
    (U : Submodule K (Fin 24→K)) (w : Fin 24→K) (Q P : K[X]) : Prop where
  flat : FlatClockHead A 5 2 2 U w
  coreInside : U≤width24WeakFiveCarrier A b
  visible : w∉width24WeakFiveCarrier A b
  qNonzero : Q≠0
  qDegree : Q.natDegree≤4
  pDegree : P.natDegree≤3
  qFit : ∀ i,quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i
  pFit : ∀ i,reflectedClock A i*b i*w i=P.eval (reflectedClock A i)*quadraticSeed A b i

/-- Native weak head and two physical trace fits, derived unconditionally
on ordinary F7 rank seven. This uses no five-contrast assumption. -/
theorem width24_ordinary_weak_head (ha : ∀ i l, i≤l → A i l=0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7)=7) :
    ∃ (U : Submodule K (Fin 24→K)) (w : Fin 24→K) (Q P : K[X]),
      Width24OrdinaryWeakHead A b U w Q P := by
  let D := diag (nodes A)
  let F := zeroSpace A
  let H := width24WeakFiveCarrier A b
  have sep := coeff_separated ho (q:=7) (by decide)
  have f5lo : 5≤finrank K (F 5) :=
    grade_five_surplus_of_reviewed_order ha ho (by decide : 10≤16)
  have seven' : finrank K (F 7)=7 := seven
  have step5 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j:=5) (by decide) (by decide))
  have step6 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j:=6) (by decide) (by decide))
  change finrank K (F 5)<finrank K (F 6) at step5
  change finrank K (F 6)<finrank K (F 7) at step6
  have five : finrank K (F 5)=5 := by omega
  have six : finrank K (F 6)=6 := by omega
  obtain ⟨r,U,w,L⟩ := flat_clock_head ha (j:=5) (d:=2) sep
    (by decide) (by decide) (by change finrank K (F 7)≤finrank K (F 5)+2;omega)
  have invisible := width24_twice_paid_F5_le_carrier ha ho
  have Uin : U≤H := (invariant_le_core L.coreInside L.coreStable 2).trans invisible
  have ps : PolySeparated A 7 := PolySeparated.of_coeff sep
  have debit := clock_invariant_outgoing ha (ps.mono (by decide : 5≤7))
    L.coreInside L.coreStable
  change finrank K U+3≤finrank K (F 6) at debit
  have dim : finrank K (F 5)=finrank K U+r := L.baseRank
  have two : 2≤r := by omega
  have cover := width24_quadratic_cover ha ho
  have inv : H.map D≤H := Hidden.carrier_invariant cover.frame.lastClock
  have wHidden : w∉H := by
    intro hw
    have powers (k : ℕ) : (D^k) w∈H := by
      induction k with
      | zero => simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using hw
      | succ k ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
        exact inv (Submodule.mem_map_of_mem ih)
    have final : F 7≤H := by
      rw [show F 7=chain D U w (r+2) from L.flags 2 le_rfl]
      exact (clock_chain_le_iff _).mpr ⟨Uin,fun k _=>powers k⟩
    exact width24_seven_not_all_hidden ha ho six final
  have paid (k : ℕ) (hk : k<r) : (D^k) w∈F 5 := by
    rw [show F 5=chain D U w r from L.flags 0 (by decide)]
    exact ((clock_chain_le_iff r).mp le_rfl).2 k hk
  have r2 : r=2 := by
    by_contra ne
    exact wHidden (invisible (mem_core.mpr (fun k hk=>paid k (by omega))))
  subst r
  have wz : w∈F 5 := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using paid 0 (by decide)
  have dw : D w∈F 5 := by simpa only [pow_one] using paid 1 (by decide)
  obtain ⟨Q,P,qd,pd,qfit,pfit⟩ := cover.two_power_traces ho wz dw
  have qn : Q≠0 := by
    intro z
    have seed (i : Fin 24) : quadraticSeed A b i*w i=0 := by
      simpa only [z,eval_zero,zero_mul] using qfit i
    have other (i : Fin 24) : ((1-nodes A i)*b i)*w i=0 := by
      change reflectedClock A i*b i*w i=0
      by_cases d : quadraticSeed A b i=0
      · simpa only [d,mul_zero] using pfit i
      · rw [(mul_eq_zero.mp (seed i)).resolve_left d,mul_zero]
    exact wHidden (Hidden.actual_defect_hidden ha ho (by decide : 5+1≤16) wz seed other)
  exact ⟨U,w,Q,P,⟨L,Uin,wHidden,qn,qd,pd,qfit,pfit⟩⟩

/-- Selecting the five-contrast branch now makes the existing census
produce the true source mask and both original-row interior ports. -/
theorem width24_weak_five_ports_of_ordinary_head
    (ha : ∀ i l, i≤l → A i l=0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7)=7)
    {U : Submodule K (Fin 24→K)} {w : Fin 24→K} {Q P : K[X]}
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (five : 5≤(weightedSites (reflectedClock A) (reverseContrast A b Q P)).card) :
    ∃ (q : K[X]) (ι : Fin 5 → Fin 24) (Z : K[X]), q≠0 ∧ WeakFiveInnerPorts A b q Q P Z ι := by
  have C := (width24_weak_five_census ha ho seven L.flat L.coreInside five
    L.qDegree L.pDegree L.qFit L.pFit).2.2.2.2.2
  exact width24_weak_five_ports_of_chart ha ho C

end RKResearch.Certified.ERK16

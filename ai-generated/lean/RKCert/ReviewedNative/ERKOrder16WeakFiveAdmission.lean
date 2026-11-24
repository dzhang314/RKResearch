module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMask
public import RKCert.ReviewedNative.NativeClockChainPeel
public import RKCert.ReviewedNative.ForwardNodalGain

@[expose] public section

/-! # The original grade-four slot of the three-dimensional weak carrier

The chronological two-feeder pay can be avoided at exact carrier rank
three: if F4 were rank three, the outgoing gain and the chain peel
would make F4 equal the invariant carrier, and the incoming gain would
charge a second dimension in the same F3→F4 transition. This uses no
signed-weight, norm, resultant or coordinate-deletion argument. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
variable {Q P : K[X]}

private theorem chain_clock_le_next {U : Submodule K (Fin 24→K)}
    (stable : U.map (diag (nodes A))≤U) (n : ℕ) :
    (chain (diag (nodes A)) U w n).map (diag (nodes A))≤
      chain (diag (nodes A)) U w (n+1) := by
  cases n with
  | zero =>
    exact stable.trans ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mp le_rfl).1
  | succ k =>
    exact le_sup_right.trans (clock_chain_next stable (Nat.succ_pos k)).le

/-- Peel back the ordinary flag from the genuine last unpaid clock power.
No earlier flag is assumed saturated. -/
theorem weak_five_low_flag_of_strip {U : Submodule K (Fin 24→K)}
    (stable : U.map (diag (nodes A))≤U)
    (seventh : zeroSpace A 7=chain (diag (nodes A)) U w 4)
    (unpaid : (diag (nodes A)^4) w∉zeroSpace A 7) :
    zeroSpace A 3≤U ∧ zeroSpace A 4≤U⊔(K∙w) := by
  let D := diag (nodes A)
  have all (t : ℕ) (ht : t≤4) :
      (D^(4-t)) w∉chain D U w (4-t) ∧ zeroSpace A (7-t)≤chain D U w (4-t) := by
    induction t with
    | zero =>
      rw [Nat.sub_zero,Nat.sub_zero,←seventh]
      exact ⟨unpaid,le_rfl⟩
    | succ t ih =>
      have old := ih (by omega)
      let n := 4-(t+1)
      let j := 7-(t+1)
      have nn : 4-t=n+1 := by dsimp [n];omega
      have jj : 7-t=j+1 := by dsimp [j];omega
      rw [nn,jj] at old
      change (D^n) w∉chain D U w n ∧ zeroSpace A j≤chain D U w n
      refine ⟨?_,?_⟩
      · intro hp
        apply old.1
        have e : (D^(n+1)) w=D ((D^n) w) := by
          rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
        rw [e]
        exact (chain_clock_le_next stable n) (Submodule.mem_map_of_mem hp)
      · intro x hx
        exact clock_chain_drop_of_next_unpaid stable n old.1
          (old.2 (zeroSpace_mono A (Nat.le_succ _) hx)) (old.2 (diag_zeroSpace A j hx))
  exact ⟨(all 4 (by decide)).2,by
    simpa only [show 7-3=4 by decide,show 4-3=1 by decide,chain,
      pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using (all 3 (by decide)).2⟩

/-- On the ordinary weak-five strip, F4 has exactly four dimensions;
its two actual summands are the three-dimensional carrier and the head.
The contradiction at rank three uses both directed Hermite gains at
the same native F3→F4 step. -/
theorem weak_five_grade_four_of_strip [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (carrierRank : finrank K (width24WeakFiveCarrier A b)=3)
    (seventh : zeroSpace A 7=chain (diag (nodes A)) (width24WeakFiveCarrier A b) w 4)
    (unpaid : (diag (nodes A)^4) w∉zeroSpace A 7) :
    finrank K (zeroSpace A 4)=4 ∧ zeroSpace A 4=width24WeakFiveCarrier A b⊔(K∙w) := by
  let U := width24WeakFiveCarrier A b
  let G := zeroSpace A 3
  let F := zeroSpace A 4
  let D := diag (nodes A)
  have stable : U.map D≤U := Hidden.carrier_invariant (width24_paid_frame ha ho).lastClock
  obtain ⟨inside,leQuad⟩ := weak_five_low_flag_of_strip stable seventh unpaid
  have j4 := coeff_separated ho (q:=4) (by decide)
  have ps : PolySeparated A 4 := PolySeparated.of_coeff j4
  have f3 : 2≤finrank K G := zeroSpace_finrank ha ho (by decide : 2+2≤16)
  have gap : finrank K G<finrank K F := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha j4 (j:=3) (by decide) (by decide))
  have r : finrank K U=3 := carrierRank
  have supCap : finrank K ↥(U⊔(K∙w))≤4 := by
    have e := Submodule.finrank_sup_add_finrank_inf_eq U (K∙w)
    have one : finrank K ↥(K∙w)≤1 := by
      by_cases z : w=0
      · rw [Submodule.span_singleton_eq_bot.mpr z,finrank_bot];decide
      · rw [finrank_span_singleton z]
    omega
  have cap : finrank K F≤4 := (Submodule.finrank_mono leQuad).trans supCap
  have four : finrank K F=4 := by
    by_contra ne
    have lower : finrank K G=2 := by omega
    have small : finrank K F=3 := by omega
    have esc : ¬G.map D≤G := by
      intro h
      have rise := clock_invariant_outgoing ha (ps.mono (by decide : 3≤4))
        (U:=G) le_rfl h
      change finrank K G+2≤finrank K F at rise
      omega
    have step : F=G⊔G.map D := zeroSpace_clock_step_of_unit
      (n:=3) (by change finrank K F≤finrank K G+1;omega) esc
    have inc : F≤U := step.symm ▸ sup_le inside ((Submodule.map_mono inside).trans stable)
    have eq : F=U := Submodule.eq_of_le_of_finrank_le inc (by change finrank K U≤finrank K F; omega)
    have stableF : F.map D≤F := eq.symm ▸ stable
    have rise := clock_invariant_incoming ha (j:=3) ps stableF
    change finrank K G+2≤finrank K F at rise
    omega
  refine ⟨four,Submodule.eq_of_le_of_finrank_le leQuad ?_⟩
  change finrank K ↥(U⊔(K∙w))≤finrank K F
  omega

/-- Assemble the proved mask chart without assuming either grade-four
admission. The degree, trace, ordinary F7 strip, and exact census
premises remain separately visible. -/
theorem width24_weak_five_chart_of_strip [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (carrierRank : finrank K (width24WeakFiveCarrier A b)=3)
    (seventh : zeroSpace A 7=chain (diag (nodes A)) (width24WeakFiveCarrier A b) w 4)
    (unpaid : (diag (nodes A)^4) w∉zeroSpace A 7)
    (seedSites : 15≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card)
    (contrastSites : 5≤(weightedSites (reflectedClock A) (reverseContrast A b Q P)).card)
    (qd : Q.natDegree≤4) (pd : P.natDegree≤3)
    (qFit : ∀ i, quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pFit : ∀ i, reflectedClock A i*b i*w i=P.eval (reflectedClock A i)*quadraticSeed A b i) :
    Width24WeakFiveChart A b w Q P := by
  obtain ⟨_,shape⟩ := weak_five_grade_four_of_strip ha ho carrierRank seventh unpaid
  have cw : w∈width24WeakFiveCarrier A b⊔(K∙w) :=
    (le_sup_right : K∙w≤width24WeakFiveCarrier A b⊔(K∙w)) (Submodule.mem_span_singleton_self _)
  exact ⟨carrierRank,le_sup_left.trans shape.ge,shape.ge cw,
    seventh,seedSites,contrastSites,qd,pd,qFit,pFit⟩

end
end RKResearch.Certified.ERK16

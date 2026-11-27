module

public import RKCert.ReviewedNative.ERK8FourOffPaidGenericGuards
public import RKCert.ReviewedNative.ERK8FourOffPaidExceptionalCharts
public import RKCert.ReviewedNative.ERK8FourOffPaidLinearClosure

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The full literal paid four-off exclusion outside characteristic eleven -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof OneOff ERKTaggedHorizon ERK8PaidField FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical Matrix

variable {K : Type*} [Field K]

theorem outside11_chart_result [EightUnits K] {u : K} (q : sevenQuad u=0)
    (h11 : (11:K)≠0) (o : CleanOrientation) : ChartResult o u := by
  by_cases p17 : (17:K)=0
  · exact chart_tests_mod_17 q p17 o
  by_cases p37 : (37:K)=0
  · exact chart_tests_mod_37 q p37 o
  by_cases p41 : (41:K)=0
  · exact chart_tests_mod_41 q p41 o
  by_cases p43 : (43:K)=0
  · exact chart_tests_mod_43 q p43 o
  by_cases p79 : (79:K)=0
  · exact chart_tests_mod_79 q p79 o
  exact ChartResult.quadratic (generic_chart_tests q ⟨h11,p17,p37,p41,p43,p79⟩ o)

variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem no_four_off_paid_outside11
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)≠0) :
    (OneOff.offKnots A).card≠4 := by
  intro off
  let : EightUnits K := eightUnits_of_order ho
  obtain ⟨P,R,dup,k,theta,kap,M,L,T,N⟩ := actual_raw_head_of_order8_four_off ha ho off
  obtain ⟨o,u,q,hh,xx,zz⟩ := paid_clean_orientation L.roots
  have D : CleanClocks (chartH o u) (chartX o u) (chartZ o u) := by
    simpa only [hh,xx,zz] using L.roots
  have raw : RawPaidShape P (chartH o u) (chartX o u) (chartZ o u) theta kap := by
    simpa only [hh,xx,zz] using N
  have S := scaled_actual_head_outside11 p q M.rankData.headNonzero raw
  have d := M.rankData.headDegree
  let actual := cleanSites (nodes A k) (nodes A 6) (nodes A 7)
  let canonical := cleanSites u (midClock K) (1-u)
  have can : actual=canonical := by dsimp only [actual,canonical]; rw [hh,xx,zz,cleanSites_chart_eq]
  have cardA : actual.card=4 := cleanSites_card L.roots
  have term : CleanTerminalProfile A (nodalHull actual) R := (cleanSites_hull L.roots).symm ▸ T
  have r := outside11_chart_result q p o
  let Q := chartQuadratic o u
  have noShared (dj : Q.p2≠0) (u₀ : K) (mem : u₀∈canonical) (q0 : Q.eval u₀=0)
      (others : ∀ t∈canonical,t≠u₀→Q.eval t≠0) : False := by
    have e := S.degree_two d dj
    apply no_paid_single_shared_root M cardA term e (can.symm ▸ mem) ((S.eval_zero_iff d u₀).mpr q0)
    intro x h hx zero
    exact others x (can ▸ h) hx ((S.eval_zero_iff d x).mp zero)
  have originNZ (p0 : Q.p0≠0) : Q.eval 0≠0 := by simpa [Quad.eval] using p0
  rcases r with nq|nl|⟨pd,p0,a,b,c⟩|⟨pd,p0,b,a,c⟩|⟨pd,p0,c,a,b⟩
  · have recpt := native_quadratic_receipt_of_chart_tests S d q D nq
    exact no_actual_paid_four_off_quadratic ha ho M L T (by rwa [hh,xx,zz])
  · have p1 := S.degree_one d nl.p2 nl.p1
    have n := clean_eval_ne_of_caps S d nl.caps
    have four := native_four_gate_of_chart_test S d q D nl.caps nl.four
    exact no_actual_paid_four_off_linear ha ho M L T p1 (by rwa [hh,xx,zz]) (by rwa [hh,xx,zz])
  · apply noShared pd u (by simp [canonical,cleanSites]) a
    intro x hx xn
    simp only [canonical,cleanSites,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with e|e|e|e
    · rw [e]; exact originNZ p0
    · exact (xn e).elim
    · rw [e]; exact c
    · rw [e]; exact b
  · apply noShared pd (1-u) (by simp [canonical,cleanSites]) b
    intro x hx xn
    simp only [canonical,cleanSites,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with e|e|e|e
    · rw [e]; exact originNZ p0
    · rw [e]; exact a
    · rw [e]; exact c
    · exact (xn e).elim
  · apply noShared pd (midClock K) (by simp [canonical,cleanSites]) c
    intro x hx xn
    simp only [canonical,cleanSites,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with e|e|e|e
    · rw [e]; exact originNZ p0
    · rw [e]; exact a
    · exact (xn e).elim
    · rw [e]; exact b

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.no_four_off_paid_outside11

module

public import RKCert.ReviewedNative.ERKGradeEightSurplus
public import RKCert.ReviewedNative.ERK17ReverseSupport
public import RKCert.ReviewedNative.ReverseUnitQuadratic

@[expose] public section

/-! # Exact native zero-first-seed cover at width twenty-six -/
namespace RKResearch.Certified.ERK17
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

structure Width26QuadraticCover (A : Matrix (Fin 26) (Fin 26) K) (b : Fin 26→K) : Prop where
  lastLive : LastActive b (Fin.last 25)
  lastClock : nodes A (Fin.last 25)=1
  lastSeed : quadraticSeed A b (Fin.last 25)=0
  terminalOut : coordinate (K:=K) (Fin.last 25)∉treeSpace A 8
  sites : 8≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card
  band : zeroAt (annih (treeSpace A 8)) (Fin.last 25)=
    weightedBand (reflectedClock A) (quadraticSeed A b) 7

/-- A true reverse annihilator with the terminal physical site deleted is
represented by a coefficient polynomial of degree at most six. -/
theorem Width26QuadraticCover.poly_cover (C : Width26QuadraticCover A b) {v : Fin 26→K}
    (h : v∈annih (treeSpace A 8)) (tail : v (Fin.last 25)=0) :
    ∃ P : K[X], P.natDegree≤6 ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v := by
  have m : v∈zeroAt (annih (treeSpace A 8)) (Fin.last 25) := mem_zeroAt.mpr ⟨h,tail⟩
  rw [C.band] at m
  obtain ⟨P,hP,hv⟩ := mem_weightedBand.mp m
  refine ⟨P,?_,hv⟩
  by_cases zero : P=0
  · simp [zero]
  · have lt : P.natDegree<7 := (natDegree_lt_iff_degree_lt zero).mpr hP
    omega

set_option maxHeartbeats 600000 in
theorem width26_quadratic_cover_of_frame [CharZero K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b) (F : OddBalancedFrame A b 8 2)
    (last : LastActive b (Fin.last 25)) (z : firstSeed A b=0) : Width26QuadraticCover A b := by
  have short : UnitQuadratic.UnitFrame A b := by
    refine ⟨z,?_,fun n lo hi => width26_reverse_clock_escape ha ho F lo (by omega)⟩
    intro n hn
    obtain ⟨r,e⟩ := F.reverse.flagExact n (by omega)
    rw [first_dim_zero z,add_zero] at r
    exact ⟨r,e⟩
  have two := UnitQuadratic.quadratic_sites_ge_two ha ho (by decide) short
  obtain ⟨sites,t,live,one,d0,band⟩ := width26_quadratic_wide_of_two_sites ha ho F z two
  obtain ⟨u,lu,_,out,_⟩ := F.reverse.firstZero z
  have atLast (i : Fin 26) (L : LastActive b i) : i=Fin.last 25 := by
    apply le_antisymm (Fin.le_last i)
    exact not_lt.mp (fun h => last.live (L.after _ h))
  rw [atLast t live] at one d0 band
  rw [atLast u lu] at out
  exact ⟨last,one,d0,out,sites,band⟩

/-- No support-size premise and no rank hypothesis are needed in the
actual ordered zero-first-seed case. -/
theorem ordered_width26_quadratic_cover [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b) (z : firstSeed A b=0) :
    Width26QuadraticCover A b := by
  obtain ⟨F,last⟩ := ordered_width26_full_frame ha ho
  exact width26_quadratic_cover_of_frame ha ho F last z

end RKResearch.Certified.ERK17

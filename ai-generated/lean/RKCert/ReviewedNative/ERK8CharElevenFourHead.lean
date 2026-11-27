module

public import RKCert.ReviewedNative.ERK8CharElevenOmittedHead
public import RKCert.ReviewedNative.ERK8PaidPhysicalBridge

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual exceptional first-clock split in the physical four-off chart
Over characteristic eleven the generic raw head identity has a truly
degenerate case. Its other orientations are explicitly retained here. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon FourOffPhysical ERK8PaidField
open RKResearch.Certified.Graded.FourOffNewton
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem clean_center_or_quadratic (p : (11:K)=0) {t : K} (l : lobattoNumer t=0) :
    t=6 ∨ (exceptionalQuadratic : K[X]).eval t=0 := by
  unfold lobattoNumer at l
  rcases mul_eq_zero.mp l with h|h
  · left
    linear_combination 6*h-t*p
  · right
    rw [exceptionalQuadratic_eval]
    linear_combination 8*h-5*(t^2-t)*p

theorem clean_pair_of_center (p : (11:K)=0) {x z : K}
    (D : CleanClocks 6 x z) : x+z=1 ∧ x*z=8 := by
  have hx := (clean_center_or_quadratic p D.root_x).resolve_left D.h_ne_x.symm
  have hz := (clean_center_or_quadratic p D.root_z).resolve_left D.h_ne_z.symm
  rw [exceptionalQuadratic_eval] at hx hz
  have prod : (x-z)*(x+z-1)=0 := by linear_combination hx-hz
  have s := sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr D.x_ne_z))
  exact ⟨s,by linear_combination x*s-hx⟩

/-- Vanishing of the shape correction is a consequence of the actual
first-clock geometry, not a restriction to a symmetric template. -/
theorem centered_raw_is_exceptional (p : (11:K)=0) {P : K[X]} {x z theta k : K}
    (D : CleanClocks 6 x z) (N : RawPaidShape P 6 x z theta k) (nz : P≠0) :
    k=0 ∧ theta≠0 ∧ P=C theta*exceptionalQuadratic ∧ x+z=1 ∧ x*z=8 := by
  obtain ⟨s,m⟩ := clean_pair_of_center p D
  have hE : cleanE (6:K) x z=0 := by
    unfold cleanE
    linear_combination -24*s+6*m+12*p
  have k0 : k=0 := by
    have r := N.ratio
    rw [hE,mul_zero] at r
    refine (mul_eq_zero.mp r.symm).resolve_right ?_
    intro hh
    unfold cleanNumer at hh
    have xx : x+1=0 := by linear_combination 6*hh-(13*x-59)*p
    have e : x=-1 := by linear_combination xx
    have root := (clean_center_or_quadratic p D.root_x).resolve_left D.h_ne_x.symm
    rw [exceptionalQuadratic_eval,e] at root
    exact one_ne_zero (by linear_combination -root+p : (1:K)=0)
  have cp : cleanPair x z=(exceptionalQuadratic : K[X]) := by
    unfold cleanPair exceptionalQuadratic
    calc
      (X-C x)*(X-C z) = X^2-C (x+z)*X+C (x*z) := by
        simp only [map_add,map_mul]
        ring
      _ = _ := by rw [s,m,map_one,one_mul]
  have ph := N.identity
  rw [cp,k0,map_zero,zero_mul,add_zero] at ph
  refine ⟨k0,?_,ph,s,m⟩
  intro e
  exact nz (by simp [ph,e])

/-- Literal order-eight adapter for the actual physical four-off branch.
Either its first nonzero clean clock is a quadratic root, or its entire
head is the exceptional quadratic with a nonzero scale. -/
theorem order8_four_off_center_or_quadratic
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (off : (offKnots A).card=4) :
    ∃ (P R : K[X]) (dup k : Fin 10) (theta scale : K),
      Placement A b P dup k ∧
      CleanPrimitivePlacement A b k 6 (nodes A 7) ∧
      CleanTerminalProfile A (quartic (nodes A k) (nodes A 6) (nodes A 7)) R ∧
      RawPaidShape P (nodes A k) (nodes A 6) (nodes A 7) theta scale ∧
      ((nodes A k=6 ∧ scale=0 ∧ theta≠0 ∧ P=C theta*exceptionalQuadratic ∧
        nodes A 6+nodes A 7=1 ∧ nodes A 6*nodes A 7=8) ∨
        (exceptionalQuadratic : K[X]).eval (nodes A k)=0) := by
  obtain ⟨P,R,dup,k,theta,scale,M,L,T,N⟩ := actual_raw_head_of_order8_four_off ha ho off
  refine ⟨P,R,dup,k,theta,scale,M,L,T,N,?_⟩
  rcases clean_center_or_quadratic p L.roots.root_h with center|quad
  · have roots := L.roots
    have raw := N
    rw [center] at roots raw
    have H := centered_raw_is_exceptional p roots raw M.rankData.headNonzero
    exact Or.inl ⟨center,H⟩
  · exact Or.inr quad

/-- Over characteristic-eleven fields without a root of the exceptional
quadratic, the actual four- and five-off branches both disappear. The
one- and seven-off branches still require separate closures. -/
theorem order8_char11_nonsplit_count
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (noRoot : ∀ x, (exceptionalQuadratic : K[X]).eval x ≠ 0) :
    (offKnots A).card=1 ∨
      ((offKnots A).card=7 ∧ (cleanKnots A).card=3) := by
  rcases order8_count_one_four_five_seven ha ho with one|⟨four,_⟩|⟨five,cl⟩|seven
  · exact Or.inl one
  · obtain ⟨P,R,dup,k,theta,scale,M,L,T,N,shape⟩ :=
      order8_four_off_center_or_quadratic ha ho p four
    rcases shape with ⟨_,_,_,_,s,m⟩ | r
    · apply False.elim (noRoot (nodes A 6) ?_)
      rw [exceptionalQuadratic_eval]
      linear_combination (nodes A 6)*s-m
    · exact (noRoot _ r).elim
  · obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inl five)
    let S : Finset K := {0,1,6}
    have le : cleanKnots A ⊆ S := by
      intro x hx
      obtain ⟨j,gj,rfl⟩ := mem_cleanKnots.mp hx
      rcases H.clean_roots j gj with h0|h1|h6|q
      · simp [S,h0]
      · simp [S,h1]
      · simp [S,h6]
      · exact (noRoot _ q).elim
    have bound := Finset.card_le_card le
    have s3 : S.card ≤ 3 := calc
      _ ≤ ({1,6} : Finset K).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({6} : Finset K).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
    omega
  · exact Or.inr seven

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_four_off_center_or_quadratic

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_char11_nonsplit_count

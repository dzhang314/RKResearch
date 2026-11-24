module

public import RKCert.ReviewedNative.ERKOrder15OmittedKnot
import RKCert.ReviewedNative.ERKOrder15ScalarFromReplay
import RKCert.ReviewedNative.Explicit

@[expose] public section

/-! # The genuine native order-fifteen endpoint -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

/-- The two frozen algebraic exclusions close the original physical
rank-two early-terminal chart in characteristic zero. -/
theorem Order15PaidStaircase.native_terminal_impossible [CharZero K]
    (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (seed : firstSeed A b=0) (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8) : False := by
  obtain ⟨v,P,B⟩ := S.actual_terminal_divisor ha ho seed term
  obtain ⟨i,_,_,un,gu,pu,f1,f2⟩ := B.omitted_knot ha ho
  have p0 := B.origin_nonzero ha ho
  have ab := S.base_degree
  have gd := S.first.degree
  have m0 := order15_escape_origin ha S.frame G S.first.paid
  obtain ⟨D,e,_,obs⟩ := order15_escape_adjacent_packet ha ho S.frame G (by omega) S.first.paid
  have mom (k : ℕ) (hk : k≤5) :
      (formalPrimitive (X^k*G)).eval 1=(formalPrimitive (X^(k+1)*G)).eval 1 := by
    rw [e]
    exact obs ⟨k,by omega⟩
  exact RKCert.ReviewedNative.JacobiMoments.order15_marked_omission_impossible ab.1 ab.2 gd m0 mom
    B.degree B.divides p0 un pu gu f1 f2

end
end RKResearch.Certified.Graded

namespace RKResearch.Certified
open RKResearch Graded
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- A strictly lower-triangular RK method of native reviewed order
fifteen needs at least twenty-three stages over every ordered field. -/
theorem native_explicit_order_fifteen_at_least_twenty_three
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b) : 23≤s := by
  by_contra no
  cases s with
  | zero =>
    have h := explicit_order_le_stages ha ho
    omega
  | succ s =>
    obtain ⟨a,G,U,w,S,_,seed,term,_⟩ := order15_ordered_terminal_chart ha ho (by omega)
    exact S.native_terminal_impossible ha ho seed term

end RKResearch.Certified

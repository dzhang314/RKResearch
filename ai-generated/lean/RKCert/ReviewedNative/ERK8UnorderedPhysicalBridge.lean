module

public import RKCert.ReviewedNative.ERK8FourOffCleanPlacementAdapter
public import RKCert.ReviewedNative.ERK8FourOffTerminalProfile

@[expose] public section

/-! # Order-free native bridge to the four-off normalized head
This packages the literal physical localization, terminal coordinate, and
clean chronology. It does not assert the Newton equations or exclude the
one-off and four-off branches. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- A literal order-eight four-off tableau over a characteristic-zero field
determines the physical placement and the normalized quadratic head,
without an order on the coefficient field. -/
theorem actual_normalized_head_of_order8_four_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (off : (offKnots A).card=4) :
    ∃ (P R : K[X]) (dup k : Fin 10) (theta scale : K),
      Placement A b P dup k ∧
      CleanPrimitivePlacement A b k 6 (nodes A 7) ∧
      CleanTerminalProfile A (quartic (nodes A k) (nodes A 6) (nodes A 7)) R ∧
      NormalizedShape P (nodes A k) (nodes A 6) (nodes A 7) theta scale := by
  obtain ⟨P,dup,k,M,L⟩ := paired_placements_of_order8_four_off ha ho off
  have zero : (0:K)∈cleanKnots A :=
    mem_cleanKnots.mpr ⟨0,M.rankData.cleanZero,M.rankData.clockZero⟩
  have zT : (0:K)∈(cleanKnots A).erase 1 := Finset.mem_erase.mpr ⟨zero_ne_one,zero⟩
  have eq : terminalCleanHull A=quartic (nodes A k) (nodes A 6) (nodes A 7) := by
    rw [L.quartic_id,←marked_paid_clean_cubic ho M]
    unfold terminalCleanHull nodalHull
    have f := (Finset.mul_prod_erase ((cleanKnots A).erase 1)
      (fun u : K => (X:K[X])-C u) zT).symm
    simpa only [map_zero,sub_zero] using f
  obtain ⟨R,dR,_,pr⟩ := terminal_profile_of_unitNine ho M.rankData.bandFour
    M.rankData.unitNine M.rankData.cleanNine M.rankData.clockNine M.rankData.cleanCard
  rw [eq] at pr
  have T : CleanTerminalProfile A (quartic (nodes A k) (nodes A 6) (nodes A 7)) R := ⟨dR,pr⟩
  obtain ⟨theta,scale,N⟩ := clean_shape_from_actual_prefix ha ho M.rankData.bandFour
    off L M.rankData.headDegree M.rankData.headNonzero M.rankData.fit T
  exact ⟨P,R,dup,k,theta,scale,M,L,T,N⟩

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.actual_normalized_head_of_order8_four_off

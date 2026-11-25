module

public import RKCert.ReviewedNative.ERK17RadauFirstCompose
public import RKCert.ReviewedNative.WeightXEightResidueCut

@[expose] public section

/-! # Native first-Radau gate from a single finite residue root -/
namespace RKResearch.Certified.ERK17

open RKCert.ReviewedNative.WeightXEight

/-- The literal native eight-moment first-primitive gate, with no
ordered or real-field hypothesis and no archived arithmetic. -/
theorem native_radau_first_gate_of_residue {K : Type*} [Field K] [CharZero K] :
    RadauFirstGate K := by
  obtain ⟨s,v,rootV,cut⟩ := residue_chosen_root
  refine native_radau_first_of_chosen_root s rootV ?_
  intro Q N qm nm qd nd prod root
  exact cut Q N qd prod root

end RKResearch.Certified.ERK17

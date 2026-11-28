module

public import RKCert.ReviewedNative.DIRK12MidpointRealIntervalData
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Exact real existence for the named first two algebraic coordinates.
All four endpoint signs are bounded by rational kernel evaluation and
transferred through the sound ordered-field Horner theorem. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open DirectedRatBox

def xLeft : Box := ratHornerBox xCoeffs (point xBox.lo)
def xRight : Box := ratHornerBox xCoeffs (point xBox.hi)
def cubicBoxes : List Box := fCoeffs.map fun L => ratHornerBox L xBox
def cubicLeft : Box := hornerBox cubicBoxes (point fBox.lo)
def cubicRight : Box := hornerBox cubicBoxes (point fBox.hi)

set_option maxHeartbeats 0
set_option maxRecDepth 14000

theorem xBox_order : xBox.lo ≤ xBox.hi := by decide +kernel
theorem fBox_order : fBox.lo ≤ fBox.hi := by decide +kernel

theorem xLeft_pos : 0 < xLeft.lo := by decide +kernel
theorem xRight_neg : xRight.hi < 0 := by decide +kernel
theorem cubicLeft_neg : cubicLeft.hi < 0 := by decide +kernel
theorem cubicRight_pos : 0 < cubicRight.lo := by decide +kernel

noncomputable def realX (x : ℝ) : ℝ := ratHorner xCoeffs x
noncomputable def realF (x f : ℝ) : ℝ :=
  horner (fCoeffs.map fun L => ratHorner L x) f

theorem horner_continuous (L : List ℝ) : Continuous (horner L) := by
  induction L with
  | nil =>
    change Continuous (fun _ : ℝ => 0)
    exact continuous_const
  | cons a L ih =>
    change Continuous (fun x : ℝ => a+x*horner L x)
    exact continuous_const.add (continuous_id.mul ih)

theorem x_straddles : 0 < realX (xBox.lo:ℝ) ∧ realX (xBox.hi:ℝ) < 0 := by
  exact ⟨positive (rat_horner_sound (K:=ℝ) xCoeffs (enclose_point xBox.lo)) xLeft_pos,
    negative (rat_horner_sound (K:=ℝ) xCoeffs (enclose_point xBox.hi)) xRight_neg⟩

theorem f_straddles {x : ℝ} (hx : Encloses xBox x) :
    realF x (fBox.lo:ℝ) < 0 ∧ 0 < realF x (fBox.hi:ℝ) := by
  have hc := map_sound (fun L => rat_horner_sound L hx) fCoeffs
  exact ⟨negative (horner_sound hc (enclose_point fBox.lo)) cubicLeft_neg,
    positive (horner_sound hc (enclose_point fBox.hi)) cubicRight_pos⟩

theorem exists_realX : ∃ x : ℝ, Encloses xBox x ∧ realX x = 0 := by
  have ord : (xBox.lo:ℝ) ≤ xBox.hi := Rat.cast_le.mpr xBox_order
  apply intermediate_value_Icc' ord (horner_continuous _).continuousOn
  exact ⟨x_straddles.2.le,x_straddles.1.le⟩

theorem exists_realF {x : ℝ} (hx : Encloses xBox x) :
    ∃ f : ℝ, Encloses fBox f ∧ realF x f = 0 := by
  have ord : (fBox.lo:ℝ) ≤ fBox.hi := Rat.cast_le.mpr fBox_order
  apply intermediate_value_Icc ord (horner_continuous _).continuousOn
  exact ⟨(f_straddles hx).1.le,(f_straddles hx).2.le⟩

theorem exists_real_parameters :
    ∃ x f : ℝ, Encloses xBox x ∧ Encloses fBox f ∧ realX x = 0 ∧ realF x f = 0 := by
  obtain ⟨x,hx,hr⟩ := exists_realX
  obtain ⟨f,hf,hs⟩ := exists_realF hx
  exact ⟨x,f,hx,hf,hr,hs⟩

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.exists_real_parameters

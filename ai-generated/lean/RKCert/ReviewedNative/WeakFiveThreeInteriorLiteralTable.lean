module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortSemantics
public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralClosedCover
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells000
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells001
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells002
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells003
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells004
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells005
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells006
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells007
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells008
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells009
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells010
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells011
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells012
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells013
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells014
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells015
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells016
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells017
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells018
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells019
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells020
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells021
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells022
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells023
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells024
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells025
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells026
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells027
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells028
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells029
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells030
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells031
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells032
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells033
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells034
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells035
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells036
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells037
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells038
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells039
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells040
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells041
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells042
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells043
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells044
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells045
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells046
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells047
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells048
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells049
public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCells050

@[expose] public section

/-! # Native signed corners at the frozen ThreeInterior rows -/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

private theorem literalPortPackets_checked :
    literalStripPackets.all (fun q => checkPortRow q.row) = true := by
  apply flatten_all_of_groups
  simp only [literalPacketGroups,List.all_cons,List.all_nil,Bool.true_and,
    packets000_ports_checked, packets001_ports_checked, packets002_ports_checked, packets003_ports_checked,
    packets004_ports_checked, packets005_ports_checked, packets006_ports_checked, packets007_ports_checked,
    packets008_ports_checked, packets009_ports_checked, packets010_ports_checked, packets011_ports_checked,
    packets012_ports_checked, packets013_ports_checked, packets014_ports_checked, packets015_ports_checked,
    packets016_ports_checked, packets017_ports_checked, packets018_ports_checked, packets019_ports_checked,
    packets020_ports_checked, packets021_ports_checked, packets022_ports_checked, packets023_ports_checked,
    packets024_ports_checked, packets025_ports_checked, packets026_ports_checked, packets027_ports_checked,
    packets028_ports_checked, packets029_ports_checked, packets030_ports_checked, packets031_ports_checked,
    packets032_ports_checked, packets033_ports_checked, packets034_ports_checked, packets035_ports_checked,
    packets036_ports_checked, packets037_ports_checked, packets038_ports_checked, packets039_ports_checked,
    packets040_ports_checked, packets041_ports_checked, packets042_ports_checked, packets043_ports_checked,
    packets044_ports_checked, packets045_ports_checked, packets046_ports_checked, packets047_ports_checked,
    packets048_ports_checked, packets049_ports_checked, packets050_ports_checked]

/-- This is the published rational vertex family at the original closed
rows, with only the optional extra coordinate moved before roots 1,2,3. -/
def threeInteriorLiteralTable :
    ThreeInteriorFiniteTable threeInteriorLiteralRows 8 6 threeInteriorLiteralClosedSlices where
  coverage := threeInterior_literal_closed_cover
  low c w := wordPortBounds c w false
  high c w := wordPortBounds c w true
  corners := by
    intro c hc w a
    have admissible := portCell_admissible_of_strip threeInterior_literal_finite_strips hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp
      (show c ∈ literalStripPackets.map StripRowPacket.row from hc)
    have test : checkPortRow q.row = true := List.all_eq_true.mp literalPortPackets_checked q hq
    exact checkPortWord_sound admissible (List.all_eq_true.mp test w (mem_portWords w)) a

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem threeInterior_literal_ratio_receipt :
    ThreeInteriorRatioReceipt (K := K) threeInteriorLiteralTable := by
  intro c hc w s j r m cell _ _ cages
  exact actualPortArgs_mem (portCell_admissible_of_strip threeInterior_literal_finite_strips hc)
    cell cages

end RKCert.ReviewedNative.ThreeInteriorPencil

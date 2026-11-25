module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices000
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices001
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices002
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices003
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices004
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices005
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices006
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices007
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices008
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices009
public import RKCert.ReviewedNative.WeakFiveThreeInteriorClosedSlices010

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def threeInteriorLiteralClosedSlices : List GridSlice :=
  [slice000, slice001, slice002, slice003, slice004, slice005, slice006, slice007,
   slice008, slice009, slice010, slice011, slice012, slice013, slice014, slice015,
   slice016, slice017, slice018, slice019, slice020, slice021, slice022, slice023,
   slice024, slice025, slice026, slice027, slice028, slice029, slice030, slice031,
   slice032, slice033, slice034, slice035, slice036, slice037, slice038, slice039,
   slice040, slice041, slice042, slice043, slice044, slice045, slice046, slice047,
   slice048, slice049, slice050, slice051, slice052, slice053, slice054, slice055,
   slice056, slice057, slice058, slice059, slice060, slice061, slice062, slice063,
   slice064, slice065, slice066, slice067, slice068, slice069, slice070, slice071,
   slice072, slice073, slice074, slice075, slice076, slice077, slice078, slice079,
   slice080, slice081, slice082, slice083, slice084, slice085]

private theorem horizontal_accepted : checkChain 256 0
    (threeInteriorLiteralClosedSlices.map (fun s => (s.xLo,s.xHi))) = true := by
  decide +kernel

private theorem vertical_accepted : threeInteriorLiteralClosedSlices.all
    (checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64) = true := by
  simp only [threeInteriorLiteralClosedSlices, List.all_cons, List.all_nil, Bool.true_and, slice000_checked,
    slice001_checked, slice002_checked, slice003_checked, slice004_checked, slice005_checked,
    slice006_checked, slice007_checked, slice008_checked, slice009_checked, slice010_checked,
    slice011_checked, slice012_checked, slice013_checked, slice014_checked, slice015_checked,
    slice016_checked, slice017_checked, slice018_checked, slice019_checked, slice020_checked,
    slice021_checked, slice022_checked, slice023_checked, slice024_checked, slice025_checked,
    slice026_checked, slice027_checked, slice028_checked, slice029_checked, slice030_checked,
    slice031_checked, slice032_checked, slice033_checked, slice034_checked, slice035_checked,
    slice036_checked, slice037_checked, slice038_checked, slice039_checked, slice040_checked,
    slice041_checked, slice042_checked, slice043_checked, slice044_checked, slice045_checked,
    slice046_checked, slice047_checked, slice048_checked, slice049_checked, slice050_checked,
    slice051_checked, slice052_checked, slice053_checked, slice054_checked, slice055_checked,
    slice056_checked, slice057_checked, slice058_checked, slice059_checked, slice060_checked,
    slice061_checked, slice062_checked, slice063_checked, slice064_checked, slice065_checked,
    slice066_checked, slice067_checked, slice068_checked, slice069_checked, slice070_checked,
    slice071_checked, slice072_checked, slice073_checked, slice074_checked, slice075_checked,
    slice076_checked, slice077_checked, slice078_checked, slice079_checked, slice080_checked,
    slice081_checked, slice082_checked, slice083_checked, slice084_checked, slice085_checked]

theorem threeInterior_literal_closed_cover :
    checkDyadicCover 8 6 (threeInteriorLiteralRows.map RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells.ThreeInteriorCell.rect)
      threeInteriorLiteralClosedSlices = true := by
  have h : checkDyadicCover 8 6 threeInteriorLiteralRects threeInteriorLiteralClosedSlices = true := by
    change (threeInteriorLiteralRects.all (DyadicRect.validAt 8 6) &&
      (checkChain 256 0 (threeInteriorLiteralClosedSlices.map (fun s => (s.xLo,s.xHi))) &&
        threeInteriorLiteralClosedSlices.all
          (checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64))) = true
    exact Bool.and_eq_true_iff.mpr ⟨literalStripPackets_valid,
      Bool.and_eq_true_iff.mpr ⟨horizontal_accepted,vertical_accepted⟩⟩
  simpa only [literalRect_projection] using h

end RKCert.ReviewedNative.ThreeInteriorPencil

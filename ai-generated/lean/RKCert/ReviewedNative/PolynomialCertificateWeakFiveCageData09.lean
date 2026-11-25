module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row076 : CageRow :=
  ⟨⟨5, 13, 5, 21⟩, [⟨1013, 1139⟩, ⟨3372, 3550⟩, ⟨7013, 7174⟩, ⟨11817, 12035⟩, ⟨17377, 17572⟩, ⟨22956, 23093⟩, ⟨27792, 27865⟩, ⟨31222, 31246⟩]⟩

theorem row076_ok : row076.ok = true := by decide +kernel

def row077 : CageRow :=
  ⟨⟨5, 12, 4, 11⟩, [⟨977, 1173⟩, ⟨3211, 3523⟩, ⟨6713, 7014⟩, ⟨11533, 11818⟩, ⟨17162, 17378⟩, ⟨22819, 22957⟩, ⟨27722, 27793⟩, ⟨31200, 31223⟩]⟩

theorem row077_ok : row077.ok = true := by decide +kernel

def row078 : CageRow :=
  ⟨⟨5, 13, 4, 11⟩, [⟨896, 1093⟩, ⟨3174, 3441⟩, ⟨6821, 7084⟩, ⟨11702, 11974⟩, ⟨17315, 17537⟩, ⟨22926, 23074⟩, ⟨27779, 27857⟩, ⟨31218, 31243⟩]⟩

theorem row078_ok : row078.ok = true := by decide +kernel

def row079 : CageRow :=
  ⟨⟨4, 7, 4, 10⟩, [⟨865, 1105⟩, ⟨3266, 3561⟩, ⟨7083, 7332⟩, ⟨11973, 12357⟩, ⟨17536, 17924⟩, ⟨23073, 23370⟩, ⟨27856, 28023⟩, ⟨31242, 31298⟩]⟩

theorem row079_ok : row079.ok = true := by decide +kernel

def row080 : CageRow :=
  ⟨⟨4, 7, 4, 11⟩, [⟨750, 1014⟩, ⟨3117, 3373⟩, ⟨6912, 7192⟩, ⟨11860, 12246⟩, ⟨17469, 17848⟩, ⟨23038, 23324⟩, ⟨27840, 28001⟩, ⟨31238, 31292⟩]⟩

theorem row080_ok : row080.ok = true := by decide +kernel

def row081 : CageRow :=
  ⟨⟨4, 4, 3, 6⟩, [⟨871, 1461⟩, ⟨2448, 3634⟩, ⟨5663, 6426⟩, ⟨10689, 11165⟩, ⟨16559, 16866⟩, ⟨22442, 22625⟩, ⟨27533, 27623⟩, ⟨31142, 31170⟩]⟩

theorem row081_ok : row081.ok = true := by decide +kernel

def row082 : CageRow :=
  ⟨⟨5, 10, 4, 12⟩, [⟨1001, 1250⟩, ⟨2989, 3390⟩, ⟨6214, 6584⟩, ⟨11085, 11354⟩, ⟨16832, 17013⟩, ⟨22610, 22720⟩, ⟨27617, 27671⟩, ⟨31168, 31185⟩]⟩

theorem row082_ok : row082.ok = true := by decide +kernel

def row083 : CageRow :=
  ⟨⟨5, 11, 4, 12⟩, [⟨906, 1154⟩, ⟨2983, 3315⟩, ⟨6382, 6714⟩, ⟨11263, 11534⟩, ⟨16970, 17163⟩, ⟨22699, 22820⟩, ⟨27662, 27723⟩, ⟨31182, 31201⟩]⟩

theorem row083_ok : row083.ok = true := by decide +kernel

def rows09 : List CageRow := [row076, row077, row078, row079, row080, row081, row082, row083]

theorem rows09_ok : rows09.all CageRow.ok = true := by
  simp only [rows09, List.all_cons, List.all_nil, row076_ok, row077_ok, row078_ok, row079_ok, row080_ok, row081_ok, row082_ok, row083_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row060 : CageRow :=
  ⟨⟨5, 11, 4, 8⟩, [⟨1309, 1412⟩, ⟨3971, 4300⟩, ⟨7414, 7736⟩, ⟨11744, 12107⟩, ⟨17177, 17434⟩, ⟨22790, 22943⟩, ⟨27698, 27772⟩, ⟨31192, 31215⟩]⟩

theorem row060_ok : row060.ok = true := by decide +kernel

def row061 : CageRow :=
  ⟨⟨5, 10, 4, 9⟩, [⟨1324, 1438⟩, ⟨3894, 4292⟩, ⟨7021, 7415⟩, ⟨11380, 11745⟩, ⟨16948, 17178⟩, ⟨22659, 22791⟩, ⟨27636, 27699⟩, ⟨31173, 31193⟩]⟩

theorem row061_ok : row061.ok = true := by decide +kernel

def row062 : CageRow :=
  ⟨⟨5, 11, 4, 9⟩, [⟨1251, 1375⟩, ⟨3762, 4120⟩, ⟨7106, 7433⟩, ⟨11589, 11931⟩, ⟨17114, 17353⟩, ⟨22764, 22907⟩, ⟨27688, 27758⟩, ⟨31189, 31211⟩]⟩

theorem row062_ok : row062.ok = true := by decide +kernel

def row063 : CageRow :=
  ⟨⟨4, 4, 3, 5⟩, [⟨1249, 1538⟩, ⟨3389, 4518⟩, ⟨5970, 7022⟩, ⟨10763, 11381⟩, ⟨16587, 16949⟩, ⟨22454, 22660⟩, ⟨27538, 27637⟩, ⟨31143, 31174⟩]⟩

theorem row063_ok : row063.ok = true := by decide +kernel

def row064 : CageRow :=
  ⟨⟨5, 10, 4, 10⟩, [⟨1254, 1398⟩, ⟨3623, 4055⟩, ⟨6694, 7107⟩, ⟨11260, 11590⟩, ⟨16904, 17115⟩, ⟨22641, 22765⟩, ⟨27629, 27689⟩, ⟨31171, 31190⟩]⟩

theorem row064_ok : row064.ok = true := by decide +kernel

def row065 : CageRow :=
  ⟨⟨5, 11, 4, 10⟩, [⟨1172, 1325⟩, ⟨3522, 3895⟩, ⟨6825, 7172⟩, ⟨11461, 11779⟩, ⟨17059, 17281⟩, ⟨22740, 22875⟩, ⟨27679, 27746⟩, ⟨31186, 31207⟩]⟩

theorem row065_ok : row065.ok = true := by decide +kernel

def row066 : CageRow :=
  ⟨⟨5, 10, 4, 11⟩, [⟨1153, 1339⟩, ⟨3314, 3752⟩, ⟨6425, 6826⟩, ⟨11164, 11462⟩, ⟨16865, 17060⟩, ⟨22624, 22741⟩, ⟨27622, 27680⟩, ⟨31169, 31187⟩]⟩

theorem row066_ok : row066.ok = true := by decide +kernel

def row067 : CageRow :=
  ⟨⟨5, 11, 4, 11⟩, [⟨1062, 1255⟩, ⟨3257, 3624⟩, ⟨6583, 6930⟩, ⟨11353, 11647⟩, ⟨17012, 17219⟩, ⟨22719, 22846⟩, ⟨27670, 27734⟩, ⟨31184, 31204⟩]⟩

theorem row067_ok : row067.ok = true := by decide +kernel

def rows07 : List CageRow := [row060, row061, row062, row063, row064, row065, row066, row067]

theorem rows07_ok : rows07.all CageRow.ok = true := by
  simp only [rows07, List.all_cons, List.all_nil, row060_ok, row061_ok, row062_ok, row063_ok, row064_ok, row065_ok, row066_ok, row067_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

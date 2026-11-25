module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row084 : CageRow :=
  ⟨⟨5, 10, 4, 13⟩, [⟨771, 1108⟩, ⟨2627, 2998⟩, ⟨6054, 6383⟩, ⟨11020, 11264⟩, ⟨16802, 16971⟩, ⟨22596, 22700⟩, ⟨27611, 27663⟩, ⟨31166, 31183⟩]⟩

theorem row084_ok : row084.ok = true := by decide +kernel

def row085 : CageRow :=
  ⟨⟨5, 11, 4, 13⟩, [⟨686, 1002⟩, ⟨2681, 2990⟩, ⟨6220, 6527⟩, ⟨11187, 11436⟩, ⟨16933, 17114⟩, ⟨22682, 22796⟩, ⟨27655, 27713⟩, ⟨31180, 31199⟩]⟩

theorem row085_ok : row085.ok = true := by decide +kernel

def row086 : CageRow :=
  ⟨⟨4, 4, 3, 7⟩, [⟨0, 1154⟩, ⟨1892, 2628⟩, ⟨5536, 6055⟩, ⟨10642, 11021⟩, ⟨16538, 16803⟩, ⟨22432, 22597⟩, ⟨27529, 27612⟩, ⟨31141, 31167⟩]⟩

theorem row086_ok : row086.ok = true := by decide +kernel

def row087 : CageRow :=
  ⟨⟨5, 10, 4, 14⟩, [⟨439, 872⟩, ⟨2333, 2682⟩, ⟨5933, 6221⟩, ⟨10967, 11188⟩, ⟨16777, 16934⟩, ⟨22584, 22683⟩, ⟨27606, 27656⟩, ⟨31165, 31181⟩]⟩

theorem row087_ok : row087.ok = true := by decide +kernel

def row088 : CageRow :=
  ⟨⟨5, 11, 4, 14⟩, [⟨385, 772⟩, ⟨2424, 2723⟩, ⟨6090, 6368⟩, ⟨11122, 11352⟩, ⟨16900, 17070⟩, ⟨22666, 22775⟩, ⟨27649, 27704⟩, ⟨31178, 31196⟩]⟩

theorem row088_ok : row088.ok = true := by decide +kernel

def row089 : CageRow :=
  ⟨⟨5, 10, 4, 15⟩, [⟨0, 505⟩, ⟨2135, 2425⟩, ⟨5841, 6091⟩, ⟨10921, 11123⟩, ⟨16754, 16901⟩, ⟨22573, 22667⟩, ⟨27601, 27650⟩, ⟨31163, 31179⟩]⟩

theorem row089_ok : row089.ok = true := by decide +kernel

def row090 : CageRow :=
  ⟨⟨5, 11, 4, 15⟩, [⟨0, 440⟩, ⟨2233, 2498⟩, ⟨5987, 6237⟩, ⟨11067, 11279⟩, ⟨16871, 17031⟩, ⟨22652, 22755⟩, ⟨27642, 27696⟩, ⟨31176, 31194⟩]⟩

theorem row090_ok : row090.ok = true := by decide +kernel

def row091 : CageRow :=
  ⟨⟨5, 12, 4, 12⟩, [⟨821, 1063⟩, ⟨2978, 3258⟩, ⟨6526, 6822⟩, ⟨11435, 11703⟩, ⟨17113, 17316⟩, ⟨22795, 22927⟩, ⟨27712, 27780⟩, ⟨31198, 31219⟩]⟩

theorem row091_ok : row091.ok = true := by decide +kernel

def rows10 : List CageRow := [row084, row085, row086, row087, row088, row089, row090, row091]

theorem rows10_ok : rows10.all CageRow.ok = true := by
  simp only [rows10, List.all_cons, List.all_nil, row084_ok, row085_ok, row086_ok, row087_ok, row088_ok, row089_ok, row090_ok, row091_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

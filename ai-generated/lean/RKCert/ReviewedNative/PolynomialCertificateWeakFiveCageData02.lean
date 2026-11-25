module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row018 : CageRow :=
  ⟨⟨3, 1, 3, 2⟩, [⟨1586, 1716⟩, ⟨5026, 5670⟩, ⟨9006, 12225⟩, ⟨10295, 12700⟩, ⟨15419, 16922⟩, ⟨22043, 22549⟩, ⟨27361, 27570⟩, ⟨31092, 31152⟩]⟩

theorem row018_ok : row018.ok = true := by decide +kernel

def row019 : CageRow :=
  ⟨⟨4, 2, 3, 3⟩, [⟨1655, 1739⟩, ⟨5354, 6039⟩, ⟨8319, 10397⟩, ⟨8620, 10397⟩, ⟨15810, 16312⟩, ⟨22093, 22298⟩, ⟨27375, 27463⟩, ⟨31095, 31121⟩]⟩

theorem row019_ok : row019.ok = true := by decide +kernel

def row020 : CageRow :=
  ⟨⟨4, 3, 3, 3⟩, [⟨1569, 1660⟩, ⟨4881, 5404⟩, ⟨7925, 10349⟩, ⟨9154, 11702⟩, ⟨16286, 16771⟩, ⟨22290, 22514⟩, ⟨27460, 27559⟩, ⟨31120, 31149⟩]⟩

theorem row020_ok : row020.ok = true := by decide +kernel

def row021 : CageRow :=
  ⟨⟨4, 4, 3, 0⟩, [⟨1549, 1610⟩, ⟨4934, 5166⟩, ⟨9433, 10087⟩, ⟨13686, 14941⟩, ⟨17217, 18378⟩, ⟨22600, 23098⟩, ⟨27583, 27774⟩, ⟨31154, 31207⟩]⟩

theorem row021_ok : row021.ok = true := by decide +kernel

def row022 : CageRow :=
  ⟨⟨4, 5, 3, 0⟩, [⟨1484, 1562⟩, ⟨4715, 4995⟩, ⟨9028, 9671⟩, ⟨13566, 14391⟩, ⟨17838, 18691⟩, ⟨22943, 23477⟩, ⟨27730, 27963⟩, ⟨31196, 31262⟩]⟩

theorem row022_ok : row022.ok = true := by decide +kernel

def row023 : CageRow :=
  ⟨⟨3, 2, 3, 1⟩, [⟨1456, 1605⟩, ⟨4591, 5140⟩, ⟨8676, 9942⟩, ⟨12699, 13912⟩, ⟨16921, 18253⟩, ⟨22548, 23283⟩, ⟨27569, 27897⟩, ⟨31151, 31246⟩]⟩

theorem row023_ok : row023.ok = true := by decide +kernel

def row024 : CageRow :=
  ⟨⟨4, 6, 3, 0⟩, [⟨1409, 1507⟩, ⟨4488, 4806⟩, ⟨8705, 9292⟩, ⟨13492, 14078⟩, ⟨18252, 18895⟩, ⟨23282, 23809⟩, ⟨27896, 28168⟩, ⟨31245, 31329⟩]⟩

theorem row024_ok : row024.ok = true := by decide +kernel

def row025 : CageRow :=
  ⟨⟨4, 7, 3, 0⟩, [⟨1320, 1440⟩, ⟨4258, 4601⟩, ⟨8447, 8960⟩, ⟨13441, 13874⟩, ⟨18546, 19039⟩, ⟨23604, 24096⟩, ⟨28080, 28385⟩, ⟨31304, 31408⟩]⟩

theorem row025_ok : row025.ok = true := by decide +kernel

def rows02 : List CageRow := [row018, row019, row020, row021, row022, row023, row024, row025]

theorem rows02_ok : rows02.all CageRow.ok = true := by
  simp only [rows02, List.all_cons, List.all_nil, row018_ok, row019_ok, row020_ok, row021_ok, row022_ok, row023_ok, row024_ok, row025_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

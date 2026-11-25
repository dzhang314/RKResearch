module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row034 : CageRow :=
  ⟨⟨4, 6, 4, 6⟩, [⟨1276, 1416⟩, ⟨4026, 4412⟩, ⟨7850, 8226⟩, ⟨12305, 12726⟩, ⟨17527, 17990⟩, ⟨22982, 23308⟩, ⟨27787, 27957⟩, ⟨31218, 31271⟩]⟩

theorem row034_ok : row034.ok = true := by decide +kernel

def row035 : CageRow :=
  ⟨⟨5, 12, 4, 7⟩, [⟨1293, 1389⟩, ⟨4010, 4293⟩, ⟨7675, 7970⟩, ⟨12106, 12440⟩, ⟨17433, 17710⟩, ⟨22942, 23116⟩, ⟨27771, 27858⟩, ⟨31214, 31241⟩]⟩

theorem row035_ok : row035.ok = true := by decide +kernel

def row036 : CageRow :=
  ⟨⟨5, 13, 4, 7⟩, [⟨1231, 1334⟩, ⟨3888, 4154⟩, ⟨7654, 7905⟩, ⟨12257, 12552⟩, ⟨17610, 17880⟩, ⟨23069, 23252⟩, ⟨27838, 27933⟩, ⟨31235, 31265⟩]⟩

theorem row036_ok : row036.ok = true := by decide +kernel

def row037 : CageRow :=
  ⟨⟨4, 7, 4, 6⟩, [⟨1153, 1314⟩, ⟨3803, 4147⟩, ⟨7768, 8043⟩, ⟨12551, 12865⟩, ⟨17879, 18291⟩, ⟨23251, 23592⟩, ⟨27932, 28130⟩, ⟨31264, 31330⟩]⟩

theorem row037_ok : row037.ok = true := by decide +kernel

def row038 : CageRow :=
  ⟨⟨4, 7, 4, 7⟩, [⟨1100, 1277⟩, ⟨3682, 4027⟩, ⟨7622, 7851⟩, ⟨12387, 12729⟩, ⟨17780, 18189⟩, ⟨23200, 23530⟩, ⟨27910, 28100⟩, ⟨31258, 31321⟩]⟩

theorem row038_ok : row038.ok = true := by decide +kernel

def row039 : CageRow :=
  ⟨⟨3, 0, 3, 4⟩, [⟨1738, 1975⟩, ⟨5853, 8999⟩, ⟨5853, 8877⟩, ⟨6163, 9673⟩, ⟨15409, 16056⟩, ⟨21857, 22156⟩, ⟨27262, 27396⟩, ⟨31061, 31101⟩]⟩

theorem row039_ok : row039.ok = true := by decide +kernel

def row040 : CageRow :=
  ⟨⟨4, 0, 4, 10⟩, [⟨1886, 2079⟩, ⟨4926, 6945⟩, ⟨4926, 6945⟩, ⟨8651, 9416⟩, ⟨15615, 15873⟩, ⟨21918, 22048⟩, ⟨27283, 27343⟩, ⟨31067, 31085⟩]⟩

theorem row040_ok : row040.ok = true := by decide +kernel

def row041 : CageRow :=
  ⟨⟨5, 0, 4, 11⟩, [⟨2024, 2283⟩, ⟨3980, 7056⟩, ⟨3980, 7056⟩, ⟨9065, 9456⟩, ⟨15688, 15830⟩, ⟨21943, 22013⟩, ⟨27292, 27324⟩, ⟨31069, 31079⟩]⟩

theorem row041_ok : row041.ok = true := by decide +kernel

def rows04 : List CageRow := [row034, row035, row036, row037, row038, row039, row040, row041]

theorem rows04_ok : rows04.all CageRow.ok = true := by
  simp only [rows04, List.all_cons, List.all_nil, row034_ok, row035_ok, row036_ok, row037_ok, row038_ok, row039_ok, row040_ok, row041_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

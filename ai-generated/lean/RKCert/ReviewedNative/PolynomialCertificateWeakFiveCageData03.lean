module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row026 : CageRow :=
  ⟨⟨4, 6, 3, 1⟩, [⟨1369, 1485⟩, ⟨4341, 4716⟩, ⟨8398, 9029⟩, ⟨13030, 13567⟩, ⟨17902, 18547⟩, ⟨23137, 23605⟩, ⟨27844, 28081⟩, ⟨31233, 31305⟩]⟩

theorem row026_ok : row026.ok = true := by decide +kernel

def row027 : CageRow :=
  ⟨⟨4, 7, 3, 1⟩, [⟨1268, 1410⟩, ⟨4103, 4489⟩, ⟨8192, 8706⟩, ⟨13101, 13493⟩, ⟨18244, 18766⟩, ⟨23439, 23901⟩, ⟨28011, 28283⟩, ⟨31286, 31376⟩]⟩

theorem row027_ok : row027.ok = true := by decide +kernel

def row028 : CageRow :=
  ⟨⟨3, 2, 3, 2⟩, [⟨1415, 1597⟩, ⟨4411, 5098⟩, ⟨8225, 9647⟩, ⟨11701, 13031⟩, ⟨16770, 17903⟩, ⟨22513, 23138⟩, ⟨27558, 27845⟩, ⟨31148, 31234⟩]⟩

theorem row028_ok : row028.ok = true := by decide +kernel

def row029 : CageRow :=
  ⟨⟨4, 4, 3, 3⟩, [⟨1467, 1587⟩, ⟨4471, 5027⟩, ⟨7779, 9007⟩, ⟨11147, 12228⟩, ⟨16682, 17227⟩, ⟨22488, 22761⟩, ⟨27550, 27673⟩, ⟨31146, 31183⟩]⟩

theorem row029_ok : row029.ok = true := by decide +kernel

def row030 : CageRow :=
  ⟨⟨4, 5, 3, 3⟩, [⟨1354, 1507⟩, ⟨4146, 4708⟩, ⟨7702, 8509⟩, ⟨11716, 12529⟩, ⟨17063, 17636⟩, ⟨22703, 23028⟩, ⟨27652, 27805⟩, ⟨31177, 31223⟩]⟩

theorem row030_ok : row030.ok = true := by decide +kernel

def row031 : CageRow :=
  ⟨⟨4, 6, 3, 2⟩, [⟨1313, 1457⟩, ⟨4146, 4592⟩, ⟨8042, 8677⟩, ⟨12528, 13102⟩, ⟨17635, 18245⟩, ⟨23027, 23440⟩, ⟨27804, 28012⟩, ⟨31222, 31287⟩]⟩

theorem row031_ok : row031.ok = true := by decide +kernel

def row032 : CageRow :=
  ⟨⟨4, 7, 4, 4⟩, [⟨1236, 1370⟩, ⟨4013, 4342⟩, ⟨8055, 8399⟩, ⟨12910, 13150⟩, ⟨18110, 18515⟩, ⟨23370, 23734⟩, ⟨27982, 28199⟩, ⟨31278, 31351⟩]⟩

theorem row032_ok : row032.ok = true := by decide +kernel

def row033 : CageRow :=
  ⟨⟨4, 7, 4, 5⟩, [⟨1198, 1344⟩, ⟨3913, 4251⟩, ⟨7914, 8227⟩, ⟨12725, 13006⟩, ⟨17989, 18400⟩, ⟨23307, 23660⟩, ⟨27956, 28163⟩, ⟨31270, 31340⟩]⟩

theorem row033_ok : row033.ok = true := by decide +kernel

def rows03 : List CageRow := [row026, row027, row028, row029, row030, row031, row032, row033]

theorem rows03_ok : rows03.all CageRow.ok = true := by
  simp only [rows03, List.all_cons, List.all_nil, row026_ok, row027_ok, row028_ok, row029_ok, row030_ok, row031_ok, row032_ok, row033_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

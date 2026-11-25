module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row092 : CageRow :=
  ⟨⟨5, 13, 4, 12⟩, [⟨744, 978⟩, ⟨2974, 3212⟩, ⟨6649, 6913⟩, ⟨11600, 11861⟩, ⟨17260, 17470⟩, ⟨22898, 23039⟩, ⟨27767, 27841⟩, ⟨31215, 31239⟩]⟩

theorem row092_ok : row092.ok = true := by decide +kernel

def row093 : CageRow :=
  ⟨⟨5, 12, 4, 13⟩, [⟨613, 907⟩, ⟨2722, 2984⟩, ⟨6367, 6650⟩, ⟨11351, 11601⟩, ⟨17069, 17261⟩, ⟨22774, 22899⟩, ⟨27703, 27768⟩, ⟨31195, 31216⟩]⟩

theorem row093_ok : row093.ok = true := by decide +kernel

def row094 : CageRow :=
  ⟨⟨5, 13, 4, 13⟩, [⟨548, 822⟩, ⟨2756, 2979⟩, ⟨6499, 6757⟩, ⟨11511, 11759⟩, ⟨17210, 17410⟩, ⟨22872, 23007⟩, ⟨27756, 27827⟩, ⟨31212, 31235⟩]⟩

theorem row094_ok : row094.ok = true := by decide +kernel

def row095 : CageRow :=
  ⟨⟨4, 7, 4, 12⟩, [⟨610, 897⟩, ⟨2968, 3175⟩, ⟨6756, 7059⟩, ⟨11758, 12143⟩, ⟨17409, 17777⟩, ⟨23006, 23282⟩, ⟨27826, 27981⟩, ⟨31234, 31285⟩]⟩

theorem row095_ok : row095.ok = true := by decide +kernel

def row096 : CageRow :=
  ⟨⟨4, 7, 4, 13⟩, [⟨440, 745⟩, ⟨2783, 2975⟩, ⟨6616, 6933⟩, ⟨11666, 12047⟩, ⟨17354, 17712⟩, ⟨22977, 23243⟩, ⟨27813, 27962⟩, ⟨31230, 31280⟩]⟩

theorem row096_ok : row096.ok = true := by decide +kernel

def row097 : CageRow :=
  ⟨⟨5, 12, 4, 14⟩, [⟨340, 687⟩, ⟨2497, 2757⟩, ⟨6236, 6500⟩, ⟨11278, 11512⟩, ⟨17030, 17211⟩, ⟨22754, 22873⟩, ⟨27695, 27757⟩, ⟨31193, 31213⟩]⟩

theorem row097_ok : row097.ok = true := by decide +kernel

def row098 : CageRow :=
  ⟨⟨5, 13, 4, 14⟩, [⟨301, 614⟩, ⟨2558, 2784⟩, ⟨6369, 6617⟩, ⟨11432, 11667⟩, ⟨17165, 17355⟩, ⟨22849, 22978⟩, ⟨27745, 27814⟩, ⟨31209, 31231⟩]⟩

theorem row098_ok : row098.ok = true := by decide +kernel

def row099 : CageRow :=
  ⟨⟨4, 6, 4, 15⟩, [⟨0, 386⟩, ⟨2319, 2610⟩, ⟨6126, 6492⟩, ⟨11214, 11585⟩, ⟨16995, 17306⟩, ⟨22736, 22951⟩, ⟨27687, 27802⟩, ⟨31191, 31228⟩]⟩

theorem row099_ok : row099.ok = true := by decide +kernel

def rows11 : List CageRow := [row092, row093, row094, row095, row096, row097, row098, row099]

theorem rows11_ok : rows11.all CageRow.ok = true := by
  simp only [rows11, List.all_cons, List.all_nil, row092_ok, row093_ok, row094_ok, row095_ok, row096_ok, row097_ok, row098_ok, row099_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

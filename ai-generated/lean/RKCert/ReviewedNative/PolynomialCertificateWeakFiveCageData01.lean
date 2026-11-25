module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row008 : CageRow :=
  ⟨⟨4, 3, 4, 2⟩, [⟨1600, 1653⟩, ⟨5120, 5329⟩, ⟨9822, 10625⟩, ⟨13304, 14562⟩, ⟨16041, 17218⟩, ⟨22268, 22601⟩, ⟨27454, 27584⟩, ⟨31118, 31155⟩]⟩

theorem row008_ok : row008.ok = true := by decide +kernel

def row009 : CageRow :=
  ⟨⟨4, 3, 4, 3⟩, [⟨1596, 1653⟩, ⟨5097, 5335⟩, ⟨9646, 10768⟩, ⟨12061, 13316⟩, ⟨16178, 17044⟩, ⟨22276, 22572⟩, ⟨27456, 27576⟩, ⟨31119, 31153⟩]⟩

theorem row009_ok : row009.ok = true := by decide +kernel

def row010 : CageRow :=
  ⟨⟨4, 0, 3, 2⟩, [⟨1743, 1814⟩, ⟨5738, 6177⟩, ⟨10147, 13117⟩, ⟨10147, 13117⟩, ⟨14179, 15386⟩, ⟨21655, 21923⟩, ⟨27204, 27302⟩, ⟨31047, 31075⟩]⟩

theorem row010_ok : row010.ok = true := by decide +kernel

def row011 : CageRow :=
  ⟨⟨4, 1, 4, 4⟩, [⟨1701, 1755⟩, ⟨5550, 5823⟩, ⟨10980, 13004⟩, ⟨10980, 13004⟩, ⟨14650, 15671⟩, ⟨21834, 22072⟩, ⟨27277, 27369⟩, ⟨31068, 31095⟩]⟩

theorem row011_ok : row011.ok = true := by decide +kernel

def row013 : CageRow :=
  ⟨⟨5, 0, 4, 6⟩, [⟨1791, 1837⟩, ⟨6068, 6444⟩, ⟨8711, 12244⟩, ⟨8711, 12244⟩, ⟨15041, 15396⟩, ⟨21774, 21885⟩, ⟨27237, 27281⟩, ⟨31055, 31068⟩]⟩

theorem row013_ok : row013.ok = true := by decide +kernel

def row014 : CageRow :=
  ⟨⟨5, 1, 4, 6⟩, [⟨1767, 1812⟩, ⟨5947, 6314⟩, ⟨8295, 11261⟩, ⟨8295, 11261⟩, ⟨15202, 15550⟩, ⟨21845, 21956⟩, ⟨27268, 27312⟩, ⟨31064, 31077⟩]⟩

theorem row014_ok : row014.ok = true := by decide +kernel

def row015 : CageRow :=
  ⟨⟨4, 0, 4, 7⟩, [⟨1785, 1868⟩, ⟨6159, 6951⟩, ⟨8083, 9418⟩, ⟨8083, 9418⟩, ⟨15255, 15666⟩, ⟨21818, 21984⟩, ⟨27250, 27321⟩, ⟨31058, 31079⟩]⟩

theorem row015_ok : row015.ok = true := by decide +kernel

def row017 : CageRow :=
  ⟨⟨4, 1, 4, 7⟩, [⟨1725, 1809⟩, ⟨5787, 6625⟩, ⟨7471, 9613⟩, ⟨7471, 9613⟩, ⟨15549, 15968⟩, ⟨21955, 22130⟩, ⟨27311, 27387⟩, ⟨31076, 31099⟩]⟩

theorem row017_ok : row017.ok = true := by decide +kernel

def rows01 : List CageRow := [row008, row009, row010, row011, row013, row014, row015, row017]

theorem rows01_ok : rows01.all CageRow.ok = true := by
  simp only [rows01, List.all_cons, List.all_nil, row008_ok, row009_ok, row010_ok, row011_ok, row013_ok, row014_ok, row015_ok, row017_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row000 : CageRow :=
  ⟨⟨3, 0, 3, 0⟩, [⟨1684, 1758⟩, ⟨5451, 5756⟩, ⟨10945, 12413⟩, ⟨13434, 16384⟩, ⟨13434, 16384⟩, ⟨21138, 21965⟩, ⟨27100, 27343⟩, ⟨31026, 31089⟩]⟩

theorem row000_ok : row000.ok = true := by decide +kernel

def row001 : CageRow :=
  ⟨⟨3, 0, 3, 1⟩, [⟨1691, 1781⟩, ⟨5488, 5900⟩, ⟨11303, 14461⟩, ⟨11712, 14977⟩, ⟨12131, 15420⟩, ⟨21470, 22044⟩, ⟨27160, 27362⟩, ⟨31038, 31093⟩]⟩

theorem row001_ok : row001.ok = true := by decide +kernel

def row002 : CageRow :=
  ⟨⟨4, 2, 3, 0⟩, [⟨1649, 1692⟩, ⟨5317, 5489⟩, ⟨10521, 11304⟩, ⟨14561, 16384⟩, ⟨14464, 16384⟩, ⟨21822, 22269⟩, ⟨27316, 27455⟩, ⟨31083, 31119⟩]⟩

theorem row002_ok : row002.ok = true := by decide +kernel

def row003 : CageRow :=
  ⟨⟨5, 6, 4, 0⟩, [⟨1629, 1651⟩, ⟨5239, 5321⟩, ⟨10277, 10541⟩, ⟨14874, 16384⟩, ⟨15836, 17308⟩, ⟨22246, 22465⟩, ⟨27450, 27524⟩, ⟨31118, 31138⟩]⟩

theorem row003_ok : row003.ok = true := by decide +kernel

def row004 : CageRow :=
  ⟨⟨5, 7, 4, 0⟩, [⟨1606, 1631⟩, ⟨5153, 5245⟩, ⟨10025, 10304⟩, ⟨14471, 15461⟩, ⟨16947, 17828⟩, ⟨22445, 22682⟩, ⟨27519, 27603⟩, ⟨31136, 31159⟩]⟩

theorem row004_ok : row004.ok = true := by decide +kernel

def row005 : CageRow :=
  ⟨⟨5, 6, 4, 1⟩, [⟨1628, 1652⟩, ⟨5234, 5325⟩, ⟨10240, 10571⟩, ⟨14124, 15973⟩, ⟨14820, 16948⟩, ⟨22259, 22446⟩, ⟨27452, 27520⟩, ⟨31118, 31137⟩]⟩

theorem row005_ok : row005.ok = true := by decide +kernel

def row006 : CageRow :=
  ⟨⟨5, 7, 4, 1⟩, [⟨1604, 1630⟩, ⟨5139, 5240⟩, ⟨9941, 10278⟩, ⟨13911, 14875⟩, ⟨16759, 17471⟩, ⟨22431, 22636⟩, ⟨27516, 27592⟩, ⟨31136, 31157⟩]⟩

theorem row006_ok : row006.ok = true := by decide +kernel

def row007 : CageRow :=
  ⟨⟨4, 2, 3, 1⟩, [⟨1651, 1702⟩, ⟨5324, 5551⟩, ⟨10570, 15809⟩, ⟨11200, 15489⟩, ⟨10880, 16235⟩, ⟨21964, 22283⟩, ⟨27342, 27458⟩, ⟨31088, 31120⟩]⟩

theorem row007_ok : row007.ok = true := by decide +kernel

def rows00 : List CageRow := [row000, row001, row002, row003, row004, row005, row006, row007]

theorem rows00_ok : rows00.all CageRow.ok = true := by
  simp only [rows00, List.all_cons, List.all_nil, row000_ok, row001_ok, row002_ok, row003_ok, row004_ok, row005_ok, row006_ok, row007_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row043 : CageRow :=
  ⟨⟨4, 1, 4, 10⟩, [⟨1784, 1966⟩, ⟨5072, 7969⟩, ⟨5072, 7969⟩, ⟨9078, 9852⟩, ⟨15818, 16087⟩, ⟨22028, 22167⟩, ⟨27335, 27400⟩, ⟨31082, 31102⟩]⟩

theorem row043_ok : row043.ok = true := by decide +kernel

def row045 : CageRow :=
  ⟨⟨4, 2, 3, 4⟩, [⟨1659, 1785⟩, ⟨5403, 8087⟩, ⟨5739, 9389⟩, ⟨6828, 10312⟩, ⟨15967, 16327⟩, ⟨22129, 22302⟩, ⟨27386, 27465⟩, ⟨31098, 31122⟩]⟩

theorem row045_ok : row045.ok = true := by decide +kernel

def row046 : CageRow :=
  ⟨⟨4, 3, 4, 8⟩, [⟨1555, 1663⟩, ⟨4744, 5477⟩, ⟨7099, 8320⟩, ⟨10178, 11148⟩, ⟨16311, 16683⟩, ⟨22297, 22489⟩, ⟨27462, 27551⟩, ⟨31120, 31147⟩]⟩

theorem row046_ok : row046.ok = true := by decide +kernel

def row047 : CageRow :=
  ⟨⟨4, 3, 4, 9⟩, [⟨1537, 1668⟩, ⟨4517, 6252⟩, ⟨5483, 7313⟩, ⟨10270, 10997⟩, ⟨16319, 16652⟩, ⟨22299, 22478⟩, ⟨27463, 27547⟩, ⟨31120, 31146⟩]⟩

theorem row047_ok : row047.ok = true := by decide +kernel

def row048 : CageRow :=
  ⟨⟨4, 2, 3, 5⟩, [⟨1667, 1920⟩, ⟨4420, 6366⟩, ⟨4480, 6366⟩, ⟨9672, 10353⟩, ⟨16055, 16336⟩, ⟨22155, 22306⟩, ⟨27395, 27466⟩, ⟨31100, 31122⟩]⟩

theorem row048_ok : row048.ok = true := by decide +kernel

def row049 : CageRow :=
  ⟨⟨4, 3, 4, 10⟩, [⟨1508, 1675⟩, ⟨4151, 5756⟩, ⟨5135, 6741⟩, ⟨10311, 10893⟩, ⟨16326, 16627⟩, ⟨22301, 22470⟩, ⟨27464, 27544⟩, ⟨31121, 31146⟩]⟩

theorem row049_ok : row049.ok = true := by decide +kernel

def row050 : CageRow :=
  ⟨⟨4, 3, 4, 11⟩, [⟨1460, 1689⟩, ⟨3633, 5232⟩, ⟨4645, 6282⟩, ⟨10336, 10819⟩, ⟨16331, 16606⟩, ⟨22303, 22462⟩, ⟨27464, 27541⟩, ⟨31121, 31145⟩]⟩

theorem row050_ok : row050.ok = true := by decide +kernel

def row051 : CageRow :=
  ⟨⟨4, 0, 3, 6⟩, [⟨1765, 4331⟩, ⟨1765, 4391⟩, ⟨1724, 4391⟩, ⟨9318, 9830⟩, ⟨15748, 15986⟩, ⟨21965, 22092⟩, ⟨27300, 27359⟩, ⟨31071, 31089⟩]⟩

theorem row051_ok : row051.ok = true := by decide +kernel

def rows05 : List CageRow := [row043, row045, row046, row047, row048, row049, row050, row051]

theorem rows05_ok : rows05.all CageRow.ok = true := by
  simp only [rows05, List.all_cons, List.all_nil, row043_ok, row045_ok, row046_ok, row047_ok, row048_ok, row049_ok, row050_ok, row051_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

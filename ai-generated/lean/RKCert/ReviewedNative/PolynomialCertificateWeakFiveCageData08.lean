module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row068 : CageRow :=
  ⟨⟨5, 12, 4, 8⟩, [⟨1243, 1355⟩, ⟨3844, 4147⟩, ⟨7432, 7703⟩, ⟨11930, 12258⟩, ⟨17352, 17611⟩, ⟨22906, 23070⟩, ⟨27757, 27839⟩, ⟨31210, 31236⟩]⟩

theorem row068_ok : row068.ok = true := by decide +kernel

def row069 : CageRow :=
  ⟨⟨5, 13, 4, 8⟩, [⟨1175, 1294⟩, ⟨3733, 4011⟩, ⟨7446, 7676⟩, ⟨12093, 12388⟩, ⟨17523, 17781⟩, ⟨23027, 23201⟩, ⟨27821, 27911⟩, ⟨31230, 31259⟩]⟩

theorem row069_ok : row069.ok = true := by decide +kernel

def row070 : CageRow :=
  ⟨⟨5, 12, 4, 9⟩, [⟨1177, 1310⟩, ⟨3653, 3972⟩, ⟨7171, 7447⟩, ⟨11778, 12094⟩, ⟨17280, 17524⟩, ⟨22874, 23028⟩, ⟨27745, 27822⟩, ⟨31206, 31231⟩]⟩

theorem row070_ok : row070.ok = true := by decide +kernel

def row071 : CageRow :=
  ⟨⟨5, 13, 4, 9⟩, [⟨1104, 1244⟩, ⟨3560, 3845⟩, ⟨7223, 7459⟩, ⟨11947, 12237⟩, ⟨17446, 17691⟩, ⟨22990, 23155⟩, ⟨27806, 27891⟩, ⟨31226, 31253⟩]⟩

theorem row071_ok : row071.ok = true := by decide +kernel

def row072 : CageRow :=
  ⟨⟨4, 7, 4, 8⟩, [⟨1036, 1232⟩, ⟨3551, 3889⟩, ⟨7458, 7655⟩, ⟨12236, 12599⟩, ⟨17690, 18094⟩, ⟨23154, 23472⟩, ⟨27890, 28072⟩, ⟨31252, 31313⟩]⟩

theorem row072_ok : row072.ok = true := by decide +kernel

def row073 : CageRow :=
  ⟨⟨4, 7, 4, 9⟩, [⟨959, 1176⟩, ⟨3412, 3734⟩, ⟨7266, 7476⟩, ⟨12098, 12474⟩, ⟨17609, 18006⟩, ⟨23112, 23419⟩, ⟨27872, 28046⟩, ⟨31247, 31305⟩]⟩

theorem row073_ok : row073.ok = true := by decide +kernel

def row074 : CageRow :=
  ⟨⟨5, 12, 4, 10⟩, [⟨1092, 1252⟩, ⟨3440, 3763⟩, ⟨6929, 7224⟩, ⟨11646, 11948⟩, ⟨17218, 17447⟩, ⟨22845, 22991⟩, ⟨27733, 27807⟩, ⟨31203, 31227⟩]⟩

theorem row074_ok : row074.ok = true := by decide +kernel

def row075 : CageRow :=
  ⟨⟨5, 13, 5, 20⟩, [⟨1062, 1178⟩, ⟨3467, 3654⟩, ⟨7116, 7267⟩, ⟨11880, 12099⟩, ⟨17410, 17610⟩, ⟨22973, 23113⟩, ⟨27799, 27873⟩, ⟨31224, 31248⟩]⟩

theorem row075_ok : row075.ok = true := by decide +kernel

def rows08 : List CageRow := [row068, row069, row070, row071, row072, row073, row074, row075]

theorem rows08_ok : rows08.all CageRow.ok = true := by
  simp only [rows08, List.all_cons, List.all_nil, row068_ok, row069_ok, row070_ok, row071_ok, row072_ok, row073_ok, row074_ok, row075_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

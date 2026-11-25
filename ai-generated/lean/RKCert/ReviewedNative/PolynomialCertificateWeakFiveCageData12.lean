module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row100 : CageRow :=
  ⟨⟨4, 7, 3, 7⟩, [⟨0, 549⟩, ⟨2460, 2826⟩, ⟨6382, 6815⟩, ⟨11510, 11958⟩, ⟨17259, 17651⟩, ⟨22925, 23207⟩, ⟨27789, 27944⟩, ⟨31223, 31275⟩]⟩

theorem row100_ok : row100.ok = true := by decide +kernel

def row101 : CageRow :=
  ⟨⟨4, 8, 3, 0⟩, [⟨1216, 1361⟩, ⟨4034, 4384⟩, ⟨8240, 8673⟩, ⟨13405, 13730⟩, ⟨18765, 19145⟩, ⟨23900, 24338⟩, ⟨28282, 28606⟩, ⟨31375, 31502⟩]⟩

theorem row101_ok : row101.ok = true := by decide +kernel

def row102 : CageRow :=
  ⟨⟨4, 9, 3, 0⟩, [⟨1095, 1267⟩, ⟨3822, 4163⟩, ⟨8072, 8431⟩, ⟨13377, 13624⟩, ⟨18932, 19226⟩, ⟨24164, 24542⟩, ⟨28496, 28826⟩, ⟨31461, 31615⟩]⟩

theorem row102_ok : row102.ok = true := by decide +kernel

def row103 : CageRow :=
  ⟨⟨4, 8, 3, 1⟩, [⟨1153, 1321⟩, ⟨3885, 4259⟩, ⟨8035, 8448⟩, ⟨13149, 13442⟩, ⟨18514, 18933⟩, ⟨23733, 24165⟩, ⟨28198, 28497⟩, ⟨31350, 31462⟩]⟩

theorem row103_ok : row103.ok = true := by decide +kernel

def row104 : CageRow :=
  ⟨⟨4, 9, 3, 1⟩, [⟨1023, 1217⟩, ⟨3688, 4035⟩, ⟨7912, 8241⟩, ⟨13184, 13406⟩, ⟨18730, 19063⟩, ⟨24009, 24397⟩, ⟨28403, 28719⟩, ⟨31429, 31567⟩]⟩

theorem row104_ok : row104.ok = true := by decide +kernel

def row105 : CageRow :=
  ⟨⟨3, 5, 2, 0⟩, [⟨722, 1154⟩, ⟨3363, 3943⟩, ⟨7734, 8227⟩, ⟨13211, 13543⟩, ⟨18905, 19341⟩, ⟨24261, 24857⟩, ⟨28622, 29234⟩, ⟨31526, 31906⟩]⟩

theorem row105_ok : row105.ok = true := by decide +kernel

def row106 : CageRow :=
  ⟨⟨4, 8, 3, 2⟩, [⟨1071, 1269⟩, ⟨3712, 4104⟩, ⟨7819, 8193⟩, ⟨12864, 13185⟩, ⟨18290, 18731⟩, ⟨23591, 24010⟩, ⟨28129, 28404⟩, ⟨31329, 31430⟩]⟩

theorem row106_ok : row106.ok = true := by decide +kernel

def row107 : CageRow :=
  ⟨⟨4, 9, 3, 2⟩, [⟨935, 1154⟩, ⟨3541, 3886⟩, ⟨7747, 8036⟩, ⟨12967, 13212⟩, ⟨18542, 18906⟩, ⟨23870, 24262⟩, ⟨28324, 28623⟩, ⟨31402, 31527⟩]⟩

theorem row107_ok : row107.ok = true := by decide +kernel

def rows12 : List CageRow := [row100, row101, row102, row103, row104, row105, row106, row107]

theorem rows12_ok : rows12.all CageRow.ok = true := by
  simp only [rows12, List.all_cons, List.all_nil, row100_ok, row101_ok, row102_ok, row103_ok, row104_ok, row105_ok, row106_ok, row107_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

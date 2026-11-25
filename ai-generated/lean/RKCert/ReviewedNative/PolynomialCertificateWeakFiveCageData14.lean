module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row116 : CageRow :=
  ⟨⟨3, 5, 3, 4⟩, [⟨429, 824⟩, ⟨3092, 3383⟩, ⟨7415, 7581⟩, ⟨12732, 13073⟩, ⟨18475, 18993⟩, ⟨23915, 24522⟩, ⟨28397, 28935⟩, ⟨31439, 31712⟩]⟩

theorem row116_ok : row116.ok = true := by decide +kernel

def row117 : CageRow :=
  ⟨⟨3, 5, 3, 5⟩, [⟨303, 683⟩, ⟨3001, 3216⟩, ⟨7254, 7467⟩, ⟨12585, 12986⟩, ⟨18349, 18909⟩, ⟨23818, 24444⟩, ⟨28337, 28870⟩, ⟨31417, 31676⟩]⟩

theorem row117_ok : row117.ok = true := by decide +kernel

def row118 : CageRow :=
  ⟨⟨4, 8, 3, 6⟩, [⟨352, 751⟩, ⟨2825, 3118⟩, ⟨6814, 7169⟩, ⟨11957, 12383⟩, ⟨17650, 18073⟩, ⟨23206, 23544⟩, ⟨27943, 28145⟩, ⟨31274, 31344⟩]⟩

theorem row118_ok : row118.ok = true := by decide +kernel

def row119 : CageRow :=
  ⟨⟨4, 9, 3, 6⟩, [⟨278, 620⟩, ⟨2855, 3077⟩, ⟨6972, 7255⟩, ⟨12218, 12586⟩, ⟨17946, 18350⟩, ⟨23458, 23819⟩, ⟨28099, 28338⟩, ⟨31328, 31418⟩]⟩

theorem row119_ok : row119.ok = true := by decide +kernel

def row120 : CageRow :=
  ⟨⟨4, 8, 3, 7⟩, [⟨0, 441⟩, ⟨2568, 2856⟩, ⟨6604, 6973⟩, ⟨11799, 12219⟩, ⟨17541, 17947⟩, ⟨23140, 23459⟩, ⟨27912, 28100⟩, ⟨31264, 31329⟩]⟩

theorem row120_ok : row120.ok = true := by decide +kernel

def row121 : CageRow :=
  ⟨⟨4, 9, 3, 7⟩, [⟨0, 353⟩, ⟨2654, 2880⟩, ⟨6794, 7101⟩, ⟨12070, 12448⟩, ⟨17833, 18233⟩, ⟨23383, 23731⟩, ⟨28059, 28285⟩, ⟨31315, 31399⟩]⟩

theorem row121_ok : row121.ok = true := by decide +kernel

def row122 : CageRow :=
  ⟨⟨3, 5, 3, 6⟩, [⟨161, 504⟩, ⟨2879, 3046⟩, ⟨7100, 7379⟩, ⟨12447, 12901⟩, ⟨18232, 18827⟩, ⟨23730, 24369⟩, ⟨28284, 28809⟩, ⟨31398, 31644⟩]⟩

theorem row122_ok : row122.ok = true := by decide +kernel

def row123 : CageRow :=
  ⟨⟨3, 5, 3, 7⟩, [⟨0, 279⟩, ⟨2723, 2913⟩, ⟨6956, 7293⟩, ⟨12317, 12817⟩, ⟨18124, 18747⟩, ⟨23650, 24297⟩, ⟨28237, 28752⟩, ⟨31381, 31615⟩]⟩

theorem row123_ok : row123.ok = true := by decide +kernel

def rows14 : List CageRow := [row116, row117, row118, row119, row120, row121, row122, row123]

theorem rows14_ok : rows14.all CageRow.ok = true := by
  simp only [rows14, List.all_cons, List.all_nil, row116_ok, row117_ok, row118_ok, row119_ok, row120_ok, row121_ok, row122_ok, row123_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

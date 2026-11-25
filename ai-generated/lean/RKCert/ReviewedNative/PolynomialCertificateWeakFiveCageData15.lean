module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row124 : CageRow :=
  ⟨⟨2, 3, 2, 2⟩, [⟨0, 541⟩, ⟨2951, 3184⟩, ⟨7378, 7556⟩, ⟨12900, 13293⟩, ⟨18826, 19476⟩, ⟨24368, 25242⟩, ⟨28808, 29817⟩, ⟨31643, 32768⟩]⟩

theorem row124_ok : row124.ok = true := by decide +kernel

def row125 : CageRow :=
  ⟨⟨3, 6, 2, 3⟩, [⟨0, 304⟩, ⟨2826, 3002⟩, ⟨7208, 7465⟩, ⟨12734, 13127⟩, ⟨18669, 19197⟩, ⟨24227, 24858⟩, ⟨28697, 29344⟩, ⟨31588, 32053⟩]⟩

theorem row125_ok : row125.ok = true := by decide +kernel

def row126 : CageRow :=
  ⟨⟨3, 7, 2, 3⟩, [⟨0, 139⟩, ⟨2898, 2973⟩, ⟨7391, 7527⟩, ⟨13052, 13293⟩, ⟨19123, 19476⟩, ⟨24784, 25242⟩, ⟨29272, 29817⟩, ⟨31989, 32768⟩]⟩

theorem row126_ok : row126.ok = true := by decide +kernel

def rows15 : List CageRow := [row124, row125, row126]

theorem rows15_ok : rows15.all CageRow.ok = true := by
  simp only [rows15, List.all_cons, List.all_nil, row124_ok, row125_ok, row126_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

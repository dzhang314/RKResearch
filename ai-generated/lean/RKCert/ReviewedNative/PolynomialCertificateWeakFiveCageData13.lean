module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row108 : CageRow :=
  ⟨⟨4, 8, 3, 3⟩, [⟨963, 1199⟩, ⟨3516, 3914⟩, ⟨7598, 7915⟩, ⟨12598, 12968⟩, ⟨18093, 18543⟩, ⟨23471, 23871⟩, ⟨28071, 28325⟩, ⟨31312, 31403⟩]⟩

theorem row108_ok : row108.ok = true := by decide +kernel

def row109 : CageRow :=
  ⟨⟨4, 9, 3, 3⟩, [⟨823, 1072⟩, ⟨3382, 3713⟩, ⟨7580, 7820⟩, ⟨12759, 13048⟩, ⟨18370, 18754⟩, ⟨23748, 24137⟩, ⟨28255, 28539⟩, ⟨31379, 31493⟩]⟩

theorem row109_ok : row109.ok = true := by decide +kernel

def row110 : CageRow :=
  ⟨⟨3, 5, 2, 1⟩, [⟨540, 1024⟩, ⟨3183, 3689⟩, ⟨7555, 7913⟩, ⟨12886, 13250⟩, ⟨18610, 19165⟩, ⟨24020, 24685⟩, ⟨28463, 29076⟩, ⟨31463, 31797⟩]⟩

theorem row110_ok : row110.ok = true := by decide +kernel

def row111 : CageRow :=
  ⟨⟨2, 3, 1, 0⟩, [⟨0, 863⟩, ⟨2951, 3535⟩, ⟨7526, 7912⟩, ⟨13072, 13428⟩, ⟨18992, 19476⟩, ⟨24521, 25242⟩, ⟨28934, 29817⟩, ⟨31711, 32768⟩]⟩

theorem row111_ok : row111.ok = true := by decide +kernel

def row112 : CageRow :=
  ⟨⟨4, 8, 3, 4⟩, [⟨817, 1101⟩, ⟨3301, 3683⟩, ⟨7331, 7623⟩, ⟨12356, 12760⟩, ⟨17923, 18371⟩, ⟨23369, 23749⟩, ⟨28022, 28256⟩, ⟨31297, 31380⟩]⟩

theorem row112_ok : row112.ok = true := by decide +kernel

def row113 : CageRow :=
  ⟨⟨4, 9, 3, 4⟩, [⟨682, 964⟩, ⟨3215, 3517⟩, ⟨7379, 7599⟩, ⟨12563, 12887⟩, ⟨18213, 18611⟩, ⟨23639, 24021⟩, ⟨28196, 28464⟩, ⟨31359, 31464⟩]⟩

theorem row113_ok : row113.ok = true := by decide +kernel

def row114 : CageRow :=
  ⟨⟨4, 8, 3, 5⟩, [⟨619, 960⟩, ⟨3076, 3413⟩, ⟨7058, 7380⟩, ⟨12142, 12564⟩, ⟨17776, 18214⟩, ⟨23281, 23640⟩, ⟨27980, 28197⟩, ⟨31284, 31360⟩]⟩

theorem row114_ok : row114.ok = true := by decide +kernel

def row115 : CageRow :=
  ⟨⟨4, 9, 3, 5⟩, [⟨503, 818⟩, ⟨3045, 3302⟩, ⟨7168, 7416⟩, ⟨12382, 12733⟩, ⟨18072, 18476⟩, ⟨23543, 23916⟩, ⟨28144, 28398⟩, ⟨31343, 31440⟩]⟩

theorem row115_ok : row115.ok = true := by decide +kernel

def rows13 : List CageRow := [row108, row109, row110, row111, row112, row113, row114, row115]

theorem rows13_ok : rows13.all CageRow.ok = true := by
  simp only [rows13, List.all_cons, List.all_nil, row108_ok, row109_ok, row110_ok, row111_ok, row112_ok, row113_ok, row114_ok, row115_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

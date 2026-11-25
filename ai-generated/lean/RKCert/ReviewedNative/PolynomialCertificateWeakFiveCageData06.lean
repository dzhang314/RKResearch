module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def row052 : CageRow :=
  ⟨⟨4, 1, 3, 6⟩, [⟨1890, 4173⟩, ⟨1890, 4497⟩, ⟨2087, 4649⟩, ⟨9608, 10084⟩, ⟨15917, 16153⟩, ⟨22063, 22192⟩, ⟨27348, 27409⟩, ⟨31085, 31105⟩]⟩

theorem row052_ok : row052.ok = true := by decide +kernel

def row053 : CageRow :=
  ⟨⟨3, 0, 3, 7⟩, [⟨0, 2926⟩, ⟨0, 2926⟩, ⟨3772, 4936⟩, ⟨9613, 10156⟩, ⟨15842, 16182⟩, ⟨22003, 22206⟩, ⟨27315, 27415⟩, ⟨31075, 31106⟩]⟩

theorem row053_ok : row053.ok = true := by decide +kernel

def row054 : CageRow :=
  ⟨⟨4, 2, 3, 6⟩, [⟨1688, 2944⟩, ⟨1856, 4737⟩, ⟨2432, 5188⟩, ⟨9958, 10374⟩, ⟨16112, 16343⟩, ⟨22175, 22309⟩, ⟨27402, 27467⟩, ⟨31102, 31122⟩]⟩

theorem row054_ok : row054.ok = true := by decide +kernel

def row055 : CageRow :=
  ⟨⟨4, 3, 3, 6⟩, [⟨1153, 2881⟩, ⟨1600, 4421⟩, ⟨4901, 5971⟩, ⟨10352, 10764⟩, ⟨16335, 16588⟩, ⟨22305, 22455⟩, ⟨27465, 27539⟩, ⟨31121, 31144⟩]⟩

theorem row055_ok : row055.ok = true := by decide +kernel

def row056 : CageRow :=
  ⟨⟨4, 2, 3, 7⟩, [⟨0, 2414⟩, ⟨130, 2414⟩, ⟨4648, 5228⟩, ⟨10083, 10386⟩, ⟨16152, 16348⟩, ⟨22191, 22311⟩, ⟨27408, 27468⟩, ⟨31104, 31123⟩]⟩

theorem row056_ok : row056.ok = true := by decide +kernel

def row057 : CageRow :=
  ⟨⟨4, 3, 3, 7⟩, [⟨0, 1889⟩, ⟨547, 2449⟩, ⟨5187, 5664⟩, ⟨10373, 10690⟩, ⟨16342, 16560⟩, ⟨22308, 22443⟩, ⟨27466, 27534⟩, ⟨31121, 31143⟩]⟩

theorem row057_ok : row057.ok = true := by decide +kernel

def row058 : CageRow :=
  ⟨⟨4, 4, 3, 4⟩, [⟨1397, 1570⟩, ⟨4054, 4882⟩, ⟨6740, 7926⟩, ⟨10892, 11717⟩, ⟨16626, 17064⟩, ⟨22469, 22704⟩, ⟨27543, 27653⟩, ⟨31145, 31178⟩]⟩

theorem row058_ok : row058.ok = true := by decide +kernel

def row059 : CageRow :=
  ⟨⟨5, 10, 4, 8⟩, [⟨1374, 1468⟩, ⟨4119, 4472⟩, ⟨7391, 7780⟩, ⟨11530, 11929⟩, ⟨17001, 17251⟩, ⟨22680, 22821⟩, ⟨27644, 27711⟩, ⟨31175, 31196⟩]⟩

theorem row059_ok : row059.ok = true := by decide +kernel

def rows06 : List CageRow := [row052, row053, row054, row055, row056, row057, row058, row059]

theorem rows06_ok : rows06.all CageRow.ok = true := by
  simp only [rows06, List.all_cons, List.all_nil, row052_ok, row053_ok, row054_ok, row055_ok, row056_ok, row057_ok, row058_ok, row059_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

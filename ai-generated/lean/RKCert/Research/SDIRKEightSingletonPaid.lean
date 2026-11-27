module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

@[expose] public section

/-! # Paid singleton SDIRK8 arithmetic receipts and quadratic modular certificate -/

namespace RKResearch.Certified.SDIRKEightSingletonPaid

theorem forced_complement {R : Type*} [CommRing R] {a y r₀ r₁ s : R}
    (ha : r₀+r₁*(a*(1-a))=0) (hy : r₀+r₁*y=0) (hu : r₁*s=1) :
    a^2-a+y=0 := by
  have h : r₁*(a^2-a+y)=0 := by linear_combination hy-ha
  calc
    a^2-a+y=(r₁*s)*(a^2-a+y) := by rw [hu,one_mul]
    _=s*(r₁*(a^2-a+y)) := by ring
    _=0 := by rw [h,mul_zero]

theorem quadratic_norm {R : Type*} [CommRing R] {a y c d : R}
    (ha : a^2-a+y=0) :
    (c+d*a)*(c+d*(1-a))=c^2+c*d+y*d^2 := by
  linear_combination -(d^2)*ha

theorem nodal_pencil {R : Type*} [CommRing R] {m₀ m₁ m₂ z : R}
    (h₁ : m₁=z*m₀) (h₂ : m₂=z*m₁) : m₀*m₂-m₁^2=0 := by
  rw [h₂,h₁]
  ring

theorem two_atom_cubic {R : Type*} [CommRing R] {m₁ m₂ m₃ x y b c : R}
    (h₁ : m₁=b*x+c*y) (h₂ : m₂=b*x^2+c*y^2) (h₃ : m₃=b*x^3+c*y^3) :
    m₃-(x+y)*m₂+x*y*m₁=0 := by
  rw [h₁,h₂,h₃]
  ring

theorem small_exceptions :
    (392 : ZMod 601) ≠ 561 ∧ (5211 : ZMod 6277) ≠ 5613 ∧
    (83 : ZMod 613)*59-61^2 ≠ 0 := by decide +kernel

def compositeModulus : ℕ := 1934863050827753745780663434769441409548442701185293084553214117772857709420033417878876403724148922630750859089076825788469889821070979913154988384561479017155091742150351943282625430821044382404334746868584382466383424788902957
def pencilConst : ℕ := 333914511530447212560596695233231050578734630254271784194782434769458865809212418678187978742655584884126329913812709234564549207312500604196223443130942810114388199869218263993590295686511312624630923906447767669660318001480785
def pencilLinear : ℕ := 1765024086716211383241971961587297040079285279024550760278165461653260969412846782430898698621908795381659258511212549832690932831199810679253385692667595388673639443057841902193725523330899448006929372494980834016380955705025855
def forcedY : ℕ := 632793690301864634812178949461593430706603109571416407990517185840421290840410718951905789872189247934175804685234385760526071175290972424270956035711305781010440755666720723289047245562283513805291424203578195174578644973040282
def pencilNorm : ℕ := 1311334713341103484375582562682649095438099724074837122248783796518577416611496704246861279412577416062699378209093239242188080776716559936429286006454169843329994141701214196012023021920162678952150879731960449430015535332600223
def pencilNormInv : ℕ := 285283155425130810479773777240193701911729161178569290939509071930343712632169881864578273463440860965332197383045002445864166496625616442076157646740010142481607116165916439505949509657456162682938415175979764907478857581305432

theorem norm_receipt :
    (pencilConst^2+pencilConst*pencilLinear+forcedY*pencilLinear^2) %
      compositeModulus=pencilNorm := by decide +kernel

theorem unit_receipt :
    (pencilNorm*pencilNormInv) % compositeModulus=1 := by decide +kernel

private theorem casts_mod {R : Type*} [CommRing R] {n x r : ℕ}
    (hN : (n : R)=0) (hmod : x%n=r) : (x : R)=r := by
  have h := congrArg (fun v : ℕ => (v : R)) (Nat.mod_add_div x n)
  simpa [Nat.cast_add,Nat.cast_mul,hN,hmod] using h.symm

theorem cofactor_no_zero {R : Type*} [CommRing R] [Nontrivial R] {a : R}
    (hN : (compositeModulus : R)=0) (ha : a^2-a+(forcedY : R)=0) :
    (pencilConst : R)+(pencilLinear : R)*a ≠ 0 := by
  intro hbad
  have hn := casts_mod (R:=R) hN norm_receipt
  have hu := casts_mod (R:=R) hN unit_receipt
  push_cast at hn hu
  have hp := quadratic_norm (c := (pencilConst : R)) (d := (pencilLinear : R)) ha
  rw [hbad, zero_mul, hn] at hp
  rw [←hp, zero_mul] at hu
  exact zero_ne_one hu

end RKResearch.Certified.SDIRKEightSingletonPaid

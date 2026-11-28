module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

namespace RKResearch.Certified.ERK10MirrorCompact
open RKResearch FiniteRootedTree
open scoped Matrix

set_option maxHeartbeats 0
set_option maxRecDepth 50000

abbrev d₁ : ℤ := 27783000
abbrev n₁ : ℤ := 1691
abbrev d₂ : ℤ := 357210000
abbrev n₂ : ℤ := -50329

def tree₁ : FiniteRootedTree := bushyTree 11
def tree₂ : FiniteRootedTree := FiniteRootedTree.butcherProduct (bushyTree 5) (bushyTree 6)

theorem integer_next₁ :
    d₁*((tree₁.factorial:ℤ)*(bNum ⬝ᵥ Φ tree₁ integerA))=(d₁+n₁)*D^11 := by
  rw [show (tree₁.factorial:ℤ) = 11 by decide +kernel]
  simp only [tree₁,Φ_bushyTree,clocks]
  change d₁*(11*(bNum ⬝ᵥ (cNum^10)))=_
  rw [←sparseB]
  decide +kernel

theorem integer_next₂ :
    d₂*((tree₂.factorial:ℤ)*(bNum ⬝ᵥ Φ tree₂ integerA))=(d₂+n₂)*D^11 := by
  rw [show (tree₂.factorial:ℤ) = 66 by decide +kernel]
  simp only [tree₂,Φ,Φ_bushyTree,clocks]
  change d₂*(66*(bNum ⬝ᵥ (cNum^4*(integerA *ᵥ cNum^5))))=_
  rw [←sparseB]
  have hAct : integerA *ᵥ cNum^5 = fun i =>
      sparseDot (aSupport i) (aNum i) (cNum^5) :=
    funext fun i => (sparseA i (cNum^5)).symm
  rw [hAct]
  decide +kernel

theorem from_integer_defect {R : Type*} [CommRing R]
    (t : FiniteRootedTree) (hs : (t.order:ℕ) = 11)
    (m v : ℤ) (he : m*((t.factorial:ℤ)*(bNum ⬝ᵥ Φ t integerA))=(m+v)*D^11)
    (d : R) (hd : (D:R)*d=1) :
    (m:R)*((t.factorial:R)*(b d ⬝ᵥ Φ t (A d))-1)=(v:R) := by
  let f := Int.castRingHom R
  have hm := congrArg f he
  change f (m*((t.factorial:ℤ)*(bNum ⬝ᵥ Φ t integerA))) = f ((m+v)*D^11) at hm
  simp only [map_mul,map_pow,map_add,map_natCast,RingHom.map_dotProduct,RKResearch.map_Φ] at hm
  change (m:R)*((t.factorial:R)*((f ∘ bNum) ⬝ᵥ Φ t (integerA.map f))) =
    ((m:R)+(v:R))*(D:R)^11 at hm
  have h : (t.order:ℕ)-1=10 := by rw [hs]
  simp only [A,b,Φ_matrix_smul,h,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  calc
    _ = ((m:R)*((t.factorial:R)*((f ∘ bNum) ⬝ᵥ Φ t (integerA.map f))))*d^11-(m:R) := by
      simp only [f]
      ring
    _ = (v:R) := by
      rw [hm,mul_assoc,←mul_pow]
      change ((m:R)+(v:R))*((D:R)*d)^11-(m:R)=(v:R)
      rw [hd]
      ring

end RKResearch.Certified.ERK10MirrorCompact

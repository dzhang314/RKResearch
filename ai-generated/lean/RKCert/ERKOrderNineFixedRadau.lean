module

public import RKCert.ERKOrderNineRadau
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Portable fixed-Radau compatibility arithmetic

The field specialization uses integer-ring polynomials. This file
checks the scaling and every nonrepeating assignment mod 353, with no
Galois-group or real-interval computation.
-/
namespace RKCert.Paired

section IntegerExpressions
variable {R S : Type*} [CommRing R] [CommRing S]

def fixedRadauT3Int (x : R) : R :=
  35*x^3 - 60*126*x^2 + 30*126^2*x - 4*126^3

def fixedRadauP0 (h x : R) : R := 3*h^2-6*x^2
def fixedRadauP1 (h x : R) : R := 3*h*x-4*x^2

def fixedRadauFInt (u v : R) (P : R → R) : R :=
  (126-u)^2*(2*u-3*v+126)*fixedRadauT3Int v*P u -
    (126-v)^3*fixedRadauT3Int u*P v

def fixedRadauGInt (r u v : R) (P : R → R) : R :=
  let D := 2*u-3*v+126
  let Dn := 3*r^2+(252-4*u-4*v)*r+126^2-252*u-252*v+6*u*v
  let L := 4*u^2-5*u*v+252*v-126^2-3*(u-v)*r
  D*(126-r)^2*P r*fixedRadauT3Int v*Dn +
    (126-v)^3*P v*fixedRadauT3Int r*L

def fixedRadauCompatInt (h r u v : R) : R :=
  fixedRadauFInt u v (fixedRadauP0 h) * fixedRadauGInt r u v (fixedRadauP1 h) -
    fixedRadauFInt u v (fixedRadauP1 h) * fixedRadauGInt r u v (fixedRadauP0 h)

theorem fixedRadauCompatInt_map (f : R →+* S) (h r u v : R) :
    f (fixedRadauCompatInt h r u v) = fixedRadauCompatInt (f h) (f r) (f u) (f v) := by
  simp [fixedRadauCompatInt,fixedRadauT3Int,fixedRadauP0,fixedRadauP1,
    fixedRadauFInt,fixedRadauGInt,map_ofNat]

end IntegerExpressions

noncomputable def fixedRadauCompatibilityTest : MvPolynomial (Fin 4) ℤ :=
  fixedRadauCompatInt (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3)

theorem fixedRadauCompatibilityTest_eval {R : Type*} [CommRing R] (z : Fin 4 → R) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) z fixedRadauCompatibilityTest =
      fixedRadauCompatInt (z 0) (z 1) (z 2) (z 3) := by
  rw [fixedRadauCompatibilityTest,fixedRadauCompatInt_map]
  simp

section FieldExpressions
variable {K : Type*} [Field K] [CharZero K]

def fixedRadauT3 (x : K) : K := x^3 - (12/7)*x^2 + (6/7)*x - 4/35

def fixedRadauF (u v : K) (P : K → K) : K :=
  (1-u)^2*(2*u-3*v+1)*fixedRadauT3 v*P u -
    (1-v)^3*fixedRadauT3 u*P v

def fixedRadauG (r u v : K) (P : K → K) : K :=
  let D := 2*u-3*v+1
  let Dn := 3*r^2+(2-4*u-4*v)*r+1-2*u-2*v+6*u*v
  let L := 4*u^2-5*u*v+2*v-1-3*(u-v)*r
  D*(1-r)^2*P r*fixedRadauT3 v*Dn +
    (1-v)^3*P v*fixedRadauT3 r*L

def fixedRadauCompat (h r u v : K) : K :=
  fixedRadauF u v (fixedRadauP0 h) * fixedRadauG r u v (fixedRadauP1 h) -
    fixedRadauF u v (fixedRadauP1 h) * fixedRadauG r u v (fixedRadauP0 h)

theorem fixedRadauCompatInt_scale (h r u v : K) :
    fixedRadauCompatInt (126*h) (126*r) (126*u) (126*v) =
      (35^2*126^18)*fixedRadauCompat h r u v := by
  have hT (x : K) : fixedRadauT3Int (126*x) = 35*126^3*fixedRadauT3 x := by
    unfold fixedRadauT3Int fixedRadauT3
    ring
  have h0 (x : K) : fixedRadauP0 (126*h) (126*x) = 126^2*fixedRadauP0 h x := by
    unfold fixedRadauP0
    ring
  have h1 (x : K) : fixedRadauP1 (126*h) (126*x) = 126^2*fixedRadauP1 h x := by
    unfold fixedRadauP1
    ring
  unfold fixedRadauCompatInt fixedRadauCompat fixedRadauFInt fixedRadauF fixedRadauGInt fixedRadauG
  dsimp only
  simp only [hT,h0,h1]
  ring

end FieldExpressions

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
/-- All 24 ordered assignments; coincident residues are not admitted. -/
theorem fixedRadauCompatInt_mod353 (h r u v : ZMod 353)
    (hh : h=41 ∨ h=111 ∨ h=161 ∨ h=320)
    (hr : r=41 ∨ r=111 ∨ r=161 ∨ r=320)
    (hu : u=41 ∨ u=111 ∨ u=161 ∨ u=320)
    (hv : v=41 ∨ v=111 ∨ v=161 ∨ v=320)
    (hhr : h≠r) (hhu : h≠u) (hhv : h≠v) (hru : r≠u) (hrv : r≠v) (huv : u≠v) :
    fixedRadauCompatInt h r u v≠0 := by
  rcases hh with rfl|rfl|rfl|rfl <;> rcases hr with rfl|rfl|rfl|rfl <;>
    rcases hu with rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;>
    first | contradiction | decide

end RKCert.Paired


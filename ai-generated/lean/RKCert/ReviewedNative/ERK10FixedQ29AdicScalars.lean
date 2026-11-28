module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPolynomial
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! The actual fixed-q head solve, before any rational-function cancellation.
The evaluation quadrature of degree nine below is used solely to evaluate
the scalar formal integrals in the fixed-q construction. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic

noncomputable section
open Polynomial
open scoped BigOperators Ring

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

abbrev avgDen : ℕ := 7257600

def avgNumerator : ℕ → ℤ
  | 0 => 2082753
  | 1 => 9449717
  | 2 => -11271304
  | 3 => 16002320
  | 4 => -17283646
  | 5 => 13510082
  | 6 => -7394032
  | 7 => 2687864
  | 8 => -583435
  | 9 => 57281
  | _ => 0

def avgRaw {R : Type*} [CommRing R] (p : R → R) : R :=
  ∑ i : Fin 10, (avgNumerator i.val : R) * p (i.val : R)

def avg {R : Type*} [CommRing R] (p : R → R) : R :=
  (avgDen : R)⁻¹ʳ * avgRaw p

theorem avg_integer_moments :
    ∀ n : Fin 10, (n.val + 1 : ℤ) * avgRaw (fun x : ℤ => x ^ n.val) = avgDen := by
  decide +kernel

theorem avgDen_two : (avgDen : F) = 2 := by decide +kernel

section Formulas

variable {R : Type*} [CommRing R]

/-- x²(x-c)² and its antiderivative vanishing at zero. -/
def m (c x : R) : R := x^2 * (x-c)^2
def jm (c x : R) : R := x^3 * (c^2*(3:R)⁻¹ʳ-c*x*(2:R)⁻¹ʳ+x^2*(5:R)⁻¹ʳ)
def wEarly (c x : R) : R := (1-x)*(x-6)*(x-15)*jm c x
def hDen (c : R) : R := avg (fun x => wEarly c x)
def hTail (c : R) : R := avg (fun x => x*wEarly c x) * (hDen c)⁻¹ʳ

def sFour (c x : R) : R := (1-x)*(x-6)*(x-hTail c)*(x-15)
def fDen (c : R) : R := avg (fun x => sFour c x*m c x)
def fTail (c : R) : R := avg (fun x => sFour c x*x*m c x) * (fDen c)⁻¹ʳ

def omegaPoly (c : R) : R := 210*c^3-336*c^2+168*c-28
def eDen (c : R) : R := c+c*omegaPoly c*26
def eTail (c : R) : R := c*(c-26)*(eDen c)⁻¹ʳ
def tThree (c x : R) : R := (x-fTail c)*(x-6)*(x-hTail c)

def kMom (c : R) : R := avg (fun x => x*(x-1)*(x-c)^2*(x-15)*tThree c x)
def jMom (c : R) : R := avg (fun x => sFour c x*(x-fTail c)*x*(x-c)*(1+omegaPoly c*x))
def lMom (c : R) : R := jMom c-2*kMom c*c⁻¹ʳ
def origin (c : R) : R := kMom c+lMom c

def qC (c : R) : R := eTail c*26*kMom c
def qL (c : R) : R := eTail c*26*lMom c
def bPoly (c x : R) : R := (x-c)*(x-26)*(x-eTail c)*tThree c x
def eZero (c : R) : R := avg (fun x => x*(x-1)*bPoly c x)
def eOne (c : R) : R := avg (fun x => x^2*(x-1)*bPoly c x)

def vCubic (c x : R) : R :=
  (75*c^3-108*c^2+45*c-5)
    -3*(175*c^3-244*c^2+97*c-10)*x
    +3*(350*c^3-476*c^2+183*c-18)*x^2
    -15*(42*c^3-56*c^2+21*c-2)*x^3
def cNu (c : R) : R := (1-15)*vCubic c 15

def beta (c : R) : R := vCubic c 0*(tThree c 0)⁻¹ʳ
def headPhi (c x : R) : R := (x-1)*(x-c)*(x-26)*(x-eTail c)*(vCubic c x-beta c*tThree c x)

def hU (c : R) : R := eZero c*15*c^2-2*qC c*c
def hV (c : R) : R := -(eZero c*15*c)-eZero c*c^2+eOne c*c+2*qC c-qL c*c
def hW (c : R) : R := -(eOne c*15*c^2)+qC c*c^2
def hhU (c : R) : R := -(avg (fun x => x*headPhi c x))
def hhV (c : R) : R := avg (fun x => headPhi c x)
def hhW (c : R) : R := avg (fun x => x^2*headPhi c x)

def determinant (c : R) : R := hU c*hhV c-hV c*hhU c
def headSum (c : R) : R := (hV c*hhW c-hW c*hhV c)*(determinant c)⁻¹ʳ
def headProduct (c : R) : R := (hW c*hhU c-hU c*hhW c)*(determinant c)⁻¹ʳ
def headQuadratic (c : R) : Polynomial R := X^2-C (headSum c)*X+C (headProduct c)

end Formulas

section Naturality
variable {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S) [IsLocalHom ρ]

theorem map_avg {f : R → R} {g : S → S} (h : ∀ x, ρ (f x) = g (ρ x)) :
    ρ (avg f) = avg g := by
  simp only [avg, avgRaw, map_mul, map_ringInverse, map_natCast, map_sum, map_intCast, h]

@[simp] theorem map_m (c x : R) : ρ (m c x) = m (ρ c) (ρ x) := by
  unfold m
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_jm (c x : R) : ρ (jm c x) = jm (ρ c) (ρ x) := by
  unfold jm
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_wEarly (c x : R) : ρ (wEarly c x) = wEarly (ρ c) (ρ x) := by
  unfold wEarly
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hDen (c : R) : ρ (hDen c) = hDen (ρ c) := by
  unfold hDen
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hTail (c : R) : ρ (hTail c) = hTail (ρ c) := by
  unfold hTail
  simp only [map_mul, map_ringInverse, map_hDen]
  congr 1
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_sFour (c x : R) : ρ (sFour c x) = sFour (ρ c) (ρ x) := by
  unfold sFour
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_fDen (c : R) : ρ (fDen c) = fDen (ρ c) := by
  unfold fDen
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_fTail (c : R) : ρ (fTail c) = fTail (ρ c) := by
  unfold fTail
  simp only [map_mul, map_ringInverse, map_fDen]
  congr 1
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_omegaPoly (c : R) : ρ (omegaPoly c) = omegaPoly (ρ c) := by
  unfold omegaPoly
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_eDen (c : R) : ρ (eDen c) = eDen (ρ c) := by
  unfold eDen
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_eTail (c : R) : ρ (eTail c) = eTail (ρ c) := by
  unfold eTail
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_tThree (c x : R) : ρ (tThree c x) = tThree (ρ c) (ρ x) := by
  unfold tThree
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_kMom (c : R) : ρ (kMom c) = kMom (ρ c) := by
  unfold kMom
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_jMom (c : R) : ρ (jMom c) = jMom (ρ c) := by
  unfold jMom
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_lMom (c : R) : ρ (lMom c) = lMom (ρ c) := by
  unfold lMom
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_origin (c : R) : ρ (origin c) = origin (ρ c) := by
  unfold origin
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_qC (c : R) : ρ (qC c) = qC (ρ c) := by
  unfold qC
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_qL (c : R) : ρ (qL c) = qL (ρ c) := by
  unfold qL
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_bPoly (c x : R) : ρ (bPoly c x) = bPoly (ρ c) (ρ x) := by
  unfold bPoly
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_eZero (c : R) : ρ (eZero c) = eZero (ρ c) := by
  unfold eZero
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_eOne (c : R) : ρ (eOne c) = eOne (ρ c) := by
  unfold eOne
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_vCubic (c x : R) : ρ (vCubic c x) = vCubic (ρ c) (ρ x) := by
  unfold vCubic
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_cNu (c : R) : ρ (cNu c) = cNu (ρ c) := by
  simp [cNu, map_ofNat]

@[simp] theorem map_beta (c : R) : ρ (beta c) = beta (ρ c) := by
  unfold beta
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_headPhi (c x : R) : ρ (headPhi c x) = headPhi (ρ c) (ρ x) := by
  unfold headPhi
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hU (c : R) : ρ (hU c) = hU (ρ c) := by
  unfold hU
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hV (c : R) : ρ (hV c) = hV (ρ c) := by
  unfold hV
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hW (c : R) : ρ (hW c) = hW (ρ c) := by
  unfold hW
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hhU (c : R) : ρ (hhU c) = hhU (ρ c) := by
  unfold hhU
  simp only [map_neg]
  congr 1
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hhV (c : R) : ρ (hhV c) = hhV (ρ c) := by
  unfold hhV
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_hhW (c : R) : ρ (hhW c) = hhW (ρ c) := by
  unfold hhW
  apply map_avg ρ
  intro y
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_determinant (c : R) : ρ (determinant c) = determinant (ρ c) := by
  unfold determinant
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_headSum (c : R) : ρ (headSum c) = headSum (ρ c) := by
  unfold headSum
  simp [map_ringInverse, map_ofNat]

@[simp] theorem map_headProduct (c : R) : ρ (headProduct c) = headProduct (ρ c) := by
  unfold headProduct
  simp [map_ringInverse, map_ofNat]

theorem map_headQuadratic (c : R) : (headQuadratic c).map ρ = headQuadratic (ρ c) := by
  simp [headQuadratic, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

end Naturality

theorem eval_headQuadratic {R : Type*} [CommRing R] (c x : R) :
    (headQuadratic c).eval x = x^2-headSum c*x+headProduct c := by
  simp [headQuadratic]

theorem eval_derivative_headQuadratic {R : Type*} [CommRing R] (c x : R) :
    (headQuadratic c).derivative.eval x = 2*x-headSum c := by
  simp [headQuadratic, derivative_add, derivative_sub, derivative_mul, one_add_one_eq_two]

end
end RKResearch.Certified.ERK10FixedQ29Adic

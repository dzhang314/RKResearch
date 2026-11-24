module

public import RKCert.ERKOrderNineFixedRadau
public import RKCert.RadauRootCertificates

@[expose] public section

/-! # Fixed-Radau late-column endpoint compatibility in characteristic zero -/
namespace RKCert.Paired
open RKCert.FixedFactor

variable {K : Type*} [Field K] [CharZero K]

theorem fixedRadauCompat_nonzero (w : Fin 4 → K)
    (hr : ∀ i, radauQuartic.eval (w i)=0) (hw : Function.Injective w) :
    fixedRadauCompat (w 0) (w 1) (w 2) (w 3)≠0 := by
  have hc := radau_root_certificate353 fixedRadauCompatibilityTest (·≠·)
    (fun z hmem hdis => by
      change MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 353)) z fixedRadauCompatibilityTest ≠ 0
      rw [fixedRadauCompatibilityTest_eval]
      have hh (i) : z i=41 ∨ z i=111 ∨ z i=161 ∨ z i=320 := by
        simpa [radauKnots353] using hmem i
      exact fixedRadauCompatInt_mod353 _ _ _ _ (hh 0) (hh 1) (hh 2) (hh 3)
        (hdis 0 1 (by decide)) (hdis 0 2 (by decide)) (hdis 0 3 (by decide))
        (hdis 1 2 (by decide)) (hdis 1 3 (by decide)) (hdis 2 3 (by decide)))
    w hr (fun _ _ hij he => hij (hw he))
  change MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i=>126*w i) fixedRadauCompatibilityTest ≠ 0 at hc
  rw [fixedRadauCompatibilityTest_eval] at hc
  change fixedRadauCompatInt (126*w 0) (126*w 1) (126*w 2) (126*w 3)≠0 at hc
  rw [fixedRadauCompatInt_scale] at hc
  exact (mul_ne_zero_iff.mp hc).2

omit [CharZero K] in
theorem fixedRadauF_affine (h u v B : K) :
    fixedRadauF u v (fun x => fixedRadauP0 h x+B*fixedRadauP1 h x) =
      fixedRadauF u v (fixedRadauP0 h)+B*fixedRadauF u v (fixedRadauP1 h) := by
  unfold fixedRadauF
  ring

omit [CharZero K] in
theorem fixedRadauG_affine (h r u v B : K) :
    fixedRadauG r u v (fun x => fixedRadauP0 h x+B*fixedRadauP1 h x) =
      fixedRadauG r u v (fixedRadauP0 h)+B*fixedRadauG r u v (fixedRadauP1 h) := by
  unfold fixedRadauG
  ring

/-- The fixed-five-on scalar gate from the manuscript. It does not
divide by either affine coefficient, and it makes no order assumption
on the field or the four Radau roots. -/
theorem fixedRadau_late_scalar_gate (w : Fin 4 → K) (B : K)
    (hR : ∀ i, radauQuartic.eval (w i)=0) (hW : Function.Injective w)
    (hF : fixedRadauF (w 2) (w 3)
      (fun x => fixedRadauP0 (w 0) x+B*fixedRadauP1 (w 0) x)=0)
    (hG : fixedRadauG (w 1) (w 2) (w 3)
      (fun x => fixedRadauP0 (w 0) x+B*fixedRadauP1 (w 0) x)=0) : False := by
  rw [fixedRadauF_affine] at hF
  rw [fixedRadauG_affine] at hG
  apply fixedRadauCompat_nonzero w hR hW
  unfold fixedRadauCompat
  linear_combination fixedRadauG (w 1) (w 2) (w 3) (fixedRadauP1 (w 0))*hF -
    fixedRadauF (w 2) (w 3) (fixedRadauP1 (w 0))*hG

end RKCert.Paired


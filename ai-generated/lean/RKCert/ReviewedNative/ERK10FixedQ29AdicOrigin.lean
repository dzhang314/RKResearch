module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicResidues
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Clear the actual origin contact without cancelling any branch of
the fixed-q head or tail formula. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic

noncomputable section
open Polynomial
open scoped Ring BigOperators

set_option maxRecDepth 40000
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

theorem avgRaw_congr {f g : R → R} (h : ∀ x, f x = g x) :
    avgRaw f = avgRaw g := congrArg avgRaw (funext h)

theorem avgRaw_scale (r : R) (f : R → R) : avgRaw (fun x => r*f x) = r*avgRaw f := by
  simp only [avgRaw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem avgRaw_add (f g : R → R) :
    avgRaw (fun x => f x+g x) = avgRaw f+avgRaw g := by
  simp only [avgRaw, mul_add, Finset.sum_add_distrib]

theorem paidAvg (h : IsUnit (avgDen : R)) (f : R → R) :
    (avgDen : R)*avg f = avgRaw f := Ring.mul_inverse_cancel_left _ _ h

def hNP (c : R) : R := 6686-22450*c+21150*c^2
def hDP (c : R) : R := 8980-31725*c+32120*c^2
def fNP (c : R) : R := 1051235*c-4965464*c^2+5011025*c^3
def fDP (c : R) : R := 2102470-14896392*c+42748688*c^2-61086000*c^3+36040380*c^4

def w30 (c x : R) : R :=
  (1-x)*(x-6)*(x-15)*(x^3*(10*c^2-15*c*x+6*x^2))

private theorem w30_eq (c x : R) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (h5 : IsUnit (5 : R)) : (30 : R)*wEarly c x = w30 c x := by
  unfold wEarly jm w30
  calc
    _ = (1-x)*(x-6)*(x-15)*
        (x^3*(10*c^2*(3*(3:R)⁻¹ʳ)-15*c*x*(2*(2:R)⁻¹ʳ)+6*x^2*(5*(5:R)⁻¹ʳ))) := by ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ h3, Ring.mul_inverse_cancel _ h2,
      Ring.mul_inverse_cancel _ h5]; ring

private theorem h_raw_num (c : R) : avgRaw (fun x => x*w30 c x) = 8640*hNP c := by
  norm_num [avgRaw, w30, hNP, Fin.sum_univ_succ, avgNumerator] <;> ring

private theorem h_raw_den (c : R) : avgRaw (fun x => w30 c x) = 8640*hDP c := by
  norm_num [avgRaw, w30, hDP, Fin.sum_univ_succ, avgNumerator] <;> ring

private theorem unit_8640 (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (h5 : IsUnit (5 : R)) :
    IsUnit (8640 : R) := by
  have H := ((h2.pow 6).mul (h3.pow 3)).mul h5
  convert H using 1 <;> norm_num

private theorem unit_n2880 (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) (h5 : IsUnit (5 : R)) :
    IsUnit (-2880 : R) := by
  have H := (((h2.pow 6).mul (h3.pow 2)).mul h5).neg
  convert H using 1 <;> norm_num

theorem h_clear (c : R) (pay : PaidHead c) : hDP c*hTail c = hNP c := by
  obtain ⟨hD,h2,h3,h5,_,hh,_,_,_,_,_⟩ := pay
  have hd : (30*(avgDen:R))*hDen c = 8640*hDP c := by
    rw [mul_assoc, hDen, paidAvg hD, ← avgRaw_scale, ← h_raw_den]
    exact avgRaw_congr (fun x => w30_eq c x h2 h3 h5)
  have hn : (30*(avgDen:R))*avg (fun x => x*wEarly c x) = 8640*hNP c := by
    rw [mul_assoc, paidAvg hD, ← avgRaw_scale, ← h_raw_num]
    exact avgRaw_congr (fun x => by
      rw [mul_left_comm, w30_eq c x h2 h3 h5])
  have he : hDen c*hTail c = avg (fun x => x*wEarly c x) := by
    unfold hTail
    rw [mul_left_comm, Ring.mul_inverse_cancel _ hh, mul_one]
  apply (unit_8640 h2 h3 h5).mul_left_cancel
  rw [←mul_assoc, ←hd, mul_assoc, he, hn]

def s4scaled (c x : R) : R := (1-x)*(x-6)*(x*hDP c-hNP c)*(x-15)

private theorem s4scaled_eq (c x : R) (h : hDP c*hTail c = hNP c) :
    hDP c*sFour c x = s4scaled c x := by
  unfold sFour s4scaled
  rw [← h]; ring

private theorem f_raw_den (c : R) : avgRaw (fun x => s4scaled c x*m c x) = -2880*fDP c := by
  norm_num [avgRaw, s4scaled, hDP, hNP, m, fDP, Fin.sum_univ_succ, avgNumerator] <;> ring

private theorem f_raw_num (c : R) :
    avgRaw (fun x => s4scaled c x*x*m c x) = -2880*fNP c := by
  norm_num [avgRaw, s4scaled, hDP, hNP, m, fNP, Fin.sum_univ_succ, avgNumerator] <;> ring

theorem f_clear (c : R) (pay : PaidHead c) : fDP c*fTail c = fNP c := by
  have H := h_clear c pay
  obtain ⟨hD,h2,h3,h5,_,_,hf,_,_,_,_⟩ := pay
  have hd : (hDP c*(avgDen:R))*fDen c = -2880*fDP c := by
    rw [mul_assoc, fDen, paidAvg hD, ← avgRaw_scale, ← f_raw_den]
    exact avgRaw_congr (fun x => by rw [←mul_assoc, s4scaled_eq c x H])
  have hn : (hDP c*(avgDen:R))*avg (fun x => sFour c x*x*m c x) = -2880*fNP c := by
    rw [mul_assoc, paidAvg hD, ← avgRaw_scale, ← f_raw_num]
    exact avgRaw_congr (fun x => by rw [←mul_assoc, ←mul_assoc, s4scaled_eq c x H])
  have he : fDen c*fTail c = avg (fun x => sFour c x*x*m c x) := by
    unfold fTail
    rw [mul_left_comm, Ring.mul_inverse_cancel _ hf, mul_one]
  apply (unit_n2880 h2 h3 h5).mul_left_cancel
  rw [←mul_assoc, ←hd, mul_assoc, he, hn]

def originRaw (c h f x : R) : R :=
  (x-1)*x*(x-c)*(x-6)*(x-15)*(x-h)*(x-f)*
    ((c-2-c*omegaPoly c)*x-c*(c-1))

def originScaled (c x : R) : R :=
  (x-1)*x*(x-c)*(x-6)*(x-15)*(x*hDP c-hNP c)*(x*fDP c-fNP c)*
    ((c-2-c*omegaPoly c)*x-c*(c-1))

private theorem origin_raw_eq (c : R) (hD : IsUnit (avgDen:R)) (hc : IsUnit c) :
    (avgDen:R)*(c*origin c) = avgRaw (fun x => originRaw c (hTail c) (fTail c) x) := by
  have hco : c*origin c = c*jMom c+(c-2)*kMom c := by
    unfold origin lMom
    calc
      _ = c * kMom c + c*jMom c - 2*kMom c*(c*c⁻¹ʳ) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel c hc]; ring
  rw [hco, mul_add, mul_left_comm (avgDen:R) c, mul_left_comm (avgDen:R) (c-2),
    jMom, kMom, paidAvg hD, paidAvg hD, ← avgRaw_scale, ← avgRaw_scale, ← avgRaw_add]
  apply avgRaw_congr
  intro x
  unfold originRaw sFour tThree
  ring

private theorem origin_polynomial_raw (c : R) :
    avgRaw (fun x => originScaled c x) = -2880*(decic R).eval c := by
  rw [decic, eval_intPolynomial]
  norm_num [avgRaw, originScaled, omegaPoly, hDP, hNP, fDP, fNP,
    Fin.sum_univ_succ, avgNumerator, intJet, decicCoeffs] <;> ring

/-- The exact scalar cofactor identity over any commutative ring with
the actual required units, without assuming a priori that the decic
is related to the physical integrals. -/
theorem origin_clear (c : R) (pay : PaidHead c) :
    (avgDen:R)*c*hDP c*fDP c*origin c = -2880*(decic R).eval c := by
  have heh := h_clear c pay
  have hef := f_clear c pay
  have H0 := origin_raw_eq c pay.1 pay.2.2.2.2.1
  calc
    _ = (hDP c*fDP c)*((avgDen:R)*(c*origin c)) := by ring
    _ = avgRaw (fun x => (hDP c*fDP c)*originRaw c (hTail c) (fTail c) x) := by
      rw [H0, avgRaw_scale]
    _ = avgRaw (fun x => originScaled c x) := by
      apply avgRaw_congr
      intro x
      unfold originScaled originRaw
      rw [← heh, ← hef]; ring
    _ = _ := origin_polynomial_raw c

theorem hDP_residue : hDP (2:F) = 2 := by unfold hDP; decide +kernel
theorem fDP_residue : fDP (2:F) = 17 := by unfold fDP; decide +kernel

/-- The selected root makes the true origin residual vanish, not only its
formal reduction or a canceled substitute. -/
theorem origin_zero_of_decic (ρ : R →+* F) [IsLocalHom ρ] {c : R}
    (hr : ρ c = 2) (hc : (decic R).eval c = 0) : origin c = 0 := by
  obtain hP := paidHead_of_residue ρ hr
  have hh : IsUnit (hDP c) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    simp only [hDP, map_add, map_sub, map_pow, map_mul, map_ofNat, hr]
    decide +kernel
  have hf : IsUnit (fDP c) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    simp only [fDP, map_add, map_sub, map_pow, map_mul, map_ofNat, hr]
    decide +kernel
  have hp := ((hP.1.mul hP.2.2.2.2.1).mul hh).mul hf
  apply hp.mul_left_cancel
  rw [origin_clear c hP, hc, mul_zero, mul_zero]

end
end RKResearch.Certified.ERK10FixedQ29Adic

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.origin_clear
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.origin_zero_of_decic

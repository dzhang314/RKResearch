module

public import RKCert.CompanionPaidMoment
public import RKCert.DirkTrace

@[expose] public section

/-! # Integer-denominator clearing for normalized paid primitives

The same scale may be used in three successive moments. In particular
a Gram identity is unaffected by the common scale and by the precise
powers of the actual nonzero integration endpoint. -/
namespace RKCert.Compound
open Polynomial RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Integral clearing is chosen before any coefficient-ring map. -/
def scaledMoment (M j d : ℕ) (u : R) (P : R[X]) : R :=
  ∑ r : Fin (d+1), ((M/(j+r.val+1):ℕ):R)*u^r.val*P.coeff r.val

theorem scaledMoment_map (f : R→+*S) (M j d : ℕ) (u : R) (P : R[X]) :
    f (scaledMoment M j d u P)=scaledMoment M j d (f u) (P.map f) := by
  simp only [scaledMoment,map_sum,map_mul,map_natCast,map_pow,coeff_map]

variable {K : Type*} [Field K] [CharZero K]

theorem scaledMoment_agrees (M j d : ℕ) (u : K) (P : K[X]) (hd : P.natDegree≤d)
    (divides : ∀ r : Fin (d+1),j+r.val+1∣M) :
    u^(j+1)*scaledMoment M j d u P=(M:K)*paidMoment P u j := by
  unfold paidMoment scaledMoment
  rw [RKCert.Paired.primitive_eval_power_mul P u j hd,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have den : ((j+i.val+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have eq : ((M/(j+i.val+1):ℕ):K) * ((j+i.val+1:ℕ):K)=(M:K) := by
    exact_mod_cast Nat.div_mul_cancel (divides i)
  rw [←mul_div_assoc,eq_div_iff den,←eq,show j+i.val+1=(j+1)+i.val by omega,pow_add]
  ring

theorem scaledMoment_eq_scale (M j d : ℕ) (u : K) (hu : u≠0) (P : K[X])
    (hd : P.natDegree≤d) (divides : ∀ r : Fin (d+1),j+r.val+1∣M) :
    scaledMoment M j d u P=((M:K)/u^(j+1))*paidMoment P u j := by
  apply mul_left_cancel₀ (pow_ne_zero _ hu)
  rw [scaledMoment_agrees M j d u P hd divides]
  field_simp [hu]

/-- Sufficient integer scale for all the specified adjacent moments. -/
theorem factorial_scale_clears {B j d : ℕ} (h : j+d+1≤B) (i : Fin (d+1)) :
    j+i.val+1∣B.factorial :=
  Nat.dvd_factorial (by omega) (by have _ := i.isLt; omega)

end
end RKCert.Compound

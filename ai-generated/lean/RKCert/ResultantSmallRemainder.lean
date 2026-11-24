module

public import RKCert.DirkResultantTransfer
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

/-! # Exact narrow-matrix computation for high-degree parameter resultants

Evaluating the parameter may leave a high-degree first polynomial, but
the resultant only needs its remainder modulo the small monic pencil.
The explicit degree-offset sign is retained for the pinned Mathlib
Sylvester convention. -/
namespace RKCert.FixedPolynomial
open Polynomial
open scoped Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

theorem parameterNorm_eval₂ (f : R→+*S) (F H L : R[X]) (m n : ℕ) (a : S) :
    (parameterNorm F H L m n).eval₂ f a=
      (F.map f).resultant (H.map f+C a*L.map f) m n := by
  let ψ := eval₂RingHom f a
  have hc : ψ.comp (C : R→+*R[X])=f := eval₂RingHom_comp_C _ _
  have hp : (parameterPencil H L).map ψ=H.map f+C a*L.map f := by
    rw [parameterPencil,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
      Polynomial.map_map,Polynomial.map_map,hc]
    simp [ψ]
  have hF : (F.map (C : R→+*R[X])).map ψ=F.map f := by rw [Polynomial.map_map,hc]
  change ψ ((F.map (C : R→+*R[X])).resultant (parameterPencil H L) m n)=_
  rw [←resultant_map_map,hF,hp]

variable {K : Type*} [Field K]

theorem resultant_remainder_of_monic (F G : K[X]) {m n : ℕ} (hF : F.natDegree≤m)
    (mG : G.Monic) (hG : G.natDegree=n) (n0 : 0<n) (nm : n≤m) :
    F.resultant G m n=(-1:K)^(n*(m-(n-1)))*(F %ₘ G).resultant G (n-1) n := by
  have dep : (F /ₘ G).natDegree+n≤m := by
    rw [natDegree_divByMonic _ mG,hG]
    omega
  have ch := resultant_add_mul_left (F %ₘ G) G (F /ₘ G) m n dep hG.le
  rw [modByMonic_add_div] at ch
  have nontriv : G≠1 := fun he => by rw [he,natDegree_one] at hG; omega
  have rd := (natDegree_modByMonic_lt F mG nontriv).trans_le hG.le
  have dc : G.coeff n=1 := hG ▸ mG.coeff_natDegree
  have extd := resultant_add_left_deg (F %ₘ G) G (n-1) n (m-(n-1))
    (show (F %ₘ G).natDegree≤n-1 by omega)
  rw [show n-1+(m-(n-1))=m by omega,dc,one_pow,mul_one] at extd
  exact ch.trans extd

theorem resultant_small_remainder (F G : K[X]) {m n : ℕ} (hF : F.natDegree≤m)
    (g0 : G≠0) (hG : G.natDegree=n) (n0 : 0<n) (nm : n≤m) :
    F.resultant G m n=G.leadingCoeff^m*((-1:K)^(n*(m-(n-1)))*
      (F %ₘ normalize G).resultant (normalize G) (n-1) n) := by
  have l0 := leadingCoeff_ne_zero.mpr g0
  have Gnorm : C G.leadingCoeff * normalize G=G := by
    rw [normalize_apply,coe_normUnit_of_ne_zero g0]
    calc
      _ = G*(C G.leadingCoeff*C G.leadingCoeff⁻¹) := by ring
      _ = G := by rw [←map_mul,mul_inv_cancel₀ l0,map_one,mul_one]
  have nd : (normalize G).natDegree=n := natDegree_normalize.trans hG
  calc
    _ = G.leadingCoeff^m*F.resultant (normalize G) m n := by
      rw [←resultant_C_mul_right,Gnorm]
    _ = _ := by rw [resultant_remainder_of_monic F _ hF (monic_normalize g0) nd n0 nm]

end
end RKCert.FixedPolynomial

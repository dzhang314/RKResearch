module

public import RKCert.PencilDividedDifference

@[expose] public section

/-! # Integer-symbolic divided differences commute with field evaluation -/
namespace RKCert.FixedPolynomial
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R] {K : Type*} [Field K]

/-- Outer variable is the companion coordinate. The coefficient variable
is the actual omitted clock. This makes no commitment about which value
that clock takes in a candidate array. -/
def universalOmission (H L : R[X]) : R[X][X] :=
  (C L*H.map (C:R→+*R[X])-C H*L.map (C:R→+*R[X])) /ₘ (X-C (X:R[X]))

theorem universalOmission_specializes (H L : R[X]) (f : R→+*K) (u : K) :
    (universalOmission H L).map (eval₂RingHom f u)=
      omittedDifference (H.map f) (L.map f) u := by
  let q := eval₂RingHom f u
  have hc : q.comp (C : R→+*R[X])=f := eval₂RingHom_comp_C _ _
  have eq (P : R[X]) : (P.map (C:R→+*R[X])).map q=P.map f := by
    rw [Polynomial.map_map,hc]
  have eqP (P : R[X]) : q P=(P.map f).eval u := by
    change P.eval₂ f u=_
    rw [eval_map]
  have lux : q (X:R[X])=u := by simp [q]
  change (universalOmission H L).map q=omittedDifference (H.map f) (L.map f) u
  unfold universalOmission omittedDifference
  rw [map_divByMonic q (monic_X_sub_C (X:R[X]))]
  simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    eq,eqP H,eqP L,lux]

theorem universalOmission_coeff_specializes (H L : R[X]) (f : R→+*K) (u : K) (j : ℕ) :
    ((universalOmission H L).coeff j).eval₂ f u =
      (omittedDifference (H.map f) (L.map f) u).coeff j := by
  rw [←universalOmission_specializes,coeff_map]
  rfl

end
end RKCert.FixedPolynomial

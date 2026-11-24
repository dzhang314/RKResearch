module

public import RKCert.ERKOrderNineOneOffTailIdentities
public import RKCert.ERKOrderNineCompactPrime

@[expose] public section

/-! # Order nine requires thirteen explicit stages over an ordered field -/
namespace RKCert.Paired

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The remaining physical one-off branch is impossible. Its terminal
polynomial is a cubic or a quartic pencil; both feed the independently
verified reflected-moment collisions. -/
theorem order9_one_off_impossible {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (OneOff.g A)).card=1) : False := by
  obtain ⟨a,d,i,j,D,F⟩ := OneOff.order9_first_four ha ho oneOff
  let z := nodes A (5:Fin 12)
  let f := OneOff.Seven.physicalTail A a d z
  have D7 := OneOff.Seven.order9_two_fibres ha ho oneOff D F
  obtain ⟨uη,κ,lam,τ₀,τ₁,af,av⟩ := OneOff.Seven.order9_actual_tail_identities ha ho oneOff D F D7
  have hf := OneOff.Seven.physicalTail_defect A a d z
  obtain ⟨rk,_,_,_⟩ := OneOff.order9_maximal_normal_profile ha ho oneOff D F
  have endClock := (order9_rank_five_full ha ho rk).2.1
  have sixth := OneOff.order9_sixth_feature ha ho oneOff D F
  have z0 : z≠0 := sixth.2.1
  have zt : z≠2*d := sixth.2.2.2.1
  rcases OneOff.Seven.endBeta_alternatives d z D.base.dn z0 D7.pz D7.pd D7.endpoint.p1 with
      ⟨ht,hz,hd,h1⟩|⟨l,ht,hz,hd,h1⟩
  · exact OneOff.order9_tail_cubic_impossible ho hf endClock zt ht hz hd h1 af
  · exact OneOff.order9_tail_quartic_impossible ho hf endClock uη zt ht hz hd h1 af av

/-- No sign, separation, or nonvanishing assumptions on the tableau:
a strictly lower triangular RK tableau satisfying all through-order-nine
rooted-tree conditions over an ordered field has at least thirteen stages. -/
theorem explicit_order_nine_at_least_thirteen {s : ℕ}
    {A : Fin s→Fin s→K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) : 13≤s := by
  have hlo := uniform_erk_field ha ho
  by_contra! hs
  have e : s=12 := by omega
  subst s
  exact order9_one_off_impossible ha ho (order9_only_one_off ha ho)

end RKCert.Paired

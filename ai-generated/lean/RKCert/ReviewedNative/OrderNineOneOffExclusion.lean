module
public import RKCert.ReviewedNative.OneOffTailIdentities
public import RKCert.ReviewedNative.OneOffOrderedTailPayment

@[expose] public section

/-! # The original reviewed order-nine one-off chart is impossible -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module Polynomial Seven
open scoped Matrix Classical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

/-- The actual twelve-stage one-off branch is excluded over an ordered
field. Its entire tableau and all its order witnesses are native. -/
theorem order9_one_off_impossible (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 9 A b) (off : (offKnots A).card=1) : False := by
  obtain ⟨a,d,i,j,D,F,D7⟩ := order9_one_off_two_fibres ha ho off
  let z := nodes A (5:Fin 12)
  let f := physicalTail A a d z
  obtain ⟨uη,κ,lam,τ₀,τ₁,af,av⟩ := order9_actual_tail_identities ha ho D F D7
  have hf := physicalTail_defect A a d z
  obtain ⟨rk,_,_,_⟩ := order9_maximal_normal_profile ha ho D F
  have endClock := (order9_rank_five_full_terminal ha ho rk).2.1
  have sixth := order9_sixth_feature ha ho D F
  have z0 : z≠0 := sixth.2.1
  have zt : z≠2*d := sixth.2.2.2.1
  rcases endBeta_alternatives d z D.base.dn z0 D7.pz D7.pd D7.endpoint.p1 with
      ⟨ht,hz,hd,h1⟩|⟨l,ht,hz,hd,h1⟩
  · exact tail_cubic_impossible ho hf endClock zt ht hz hd h1 af
  · exact tail_quartic_impossible ho hf endClock uη zt ht hz hd h1 af av

/-- Stage-floor dispatch for the one-off class, without an assumed
twelve-stage shape. The multi-off census is a separate statement. -/
theorem explicit_order_nine_one_off_at_least_thirteen {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 9 A b)
    (off : (offKnots A).card=1) : 13≤s := by
  by_contra! small
  have e := (order9_forward_chart ha ho (by omega)).1
  subst s
  exact order9_one_off_impossible ha ho off

end RKResearch.Certified.Graded.OneOff

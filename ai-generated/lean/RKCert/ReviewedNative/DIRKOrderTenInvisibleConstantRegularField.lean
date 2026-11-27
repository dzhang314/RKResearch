module

public import Lean

@[expose] public section

/-! The literal middle-row cancellations making the two lifted quartic
cuts. Pure field algebra; the ambient grade and tableau hypotheses are
supplied in the companion mathematical proof. -/
namespace RKResearch.Certified.Graded.InvisibleConstantRegularField

open Lean.Grind
variable {F : Type} [Field F]

private theorem cancel (d z : F) (hd : d ≠ 0) (h : d*z=0) : z=0 := by
  have h' := congrArg (fun w => d⁻¹*w) h
  rw [←Semiring.mul_assoc, Field.inv_mul_cancel hd, Semiring.one_mul, Semiring.mul_zero] at h'
  exact h'

private theorem mulNe (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 := by
  intro h
  exact hb (cancel a b ha h)

/-- The forward or reverse gap-two Volterra equation supplies its
nonzero middle primitive and the lifted-cut coefficient. -/
theorem gap_two_middle (d delta p f v : F)
    (hd : d≠0) (hdelta : delta≠0) (hp : p≠0) (hf : f≠0)
    (h : p*(delta-d)*f=d*d*v) :
    (p*f+d*v≠0) ∧ delta*v+(1-delta/d)*(p*f+d*v)=0 := by
  have hscale : d*(p*f+d*v)=p*delta*f := by grind
  constructor
  · intro hz
    rw [hz,Semiring.mul_zero] at hscale
    exact mulNe _ _ (mulNe _ _ hp hdelta) hf hscale.symm
  · apply cancel d _ hd
    have hi := Field.mul_inv_cancel hd
    simp only [Field.div_eq_mul_inv]
    grind

/-- Same scalar equation in the reverse profile, with x−w instead of
x−u as the multiplier of the lifted mark. -/
theorem reverse_lift (d delta q r b : F)
    (hd : d≠0) (hdelta : delta≠0) (hq : q≠0) (hr : r≠0)
    (h : q*(delta-d)*r=d*d*b) :
    (q*r+d*b≠0) ∧ -delta*b+(delta/d-1)*(q*r+d*b)=0 := by
  obtain ⟨hn,hk⟩ := gap_two_middle d delta q r b hd hdelta hq hr h
  exact ⟨hn, by grind⟩

/-- The front coefficient comparison reduces to one cubic, without
taking an inverse of the primitive coefficient sigma. -/
theorem front_cubic_clear (c42 u k B N E r e sigma lam w : F)
    (h₁ : lam*r=sigma*w)
    (h₂ : c42*lam=(k-1)*B-sigma)
    (h₃ : lam*e= -u+(k-1)*N+sigma*w*k)
    (h₄ : sigma*k=1+(k-1)*E) :
    c42*k*(-u+(k-1)*N)+(r*k-e)*(k*(k-1)*B-(1+(k-1)*E))=0 := by
  have hL : k*(k-1)*B-(1+(k-1)*E)=c42*k*lam := by grind
  rw [hL]
  have hmid : -u+(k-1)*N+(r*k-e)*lam=0 := by grind
  calc
    _ = (c42*k)*(-u+(k-1)*N+(r*k-e)*lam) := by grind
    _ = 0 := by rw [hmid, Semiring.mul_zero]

end RKResearch.Certified.Graded.InvisibleConstantRegularField

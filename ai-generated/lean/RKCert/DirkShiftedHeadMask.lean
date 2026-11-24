module
public import RKCert.DirkPhysicalHeadFactor
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
variable {K : Type*} [Field K] [CharZero K] {s m j : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b w : Vec K (s+1)} {P : K[X]}

/-- Apply the original head-factor pivot at exactly the grade where the
shifted numerical mask is paid. In particular cw paid in F₅ at p14/r=2
does not cost a spurious extra grade. -/
theorem no_shifted_lobatto_factor_mask (hm : m=7 ∨ m=8)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (fact : P∣lobatto m) (dP : (X*P).natDegree≤j) (pay : j+2≤m)
    (hw : w∈zeroSpace A j)
    (mask : ∀ i, (∃ f∈zeroSpace A m, f i≠0) → w i=nodes A i*P.eval (nodes A i)) : False := by
  have tr := (OrdinaryTrace.scalar A dP).sub_pure hw
  apply no_clean_head_lobatto_factor hm ha ho he tr pay fact
  intro i act f hf
  by_contra hn
  apply act
  simp [mask i ⟨f,hf,hn⟩]

end RKCert.Paired.Terminal

import RKCert.ReviewedNative.AffineLowerOffReceiverDonors

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.EffectiveDonors
open scoped Matrix
noncomputable section
variable {K : Type*} [Field K] {s m : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {l : Fin s→K}
variable {x γ : K} {cut : Fin s}

/-- The inclusive odd-order prefix preserves the nonzero common
SDIRK diagonal and pays m nonzero earlier donor clocks off x. -/
theorem audit_inclusive_sdirk_odd
    (P : ClockAffineProbe A l x cut)
    (lower : ∀ i j,i<j→A i j=0) (diag : ∀ i,A i i=γ) (gamma : γ≠0)
    (nz : x≠0) (lastLive : l cut≠0)
    (paid : ∀ v∈zeroSpace A (2*m+1), row l v=0) :
    HasOrder (2*m+1) (x⁻¹ • prefixMatrix A (Nat.succ_le_of_lt cut.isLt))
      (fun j : Fin (cut.val+1) => x⁻¹*affineReceiverRow A l
        (Fin.castLE (Nat.succ_le_of_lt cut.isLt) j)) ∧
    (∀ i : Fin (cut.val+1),
      (x⁻¹ • prefixMatrix A (Nat.succ_le_of_lt cut.isLt)) i i=x⁻¹*γ ∧
      (x⁻¹ • prefixMatrix A (Nat.succ_le_of_lt cut.isLt)) i i≠0) ∧
    m≤(offReceiverSites
      (fun j : Fin cut.val=>nodes A (Fin.castLE cut.isLt.le j))
      (fun j : Fin cut.val=>affineReceiverRow A l (Fin.castLE cut.isLt.le j)) x 1).card := by
  refine ⟨P.prefix_hasOrder_inclusive_of_lower lower nz _ paid,?_,?_⟩
  · intro i
    have same := scaled_prefix_constant_diagonal (Nat.succ_le_of_lt cut.isLt) x⁻¹ diag i
    refine ⟨same,?_⟩
    rw [same]
    exact mul_ne_zero (inv_ne_zero nz) gamma
  · exact P.lower_offReceiver_donor_count lower nz lastLive _ paid (n:=m) (e:=1) le_rfl

theorem audit_exclusive_strict_cut (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (nz : x≠0) (q : ℕ)
    (paid : ∀ v∈zeroSpace A q,row l v=0) :
    HasOrder q (x⁻¹ • prefixMatrix A cut.isLt.le)
      (fun j : Fin cut.val=>x⁻¹*affineReceiverRow A l (Fin.castLE cut.isLt.le j)) :=
  P.prefix_hasOrder_exclusive_of_lower_of_self_zero (fun i j ij=>strict i j ij.le)
    (by rw [strict cut cut le_rfl,mul_zero]) nz q paid

#print axioms RKResearch.Certified.Graded.ClockAffineProbe.prefix_hasOrder_inclusive_of_lower
#print axioms RKResearch.Certified.Graded.ClockAffineProbe.prefix_hasOrder_exclusive_of_lower_of_self_zero
#print axioms RKResearch.Certified.Graded.EffectiveDonors.off_one_cover_card_of_hasOrder
#print axioms RKResearch.Certified.Graded.ClockAffineProbe.lower_offReceiver_donor_count
#print axioms audit_inclusive_sdirk_odd
#print axioms audit_exclusive_strict_cut

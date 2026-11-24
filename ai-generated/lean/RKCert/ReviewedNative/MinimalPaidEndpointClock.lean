module

public import RKCert.ReviewedNative.PaidEndpointClock
public import RKCert.ReviewedNative.MinimalDefectClean

@[expose] public section

/-! # Clean clocks at a minimally ranked paid endpoint

The grade-three chain is an explicit conditional premise.
There is no stage count or reverse-rank hypothesis. The conclusions count
numerical clocks of actual rows, without selecting or merging a tableau.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p q : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {b : Fin (s+1)→K} {t : Fin (s+1)}

/-- A set consists of distinct nonzero clocks, each with a literal
off-endpoint representative whose actual quadratic defect is zero. -/
def OffEndpointQuadraticClockCover
    (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (t : Fin (s+1)) (S : Finset K) : Prop :=
  ∀ x∈S, x≠0 ∧ ∃ i : Fin (s+1), i≠t ∧ nodes A i=x ∧ monomialStageDefect A 1 i=0

structure MinimalPaidEndpointClockBounds
    (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (q : ℕ) (t : Fin (s+1)) : Prop where
  inside : ∀ {i : Fin (s+1)}, i≠t → nodes A i≠0 → monomialStageDefect A 1 i=0 →
    nodes A i∈Set.Ioo (0:K) 1
  count : ∀ S : Finset K, OffEndpointQuadraticClockCover A t S → S.card≤q-1

/-- At a paid even midpoint with the stated minimal rank and grade-three
base, every nonzero
off-coordinate quadratic-clean clock is interior, and at most q-1
distinct such clocks can occur. The paid coordinate need not be last. -/
theorem minimal_paid_endpoint_clock_bounds
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (q₂ : 2≤q) (q₁₀ : q≤10) (pay : 2*q≤p)
    (defectRank : finrank K (zeroSpace A q)=q-1)
    (baseF3 : 3≤q → zeroSpace A 3=
      RKCert.OneEscape.chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) 2)
    (one : nodes A t=1) (live : b t≠0)
    (coord : coordinate (K:=K) t∈treeSpace A q) :
    MinimalPaidEndpointClockBounds A q t := by
  obtain ⟨J,H⟩ := paid_endpoint_clock_of_coordinate ha ho q₂ q₁₀ pay one live coord
  have clean (i : Fin (s+1)) (gz : monomialStageDefect A 1 i=0) :
      ∀ f∈zeroSpace A q, f i=0 :=
    (minimal_defect_clean_iff_quadratic_zero (j:=q) ha ho pay defectRank baseF3 q₂ le_rfl i).mpr gz
  refine ⟨?_,?_⟩
  · intro i off cn gz
    exact H.clean_clock_interior off cn (clean i gz)
  · intro S actual
    apply H.clean_clock_card_le S
    intro x hx
    obtain ⟨xn,i,off,cx,gz⟩ := actual x hx
    exact ⟨xn,i,off,cx,clean i gz⟩

/-- Either a single exterior nonzero clean clock or q distinct
nonzero clean clocks off the given coordinate is an obstruction. -/
theorem MinimalPaidEndpointClockBounds.false_of_exterior_or_excess
    (H : MinimalPaidEndpointClockBounds A q t) (positive : 0<q)
    (bad : (∃ i : Fin (s+1), i≠t ∧ nodes A i≠0 ∧ monomialStageDefect A 1 i=0 ∧
        nodes A i∉Set.Ioo (0:K) 1) ∨
      ∃ S : Finset K, OffEndpointQuadraticClockCover A t S ∧ q≤S.card) : False := by
  rcases bad with ⟨i,off,cn,gz,outside⟩ | ⟨S,actual,many⟩
  · exact outside (H.inside off cn gz)
  · have few := H.count S actual
    omega

end
end RKResearch.Certified.Graded.Reverse

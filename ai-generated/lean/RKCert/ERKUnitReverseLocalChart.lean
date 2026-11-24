module
public import RKCert.ERKLocalizedReverseReusable

@[expose] public section

/-! # Transfer the already-audited localized reverse chronology.

The four exact reverse ranks and degree payments are the input. The
original order-twelve case is one specialization, not an assumption on
the array in a higher order. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.OrderTwelve RKCert.OneEscape Module
open scoped Classical
variable {K:Type*} [Field K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

structure UnitFirstFour (A:Fin s→Fin s→K) (b:Vec K s) : Prop where
  zero : backSeed1 A b=0
  rank : ∀ n≤4,finrank K (back A b n)=n
  clock2 : ¬(back A b 2).map (diag (mirror A))≤back A b 2
  clock3 : ¬(back A b 3).map (diag (mirror A))≤back A b 3
  cubic : reverseResidual A b 2∈back A b 2
  quartic : reverseResidual A b 3∈back A b 3

variable [CharZero K]

/-- Paid complementary ordinary ranks give all the first four actual
reverse conditions, including the two noninvariant steps. -/
theorem unit_first_four_of_exact (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (hp:10≤p)
    (zero:backSeed1 A b=0) (rank:∀n≤4,finrank K (back A b n)=n)
    (exactBand:∀n,1≤n→n≤4→back A b n=annih (treeSpace A (p-2-n))) :
    UnitFirstFour A b := by
  have non (n:ℕ) (lo:2≤n) (hi:n≤3) :
      ¬(back A b n).map (diag (mirror A))≤back A b n := by
    intro inv
    have ymask:RKCert.Endpoint.MaskInvariant (mirror A) (back A b n):=by
      intro a v hv
      exact Clock.fiber_mem inv a hv
    have a:p-3-n+1=p-2-n:=by omega
    have b:p-3-n=p-2-(n+1):=by omega
    have dp:=back_mask_rank_jump ha ho (p-3-n) n (by omega)
      (by rw [a,exactBand n (by omega) (by omega)])
      (by rw [b,←exactBand (n+1) (by omega) (by omega)]) ymask
    rw [rank n (by omega),rank (n+1) (by omega)] at dp
    omega
  refine ⟨zero,rank,non 2 (by decide) (by decide),non 3 (by decide) (by decide),?_,?_⟩
  · rw [exactBand 2 (by decide) (by decide)]
    exact reverseResidual_mem ho (by decide) (by omega)
  · rw [exactBand 3 (by decide) (by decide)]
    exact reverseResidual_mem ho (by decide) (by omega)

/-- Reuse the checked localized-row backend at the actual early budgets. -/
theorem unit_back_one_noninvariant {t:ℕ} {A:Fin (t+1)→Fin (t+1)→K} {b:Vec K (t+1)}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (hp:10≤p) (G:UnitFirstFour A b) :
    ¬(back A b 1).map (diag (mirror A))≤back A b 1 := by
  intro inv
  have ch:=localized_reverse_chart_of_ranks ha ho (by omega) G.zero G.rank
    G.clock2 G.clock3 G.cubic G.quartic inv
  exact localized_reverse_rows_impossible ha ho hp
    (localized_reverse_rows_of_chart ha ho (by omega) G.zero ch)

/-- One nonzero quadratic-defect site alone would make the entire
first reverse line invariant, so it cannot survive the actual cut. -/
theorem unit_no_single_reverse_site {t:ℕ} {A:Fin (t+1)→Fin (t+1)→K} {b:Vec K (t+1)}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:10≤p) (G:UnitFirstFour A b) :
    (Clock.headSites (mirror A) (backSeed2 A b)).card≠1 := by
  classical
  intro one
  apply unit_back_one_noninvariant ha ho hp G
  let d:=backSeed2 A b
  let y:=mirror A
  have z:back A b 0=⊥:=Submodule.finrank_eq_zero.mp (G.rank 0 (by decide))
  have l:back A b 1=K∙d:=by
    change back A b 0⊔(back A b 0).map (transMat A)⊔(back A b 0).map (diag y)⊔(K∙d)=K∙d
    simp [z]
  obtain ⟨a,eq⟩:=Finset.card_eq_one.mp one
  have e:diag y d=a • d:=by
    ext i
    by_cases q:d i=0
    · simp [q]
    · have t:=Clock.headSites_mem (c:=y) i q
      change y i∈Clock.headSites (mirror A) (backSeed2 A b) at t
      rw [eq,Finset.mem_singleton] at t
      simp [t]
  rw [l,Submodule.map_span,Set.image_singleton,e]
  exact (Submodule.span_singleton_le_iff_mem ..).mpr
    ((K∙d).smul_mem a (Submodule.mem_span_singleton_self d))

end RKCert.Paired.ReverseHull

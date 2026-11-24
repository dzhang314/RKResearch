module

public import RKCert.ERKOrderNineCompactFactorization
public import RKCert.ERKOrderNineCensus

@[expose] public section

/-! The characteristic-zero six-on atlas and its actual ordered-tableau consequence.
The independent one-off atlas is not part of this exclusion. -/
namespace RKCert.CompactResidue

open Polynomial RKCert.GoodPrimeDense RKCert.Paired RKCert.FixedFactor

theorem rows_checked {S : NatSelectorDatum 1319} (mem : S∈primeRows) :
    S.Checked 581 ∨ TapeChecked S 581 := by
  simp only [primeRows,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inl NatRow0.checked
  · exact Or.inl NatRow1.checked
  · exact Or.inl NatRow2.checked
  · exact Or.inl NatRow3.checked
  · exact Or.inl NatRow4.checked
  · exact Or.inl NatRow5.checked
  · exact Or.inr Row6.checked
  · exact Or.inr Row7.checked

theorem mod1319_terminal {E : Type*} [Field E] [CharP E 1319] (h u v l d : E)
    (checkD : d*84=1) (checkL : (h48.map (Int.castRingHom E)).eval l=0)
    (roots : RootSystem (pencilAt l d) h u v) (diag : ∀j,zEval (diagAux j) ![l,h,u,v]=0) :
    terminalAt h u v l d≠0 :=
  mod1319_terminal_of_mixed_certificate primeRows prime_factorization rows_checked h u v l d
    checkD checkL roots diag

/-- A terminal product cannot vanish on the six-on scalar atlas over any
characteristic-zero field. The proof uses exact reduction at 1319, not sign. -/
theorem sixOn_atlas_impossible {K : Type*} [Field K] [CharZero K] {h u v l : K}
    (hr : (lobattoPencil l).eval h=0) (ur : (lobattoPencil l).eval u=0)
    (vr : (lobattoPencil l).eval v=0) (uh : u≠h) (vh : v≠h) (vu : v≠u)
    (k : sixOnK8 h u v l=0) :
    sixOnTerminalProduct h u v l ≠ 0 :=
  sixOn_atlas_impossible_of_mixed_certificate primeRows prime_factorization rows_checked hr ur vr uh vh vu k

end RKCert.CompactResidue

namespace RKCert.Paired

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem order9_no_five_off_six_on
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6) : False := by
  obtain ⟨h,u,v,l,inj,roots,k,terminal⟩ := order9_actual_five_six_atlas_input ha ho N M
  refine CompactResidue.sixOn_atlas_impossible (roots 0) (roots 2) (roots 3) ?_ ?_ ?_ k terminal
  · exact fun e => (by decide : (2:Fin 4)≠0) (inj e)
  · exact fun e => (by decide : (3:Fin 4)≠0) (inj e)
  · exact fun e => (by decide : (3:Fin 4)≠2) (inj e)

/-- A hypothetical 12-stage order-nine tableau over an ordered field must
have exactly one off node. The one-off atlas still requires exclusion. -/
theorem order9_only_one_off
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    (supportedNodes A (qdef A)).card=1 := by
  rcases order9_actual_remaining_census ha ho with h|⟨x,y⟩
  · exact h
  · exact (order9_no_five_off_six_on ha ho x y).elim

end RKCert.Paired

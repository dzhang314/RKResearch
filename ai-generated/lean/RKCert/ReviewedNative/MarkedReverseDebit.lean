module

public import RKCert.ReviewedNative.OptionalTerminalMark
public import RKCert.ReviewedNative.ReverseClockGain

@[expose] public section

/-! # Saturated marked space pays the full reverse clock debit

The all-monomial primitive flag belongs to the exact marked annihilator,
including the same physical terminal as the ordinary mark. Reuse the
checked reverse Hermite gain only after proving this identification. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
variable {K : Type*} [Field K] {s p j n : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

/-- Both the ordinary and all-monomial reverse flags annihilate the
physical terminal line under the same vanishing first-seed condition. -/
theorem primitive_mark_paid (ha : ∀ i k,i ≤ k → A i k=0)
    (L : LastActive b (Fin.last s)) (n : ℕ) :
    primitiveBack A b n≤annih (terminalMark A b) := by
  by_cases z : firstSeed A b=0
  · intro w hw
    rw [terminalMark,ite_eq_left z]
    apply mem_annih.mpr
    intro v hv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    have atLast := mem_tailZero.mp (L.primitiveBack_tail ha z n hw) (Fin.last s) le_rfl
    rw [map_smul,row_coordinate,atLast,smul_zero]
  · intro w _
    rw [terminalMark,ite_eq_right z]
    apply mem_annih.mpr
    intro v hv
    rw [(Submodule.mem_bot K).mp hv,map_zero]

theorem primitiveBack_le_marked_annih (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder p A b) (L : LastActive b (Fin.last s)) (pay : j+n+2≤p) :
    primitiveBack A b n ≤ annih (markedTreeSpace A b j) := by
  intro w hw
  apply mem_annih.mpr
  change treeSpace A j ⊔ terminalMark A b ≤ (row w).ker
  exact sup_le (mem_annih.mp (primitiveBack_annih ho j n pay hw))
    (mem_annih.mp (primitive_mark_paid ha L n hw))

/-- The exact reverse flag is earned whenever there is no spare rank:
no invariant smaller flag is substituted for the true annihilator. -/
theorem primitiveBack_eq_marked_annih_of_rank (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder p A b) (L : LastActive b (Fin.last s)) (pay : j+n+2≤p)
    (sat : s+1≤finrank K (markedTreeSpace A b j)+n+finrank K (back A b 0)) :
    primitiveBack A b n = annih (markedTreeSpace A b j) := by
  apply Submodule.eq_of_le_of_finrank_le (primitiveBack_le_marked_annih ha ho L pay)
  have dim := finrank_annih (markedTreeSpace A b j)
  rw [Fintype.card_fin] at dim
  have lo := back_finrank ha ho n (by omega)
  have big := Submodule.finrank_mono (back_le_primitiveBack (A:=A) (b:=b) n)
  omega

/-- Stable forward columns give stable reflected-clock rows in the true
annihilator. The identity is just diag(1-c)=I-diag(c). -/
theorem marked_annih_reflected_stable
    (stable : (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j) :
    (annih (markedTreeSpace A b j)).map (diag (reflectedClock A))≤
      annih (markedTreeSpace A b j) := by
  apply annih_map_diag
  intro v hv
  change diag (reflectedClock A) v∈markedTreeSpace A b j
  have e : diag (reflectedClock A) v=v-diag (nodes A) v := by
    ext i
    simp [reflectedClock,sub_mul]
  rw [e]
  exact (markedTreeSpace A b j).sub_mem hv (stable (Submodule.mem_map_of_mem hv))

/-- Invariance pays at least floor((n+2)/2) of the immediately previous
marked grade. All costs are counted in the original finite coordinate space. -/
theorem marked_clock_invariant_debit [CharZero K] (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder p A b) (L : LastActive b (Fin.last s)) (pos : 1≤j) (pay : j+n+2≤p)
    (sat : s+1≤finrank K (markedTreeSpace A b j)+n+finrank K (back A b 0))
    (stable : (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j) :
    finrank K (markedTreeSpace A b (j-1))+(n+2)/2≤finrank K (markedTreeSpace A b j) := by
  have ident := primitiveBack_eq_marked_annih_of_rank ha ho L pay sat
  have inv : (primitiveBack A b n).map (diag (reflectedClock A))≤primitiveBack A b n := by
    rw [ident]
    exact marked_annih_reflected_stable stable
  have cost := reverse_clock_invariant_gain ha ho n (by omega) inv
  have hi : finrank K (primitiveBack A b (n+1))≤finrank K (annih (markedTreeSpace A b (j-1))) :=
    Submodule.finrank_mono (primitiveBack_le_marked_annih ha ho L (by omega))
  rw [ident] at cost
  have d := finrank_annih (markedTreeSpace A b j)
  have e := finrank_annih (markedTreeSpace A b (j-1))
  rw [Fintype.card_fin] at d e
  omega

end RKResearch.Certified.Graded.Reverse

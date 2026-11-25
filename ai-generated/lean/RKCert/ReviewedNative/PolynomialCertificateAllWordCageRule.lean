module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortSchema

@[expose] public section

/-! # One-coordinate closed subdivision and grouped exact port witnesses -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

/-- The other seven projected coordinates are untouched. The geometric
chart rectangle is not being cut, just a closed factor interval. -/
def cutCage (r : CageRow) (slot : Fin 8) (cut : ℕ) (right : Bool) : CageRow :=
  ⟨r.rect, List.ofFn (fun j : Fin 8 =>
    let ab := r.endpoint j.val
    if j = slot then (if right then (cut, ab.2) else (ab.1, cut)) else ab)⟩

theorem cutCage_endpoint (r : CageRow) (slot : Fin 8) (cut : ℕ) (right : Bool) (j : Fin 8) :
    (cutCage r slot cut right).endpoint j.val =
      if j = slot then
        (if right then (cut, (r.endpoint j.val).2) else ((r.endpoint j.val).1, cut))
      else r.endpoint j.val := by
  simp only [cutCage, CageRow.endpoint, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some] <;> rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem cutCage_covers (r : CageRow) (slot : Fin 8) (cut : ℕ)
    {β : Fin 8 → K} (hb : InCages r β) :
    InCages (cutCage r slot cut false) β ∨ InCages (cutCage r slot cut true) β := by
  by_cases side : β slot ≤ (cut : K) / 32768
  · left
    intro j
    by_cases eq : j = slot
    · subst j
      rw [cutCage_endpoint, if_pos rfl]
      exact ⟨(hb slot).1, side⟩
    · simpa only [cutCage_endpoint, if_neg eq] using hb j
  · right
    intro j
    by_cases eq : j = slot
    · subst j
      rw [cutCage_endpoint, if_pos rfl]
      exact ⟨(lt_of_not_ge side).le, (hb slot).2⟩
    · simpa only [cutCage_endpoint, if_neg eq] using hb j

abbrev GroupPortPlan := List (List PortWord × List SignedPort)

def groupChecks (r : CageRow) (plan : GroupPortPlan) : Bool :=
  plan.all (fun x => planOK x.1 r x.2)

theorem groupChecks_append (r : CageRow) (a b : GroupPortPlan) :
    groupChecks r (a ++ b) = (groupChecks r a && groupChecks r b) := List.all_append

/-- The one failing port may depend on both the whole word and the row. -/
def AllWordCage (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (words : List (List PortWord)) (r : CageRow) : Prop :=
  ∀ {β : Fin 8 → K}, InCages r β → ∀ {w : PortWord}, w ∈ words.flatten → ∃ p ∈ w.six, p.value β ≠ 0

def AllWordRows (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (words : List (List PortWord)) (rows : List CageRow) : Prop :=
  ∀ r ∈ rows, AllWordCage K words r

theorem allWordCage_of_plan {r : CageRow} {words : List (List PortWord)} {plan : GroupPortPlan}
    (keys : plan.map Prod.fst = words) (good : groupChecks r plan = true) :
    AllWordCage K words r := by
  intro β hb w hw
  obtain ⟨g, hg, hwg⟩ := List.mem_flatten.mp hw
  rw [← keys] at hg
  obtain ⟨⟨g', p⟩, hp, he⟩ := List.mem_map.mp hg
  change g' = g at he
  subst g'
  exact plan_forces_nonzero (List.all_eq_true.mp good _ hp) hwg hb

theorem allWordCage_join {r : CageRow} {words : List (List PortWord)} {slot : Fin 8} {cut : ℕ}
    (left : AllWordCage K words (cutCage r slot cut false))
    (right : AllWordCage K words (cutCage r slot cut true)) : AllWordCage K words r := by
  intro β hb w hw
  rcases cutCage_covers r slot cut hb with h | h
  · exact left h hw
  · exact right h hw

theorem allWordRows_append {words : List (List PortWord)} {l r : List CageRow}
    (hl : AllWordRows K words l) (hr : AllWordRows K words r) : AllWordRows K words (l ++ r) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hl x h
  · exact hr x h

theorem allWordRows_nil {words : List (List PortWord)} : AllWordRows K words [] := by
  intro r hr
  exact (List.not_mem_nil hr).elim

theorem allWordRows_cons {words : List (List PortWord)} {r : CageRow} {rs : List CageRow}
    (h : AllWordCage K words r) (hs : AllWordRows K words rs) : AllWordRows K words (r :: rs) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hs x hx

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

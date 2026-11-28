module
public import Init
@[expose] public section

namespace RKResearch.Certified.ERK10AttachCore

/-! The logical endgame of the order-ten proof, abstract over the actual
tree presentation and coefficient module. All ring-theoretic inputs are
named hypotheses. No assertion about the paid tableau is built into the
definition. It can be instantiated using the literal attach recursion. -/

structure Kit (T : Type u) (V : Type v) where
  size : T → Nat
  attach : T → T → T → Prop
  positive : ∀ t, 0 < size t
  decompose : ∀ t, 6 ≤ size t → ∃ l r, attach t l r
  attach_size : ∀ t l r, attach t l r → size t = size l + size r
  zero : V
  add : V → V → V
  mul : V → V → V
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  err : T → V
  edge : T → V
  nominal : T → V
  primitive : T → V
  recurrence : ∀ t l r, attach t l r →
    err t = add (add (mul (primitive l) (err r)) (mul (nominal r) (edge l)))
      (mul (edge l) (err r))
  ann : Nat → V → Prop
  line : V → Prop
  ann_zero : ∀ j, ann j zero
  ann_add : ∀ j x y, ann j x → ann j y → ann j (add x y)
  nominal_shift : ∀ t j x, j + (size t - 1) ≤ 5 →
    ann (j+(size t-1)) x → ann j (mul (nominal t) x)
  primitive_shift : ∀ t j x, j + size t ≤ 5 →
    ann (j+size t) x → ann j (mul (primitive t) x)
  err_low : ∀ t, size t ≤ 4 → err t = zero
  edge_low : ∀ t, size t ≤ 3 → edge t = zero
  err_five : ∀ t, size t = 5 → line (err t)
  edge_four : ∀ t, size t = 4 → line (edge t)
  line_ann : ∀ x, line x → ann 5 x
  edge_step : ∀ t, 5 ≤ size t → size t ≤ 9 →
    ann (10-size t) (err t) → ann (9-size t) (edge t)
  line_product : ∀ x y, line x → line y → ann 1 (mul x y)
  line_ann_product : ∀ x y, line x → ann 4 y → ann 0 (mul x y)
  ann_line_product : ∀ x y, ann 4 x → line y → ann 0 (mul x y)

/-- The entire nonlinear attach induction with the exact \(4+5\),
\(4+6\), \(5+5\) product cases, not a linear word-only assertion. -/
theorem Kit.grade {T : Type u} {V : Type v} (K : Kit T V)
    (t : T) (lo : 5 ≤ K.size t) (hi : K.size t ≤ 10) :
    K.ann (10-K.size t) (K.err t) := by
  suffices H : ∀ n : Nat, ∀ x : T, K.size x = n → 5 ≤ n → n ≤ 10 →
      K.ann (10-K.size x) (K.err x) from H _ t rfl lo hi
  intro n
  induction n using Nat.strongRecOn
  next n ih =>
    intro x hx h5 h10
    by_cases hn5 : n = 5
    · have hx5 : K.size x = 5 := hx.trans hn5
      rw [hx5]
      exact K.line_ann _ (K.err_five x hx5)
    have hsix : 6 ≤ K.size x := by omega
    obtain ⟨l,r,h⟩ := K.decompose x hsix
    have hSum := K.attach_size x l r h
    have hl := K.positive l
    have hr := K.positive r
    have hLt : K.size l < n := by omega
    have hRt : K.size r < n := by omega
    let j := 10 - (K.size l + K.size r)
    have jp : j+K.size l=10-K.size r := by dsimp [j]; omega
    have jn : j+(K.size r-1)=9-K.size l := by dsimp [j]; omega
    have lAnn (hL : 5 ≤ K.size l) := ih _ hLt l rfl hL (by omega)
    have rAnn (hR : 5 ≤ K.size r) := ih _ hRt r rfl hR (by omega)
    have he (hL : 4 ≤ K.size l) : K.ann (9-K.size l) (K.edge l) := by
      by_cases hL4 : K.size l=4
      · rw [hL4]
        exact K.line_ann _ (K.edge_four l hL4)
      · exact K.edge_step l (by omega) (by omega) (lAnn (by omega))
    have left : K.ann j (K.mul (K.primitive l) (K.err r)) := by
      by_cases hR : 5 ≤ K.size r
      · apply K.primitive_shift l j _ (by rw [jp]; omega)
        rw [jp]
        exact rAnn hR
      · rw [K.err_low r (by omega),K.mul_zero]
        exact K.ann_zero _
    have right : K.ann j (K.mul (K.nominal r) (K.edge l)) := by
      by_cases hL : 4 ≤ K.size l
      · apply K.nominal_shift r j _ (by rw [jn]; omega)
        rw [jn]
        exact he hL
      · rw [K.edge_low l (by omega),K.mul_zero]
        exact K.ann_zero _
    have prod : K.ann j (K.mul (K.edge l) (K.err r)) := by
      by_cases hL : 4 ≤ K.size l
      · by_cases hR : 5 ≤ K.size r
        · have shape : (K.size l=4 ∧ K.size r=5) ∨
              (K.size l=4 ∧ K.size r=6) ∨ (K.size l=5 ∧ K.size r=5) := by omega
          rcases shape with ⟨hL4,hR5⟩|⟨hL4,hR6⟩|⟨hL5,hR5⟩
          · have hj : j=1 := by dsimp [j]; omega
            rw [hj]
            exact K.line_product _ _ (K.edge_four l hL4) (K.err_five r hR5)
          · have hj : j=0 := by dsimp [j]; omega
            rw [hj]
            apply K.line_ann_product _ _ (K.edge_four l hL4)
            simpa only [hR6] using rAnn hR
          · have hj : j=0 := by dsimp [j]; omega
            rw [hj]
            apply K.ann_line_product _ _ _ (K.err_five r hR5)
            simpa only [hL5] using he hL
        · rw [K.err_low r (by omega),K.mul_zero]
          exact K.ann_zero _
      · rw [K.edge_low l (by omega),K.zero_mul]
        exact K.ann_zero _
    rw [hSum,K.recurrence x l r h]
    exact K.ann_add _ _ _ (K.ann_add _ _ _ left right) prod

end RKResearch.Certified.ERK10AttachCore

#print axioms RKResearch.Certified.ERK10AttachCore.Kit.grade

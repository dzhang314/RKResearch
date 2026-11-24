module
public import RKCert.ERKFiniteReverseGain

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

omit [CharZero K] in
theorem chain_add_core {V:Type*} [AddCommGroup V] [Module K V]
    {T:V→ₗ[K]V} {U W:Submodule K V} {w:V} (n:ℕ) :
    chain T (U⊔W) w n=chain T U w n⊔W := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [chain,ih]
    ac_rfl

omit [CharZero K] in
theorem Eplus_band_growth {q d j n:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hj:q+1≤j) (hn:0<n) (hU:U.map (diag (nodes A))≤U)
    (he:treePlus A d j=polyBand A q⊔chain (diag (nodes A)) U w n) :
    treePlus A d j ⊔ (treePlus A d j).map (diag (nodes A)) =
      polyBand A q⊔chain (diag (nodes A)) U w (n+1) := by
  let C := diag (nodes A)
  let P := polyBand A q
  let Z := chain C U w n
  have hm : P.map C≤treePlus A d j := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro v hv
    exact (show treeSpace A j≤treePlus A d j from le_sup_left)
      (treeSpace_mono A hj (diag_treeSpace A q (polyBand_le A le_rfl hv)))
  change treePlus A d j=P⊔Z at he
  rw [he] at hm
  rw [he,Submodule.map_sup,←chain_sup_map hU hn]
  apply le_antisymm
  · apply sup_le
    · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)
    · exact sup_le (hm.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right))) (le_sup_right.trans le_sup_right)
  · exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))

theorem edge_noninvariant (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:8≤q) (M:Margin A b q ε d)
    {j:ℕ} (hlo:q≤j) (hhi:j+4≤2*q+ε)
    (rNow:finrank K (treePlus A d j)=q+j+1+d)
    (rPrev:finrank K (treePlus A d (j-1))=
      if j=q then 2*q-1+d else q+j+d) :
    ¬ (treePlus A d j).map (diag (nodes A))≤treePlus A d j := by
  intro h
  have eq:j-1+1=j := by omega
  have hnew : (treePlus A d (j-1+1)).map (diag (nodes A))≤treePlus A d (j-1+1) := by rw [eq];exact h
  by_cases hqj:j=q
  · have r := finite_reverse_gain ha ho d (j-1) 3 (by decide) (by decide) (by omega) (by omega) M.atOne hnew
    rw [eq,rNow,rPrev,ite_eq_left hqj] at r
    omega
  · have r := finite_reverse_gain ha ho d (j-1) 2 (by decide) (by decide) (by omega) (by omega) M.atOne hnew
    rw [eq,rNow,rPrev,ite_eq_right hqj] at r
    omega

theorem band_step (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:8≤q) (M:Margin A b q ε d)
    {a j n:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hlo:q≤j) (hhi:j+4≤2*q+ε) (ha':a+1≤j) (hn:0<n) (hU:U.map (diag (nodes A))≤U)
    (E:treePlus A d j=polyBand A a⊔chain (diag (nodes A)) U w n)
    (rNow:finrank K (treePlus A d j)=q+j+1+d)
    (rPrev:finrank K (treePlus A d (j-1))=
      if j=q then 2*q-1+d else q+j+d) :
    treePlus A d (j+1)=polyBand A a⊔chain (diag (nodes A)) U w (n+1) ∧
      finrank K (treePlus A d (j+1))=q+(j+1)+1+d := by
  let Z:=treePlus A d j⊔(treePlus A d j).map (diag (nodes A))
  have hne : treePlus A d j<Z := lt_of_le_of_ne le_sup_left
    (fun e=>edge_noninvariant ha ho hq M hlo hhi rNow rPrev (le_sup_right.trans (le_of_eq e.symm)))
  have hin : Z≤treePlus A d (j+1) := sup_le (Eplus_mono A d (by omega)) (Eplus_clock A d j)
  have low := Submodule.finrank_lt_finrank_of_lt hne
  have mid := Submodule.finrank_mono hin
  have high := M.cap (j+1) (by omega)
  have eq := Submodule.eq_of_le_of_finrank_le hin (by omega)
  exact ⟨eq.symm.trans (Eplus_band_growth ha' hn hU E),by omega⟩

/-- Propagate from the actual first paid grade through E_(p−3). The first
midpoint jump uses three reverse independent knots; all subsequent jumps need
only two. This leaves only the initial alias split outside the induction. -/
theorem band_staircase (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:8≤q) (M:Margin A b q ε d)
    {a l:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hlo:q≤a+1) (hL:0<l) (hU:U.map (diag (nodes A))≤U)
    (E:treePlus A d (a+1)=polyBand A a⊔chain (diag (nodes A)) U w l)
    (rNow:finrank K (treePlus A d (a+1))=q+(a+1)+1+d)
    (rPrev:finrank K (treePlus A d ((a+1)-1))=
      if a+1=q then 2*q-1+d else q+(a+1)+d) :
    ∀ k,a+1+k≤2*q+ε-3→
      treePlus A d (a+1+k)=polyBand A a⊔chain (diag (nodes A)) U w (l+k) ∧
      finrank K (treePlus A d (a+1+k))=q+(a+1+k)+1+d ∧
      finrank K (treePlus A d ((a+1+k)-1))=
        if a+1+k=q then 2*q-1+d else q+(a+1+k)+d := by
  intro k
  induction k with
  | zero => intro _;simpa only [Nat.add_zero] using And.intro E (And.intro rNow rPrev)
  | succ n ih =>
    intro bound
    obtain ⟨e,r,prev⟩:=ih (by omega)
    obtain ⟨e',r'⟩:=band_step ha ho hq M (j:=a+1+n) (n:=l+n)
      (by omega) (by omega) (by omega) (by omega) hU e r prev
    have eq:a+1+(n+1)=a+1+n+1 := by omega
    rw [eq,show a+1+n+1-1=a+1+n by omega,ite_eq_right (by omega)]
    exact ⟨e',r',by omega⟩

end RKCert.Paired.FiniteMidpoint


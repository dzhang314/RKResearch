module
public import RKCert.DirkMidpointHead
public import RKCert.DirkTailGridShift

@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s m j q : ℕ}
variable {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
noncomputable section

/-- Noninvariance of the true reverse-word annihilator implies noninvariance
of every actual tree space beyond the midpoint up to its final increment. -/
theorem even_tree_clock_escape (hm : 7≤m) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+4≤2*m) : ¬(treeSpace A q).map (diag (nodes A))≤treeSpace A q := by
  let r:=2*m-q-3
  have er:q+r+3=2*m:=by dsimp [r];omega
  have eqn:=(even_dual_band hm ha ho he low er).2.2.1
  have esc : ¬(dirkBack A b r).map (diag (mirror A))≤dirkBack A b r := by
    rcases eq_or_lt_of_le (show 1≤r by omega) with eq|lt
    · rw [←eq]
      exact even_reverse_nonlocal hm ha ho he
    · exact word_escape hm ha ho he (by omega) (by omega)
  rw [eqn] at esc
  intro inv
  apply esc
  rintro _ ⟨w,hw,rfl⟩
  apply mem_annih.mpr; intro v hv
  rw [row_flip_diag]
  apply mem_annih.mp hw
  have ex : diag (mirror A) v=v-diag (nodes A) v := by
    ext i;simp [mirror];ring
  rw [ex]
  exact (treeSpace A q).sub_mem hv (inv ⟨v,hv,rfl⟩)

/-- The whole tree-space increment is supplied by physical multiplication
by c, since the noninvariant image already consumes the sole new rank. -/
theorem even_tree_clock_step (hm : 7≤m) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+4≤2*m) :
    treeSpace A (q+1)=treeSpace A q ⊔ (treeSpace A q).map (diag (nodes A)) := by
  have sz:= (even_dual_band hm ha ho he (q:=q) (r:=2*m-q-3) low (by omega)).1
  have sn:= (even_dual_band hm ha ho he (q:=q+1) (r:=2*m-q-4) (by omega) (by omega)).1
  have esc:=even_tree_clock_escape hm ha ho he low high
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le (treeSpace_mono A (by omega)) (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A q))
  · have hs : treeSpace A q < treeSpace A q ⊔ (treeSpace A q).map (diag (nodes A)) :=
      lt_of_le_of_ne le_sup_left (fun e=>esc (le_sup_right.trans (le_of_eq e.symm)))
    have:=Submodule.finrank_lt_finrank_of_lt hs
    omega

omit [CharZero K] in
private theorem chain_mono_length {V : Type*} [AddCommGroup V] [Module K V]
    {T : V→ₗ[K]V} {U : Submodule K V} {w : V} {n k : ℕ} (inc : n≤k) :
    chain T U w n≤chain T U w k := by
  obtain ⟨u,mem⟩:=(chain_le_iff (T:=T) (U:=U) (w:=w) k).mp le_rfl
  exact (chain_le_iff n).mpr ⟨u,fun i hi=>mem i (hi.trans_le inc)⟩

namespace MidpointHead

/-- The genuine post-midpoint E_q equals the *fixed* scalar P_m block plus
the very same core and successively longer clock orbit of its genuine
grade-five head. No high-degree polynomial block is being silently added. -/
theorem tree_band {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {r : ℕ}
    (h : MidpointHead A m U w r) (fixed : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+3≤2*m) :
    treeSpace A q=LinearMap.range (polyEval A m) ⊔ chain (diag (nodes A)) U w (r+(q-5)) := by
  have hm : 7≤m:=by rcases fixed with rfl|rfl|rfl|rfl <;>decide
  induction q,low using Nat.le_induction with
  | base => rw [tree_eq_poly_sup_zero ho (by omega),h.band m (by omega) le_rfl]
  | succ q hq ih =>
    have qr:=ih (by omega)
    have step:=even_tree_clock_step hm ha ho he hq (by omega : q+4≤2*m)
    let T:=diag (nodes A)
    let V:=LinearMap.range (polyEval A m)
    let S:=chain T U w (r+(q-5))
    have ex : S ⊔ S.map T=chain T U w (r+((q+1)-5)) := by
      rw [show r+((q+1)-5)=(r+(q-5))+1 by omega]
      exact chain_sup_map h.invariant (by have:=h.positive;omega)
    have fm : zeroSpace A m≤S := by
      rw [h.band m (by omega) le_rfl]
      exact chain_mono_length (by omega)
    have cs : V.map T≤V ⊔ (S ⊔ S.map T) :=
      (midpoint_scalar_shift fixed ha ho he).trans
        (sup_le_sup_left (sup_le_sup fm (Submodule.map_mono fm)) _)
    rw [step,qr]
    change (V ⊔ S) ⊔ (V ⊔ S).map T=V ⊔ _
    rw [Submodule.map_sup,←ex]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
        (sup_le cs (le_sup_right.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_left) (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))

end MidpointHead
end
end RKCert.Paired.Terminal

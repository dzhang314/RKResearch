module

public import RKCert.DirkWeightedFiveCut
public import RKCert.DirkWeightedFiveSites
public import RKCert.FiveDebutFourAtoms
public import RKCert.FiveDebutScalar

@[expose] public section

/-! # Weighted fifth debut through the two paid bands

The numerical obstruction reuses the certified ordinary Hankel and
fixed scalar tail; only the physical rank cuts and actual visits differ.
-/
namespace RKCert.Paired.LocalProjection.WeightedFive
open RKCert.Endpoint RKCert.FiveDebut Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable (D : WeightedFive K s)

omit [CharZero K] in
theorem masked_response {S : Finset K} {i : Fin s} {P : K[X]} (db : D.Debut S i)
    {j : ℕ} (hj : 5≤j) (ju : j≤6) (dp : P.natDegree≤j) (h0 : P.eval 0=0)
    (roots : ∀ a∈S,P.eval a=0) :
    ∃ Q : K[X],Q.degree<((j-3:ℕ):WithBot ℕ) ∧
      ∀ l,(l < i ∨ l=i ∧ D.pivot i=0) → D.base l≠0 →
        (Paired.primitive P).eval (D.clock l)=D.amp l*Q.eval (D.clock l) := by
  have pre := D.mask db h0 roots
  have dq : (0:K[X]).degree<((j-4:ℕ):WithBot ℕ) := by
    rw [degree_zero]
    exact WithBot.bot_lt_coe _
  obtain ⟨Q,dQ,vals⟩ := D.primitive_pay hj ju dp dq (by simpa using pre)
  refine ⟨Q,dQ,fun l pay active => ?_⟩
  rw [←formalPrimitive_eq_treePrimitive]
  exact D.normalize l active (vals l pay)

set_option maxHeartbeats 1400000 in
theorem impossible (D : WeightedFive K s) : False := by
  classical
  obtain ⟨E⟩ := D.exists_debuts 5 D.count
  let ix₃ := E.index ∘ prefixThree
  let ix₄ := E.index ∘ prefixFour
  let fourth := E.index (3:Fin 5)
  let fifth := E.index (Fin.last 4)
  let z : Fin 5→K := D.clock ∘ E.index
  let w : Fin 5→K := D.amp ∘ E.index
  let z₃ := z ∘ prefixThree
  let z₄ := z ∘ prefixFour
  let w₃ := w ∘ prefixThree
  let w₄ := w ∘ prefixFour
  let S₃ := Finset.univ.image (D.clock ∘ ix₃)
  let S₄ := Finset.univ.image (D.clock ∘ ix₄)
  have db₄ : D.Debut S₃ fourth := E.debut_at 3
  have db₅ : D.Debut S₄ fifth := E.debut_at (Fin.last 4)
  have before₄ (j : Fin 3) : ix₃ j < fourth := E.ordered (show prefixThree j < (3:Fin 5) from j.isLt)
  have before₅ (j : Fin 4) : ix₄ j < fifth := E.ordered (show prefixFour j < Fin.last 4 from j.isLt)
  have clock₃ : Function.Injective z₃ := E.inj.comp (Fin.castLE_injective (by decide))
  have clock₄ : Function.Injective z₄ := E.inj.comp (Fin.castLE_injective (by decide))
  have head₃ (j : Fin 3) : D.head (ix₃ j)≠0 := by
    apply D.early_head (E.debut_at (prefixThree j))
    have a : (Finset.univ.image (D.clock ∘ E.priorIndex (prefixThree j))).card≤j.val :=
      Finset.card_image_le.trans (by rw [Finset.card_univ,Fintype.card_fin]; exact Nat.le_refl _)
    omega
  have n₃ (j : Fin 3) : w₃ j≠0 := div_ne_zero (head₃ j) (E.active (prefixThree j))
  have off : D.pivot fifth=0 := D.refund_fifth ix₃ db₅
    (Finset.card_image_le.trans (by simp)) (fun j => E.ordered (show prefixThree j < Fin.last 4 from by
      have := j.isLt; exact Nat.lt_trans this (by decide))) head₃ clock₃
  have pay₅ (j : Fin 5) : E.index j < fifth ∨ E.index j=fifth ∧ D.pivot fifth=0 := by
    by_cases e : j=Fin.last 4
    · exact Or.inr ⟨congrArg E.index e,off⟩
    · exact Or.inl (E.ordered (lt_of_le_of_ne (Fin.le_last j) e))
  have cover₃ (i : Fin s) (il : i < fourth) (b : D.base i≠0) (c : D.clock i≠0) :
      ∃ j,D.clock i=D.clock (ix₃ j) := by
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp (db₄.old i il b c)
    exact ⟨j,e.symm⟩
  have cover₄ (i : Fin s) (il : i < fifth) (b : D.base i≠0) (c : D.clock i≠0) :
      ∃ j,D.clock i=D.clock (ix₄ j) := by
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp (db₅.old i il b c)
    exact ⟨j,e.symm⟩
  let use₃ : Fin 1→Fin 3 := Fin.castLE (by decide)
  obtain ⟨P,Q,pn,dp,p0,dq,fit,zero⟩ := D.paired_cut (j:=5) (d:=1) ix₃ ix₃
    (by decide) (by decide) (by decide) before₄ (fun j => E.active (prefixThree j)) cover₃
    (fun j => Or.inl (before₄ j)) (fun j => E.active (prefixThree j)) use₃
    (fun j => n₃ (use₃ j)) (clock₃.comp (Fin.castLE_injective _)) (by decide)
  have rank₃ := three_cut_singular clock₃ (fun j => E.nz (prefixThree j)) n₃ pn dp p0 dq fit zero
  let use₄ : Fin 2→Fin 4 := Fin.castLE (by decide)
  have nu₄ (j : Fin 2) : D.amp (ix₄ (use₄ j))≠0 := n₃ (Fin.castLE (by decide : 2≤3) j)
  obtain ⟨T,R,tn,dt,t0,dr,fit₄,zero₅⟩ := D.paired_cut (j:=6) (d:=2) ix₄ E.index
    (by decide) (by decide) (by decide) before₅ (fun j => E.active (prefixFour j)) cover₄
    pay₅ E.active use₄ nu₄ (clock₄.comp (Fin.castLE_injective _)) (by decide)
  have fresh (j : Fin 4) : z (Fin.last 4)≠z₄ j := fun e =>
    (Fin.ne_of_gt (show prefixFour j < Fin.last 4 from j.isLt)) (E.inj e)
  obtain ⟨n₄,h1,h2⟩ := five_cut_linear_kernel clock₄ (fun j => E.nz (prefixFour j))
    (E.nz (Fin.last 4)) fresh tn dt t0 dr fit₄ (zero₅ (Fin.last 4)) (fun j => zero₅ (prefixFour j))
  let a := fun i => z₃ i^2/w₃ i
  let A := fun i => z₄ i^2/w₄ i
  let y := z (3:Fin 5)
  let x := z (Fin.last 4)
  let atom := y^2/w (3:Fin 5)
  have split (k : ℕ) : sumPower z₄ A k=sumPower z₃ a k+atom*y^k := by
    unfold sumPower
    rw [Fin.sum_univ_castSucc]
    rfl
  have nn : atom≠0 := div_ne_zero (pow_ne_zero _ (E.nz 3)) (n₄ (Fin.last 3))
  have yx : y≠x := fun e => (by decide : (3:Fin 5)≠Fin.last 4) (E.inj e)
  change sumPower z₃ a 0*sumPower z₃ a 2=(sumPower z₃ a 1)^2 at rank₃
  change sumPower z₄ A 1=x*sumPower z₄ A 0 at h1
  change sumPower z₄ A 2=x*sumPower z₄ A 1 at h2
  simp only [split,pow_zero,mul_one,pow_one] at h1 h2
  obtain ⟨e0,e1,e2⟩ := fourth_atom_zero rank₃ nn yx h1 h2
  have bm (j : Fin 3) : sumPower z₄ A j.val=0 := by
    rw [split]
    fin_cases j <;> first | simpa using e0 | simpa using e1 | simpa using e2
  obtain ⟨lam,lam_ne,amplitudes⟩ := four_atoms_normalized clock₄
    (fun j => E.nz (prefixFour j)) n₄ bm
  apply five_scalar_impossible z w E.inj E.nz lam lam_ne amplitudes
  · let U := threeNodal z
    have dU : U.natDegree=3 := by simp [U,threeNodal]
    have rU (a : K) (ha : a∈S₃) : U.eval a=0 := by
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
      exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    obtain ⟨B,dB,vals⟩ := D.masked_response db₄ (j:=5) (by decide) (by decide)
      (P:=X*U) (natDegree_mul_le.trans (by rw [natDegree_X,dU]; decide))
      (by simp) (fun a ha => by simp [rU a ha])
    exact ⟨B,dB,fun j => vals _ (Or.inl (before₄ j)) (E.active (prefixThree j))⟩
  · let V := fourNodal z
    have dV : V.natDegree=4 := by simp [V,fourNodal]
    have rV (a : K) (ha : a∈S₄) : V.eval a=0 := by
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
      exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    obtain ⟨B,dB,vals⟩ := D.masked_response db₅ (j:=5) (by decide) (by decide)
      (P:=X*V) (natDegree_mul_le.trans (by rw [natDegree_X,dV]))
      (by simp) (fun a ha => by simp [rV a ha])
    exact ⟨B,dB,fun j => vals _ (pay₅ j) (E.active j)⟩
  · let V := fourNodal z
    have dV : V.natDegree=4 := by simp [V,fourNodal]
    have rV (a : K) (ha : a∈S₄) : V.eval a=0 := by
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
      exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    obtain ⟨B,dB,vals⟩ := D.masked_response db₅ (j:=6) (by decide) (by decide)
      (P:=X^2*V) (natDegree_mul_le.trans (by rw [natDegree_X_pow,dV]))
      (by simp) (fun a ha => by simp [rV a ha])
    exact ⟨B,dB,fun j => vals _ (pay₅ j) (E.active j)⟩

end
end RKCert.Paired.LocalProjection.WeightedFive

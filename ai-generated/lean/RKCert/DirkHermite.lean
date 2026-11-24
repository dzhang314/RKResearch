module

public import RKCert.TableauHermiteGain
public import RKCert.DirkNoStall

@[expose] public section

/-! # Inclusive prefix Hermite gain for ordinary lower-triangular tableaux

In contrast to strict causality, the new node at the last detecting row has
to be a root of the input. The counted observations then use double roots
at every observed node, including that last row. -/

namespace RKCert.Endpoint
open Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

def InclusiveCausal (N : (Fin s → K) →ₗ[K] (Fin s → K)) : Prop :=
  ∀ (i : Fin s) (x y : Fin s → K), (∀ j ≤ i, x j=y j) → N x i=N y i

theorem inclusive_nodal_primitive_zero [CharZero K] (S : Finset K)
    (Q : K[X]) (hd : Q.natDegree+1<S.card)
    (hv : ∀ a∈S, a≠0 → (formalPrimitive (nodalHull S*Q)).eval a=0) :
    Q=0 := by
  let F := formalPrimitive (nodalHull S * Q)
  have hroot (a : K) (ha : a∈S) : F.IsRoot a := by
    by_cases h : a=0
    · subst a; exact formalPrimitive_eval_zero _
    · exact hv a ha h
  have hdouble (a : K) (ha : a∈S) : F.derivative.IsRoot a := by
    dsimp only [F]
    rw [derivative_formalPrimitive]
    simp [IsRoot,nodalHull_eval_of_mem ha]
  by_contra hQ
  have hF : F≠0 := by
    intro hf
    have he := congrArg Polynomial.derivative hf
    simp [F,(monic_nodalHull S).ne_zero,hQ] at he
  have hsq (a : K) (ha : a∈S) : (X-C a)^2 ∣ F :=
    (le_rootMultiplicity_iff hF).mp ((one_lt_rootMultiplicity_iff_isRoot hF).mpr
      ⟨hroot a ha,hdouble a ha⟩)
  have hdiv : nodalHull S ^ 2 ∣ F := by
    rw [nodalHull,←Finset.prod_pow]
    exact Finset.prod_dvd_of_coprime (fun a _ b _ hn =>
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hn).isUnit).pow) hsq
  have h1 := natDegree_formalPrimitive_le (nodalHull S*Q)
  have h2 := natDegree_mul_le (p:=nodalHull S) (q:=Q)
  rw [natDegree_nodalHull] at h2
  have h3 : (nodalHull S ^ 2).natDegree=2*S.card := by
    rw [natDegree_pow,natDegree_nodalHull,Nat.mul_comm]
  apply hF (eq_zero_of_dvd_of_natDegree_lt hdiv _)
  rw [h3]
  dsimp [F] at *
  omega

variable [CharZero K]

/-- Two linear lifts of the same polynomial test. The first is in the nodal
subspace, the second detects all selected nodes. Their difference under
the causal map is paid in the space of genuine primitive defects. -/
theorem inclusive_nodal_lifts (c v : Fin s → K) (U Z : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : InclusiveCausal N)
    (hU : MaskInvariant c U) {r : ℕ} (hr : 0<r)
    (hcount : r≤(failedNodes c v U s).card)
    (hprim : ∀ P : K[X], P.natDegree+1≤2*r+1 →
      N (weightedEval c v P) - weightedEval c v (formalPrimitive P) ∈ Z) :
    ∃ L D : (Fin r → K) →ₗ[K] (Fin s → K),
      (∀ q, L q∈U) ∧ (∀ q, D q - N (L q) ∈ Z) ∧ (∀ q, D q∈U → q=0) := by
  classical
  obtain ⟨k,hs,hnew,hkbad⟩ := exists_rth_failure c v U hr hcount
  let B := failedNodes c v U (k.val+1)
  let S := insert 0 B
  have hB : B=insert (c k) (failedNodes c v U k.val) := by
    apply Finset.Subset.antisymm (failedNodes_step c v U k)
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|hm
    · exact hkbad
    · exact failedNodes_mono c v U (Nat.le_succ _) hm
  have h0B : 0∉B := fun h => (mem_failedNodes.mp h).1 rfl
  have hScard : S.card=r+1 := by
    simp only [S,Finset.card_insert_of_notMem h0B]
    rw [hB,Finset.card_insert_of_notMem hnew,hs]
  have h0S : 0∈S := Finset.mem_insert_self _ _
  let H := nodalHull S
  obtain ⟨w,hw,hwP⟩ := exists_masked_prefix_lift c v hU (k.val+1) H
    (nodalHull_eval_of_mem h0S) (fun a ha => nodalHull_eval_of_mem (Finset.mem_insert_of_mem ha))
  let L := (weightedEval c w).comp (ofFn r)
  let G := ((weightedEval c v).comp formalPrimitiveLinear - N.comp (weightedEval c v)).comp
    ((LinearMap.mulLeft K H).comp (ofFn r))
  let D := G + N.comp L
  have eqL (q : Fin r → K) : L q=weightedEval c w (ofFn r q) := rfl
  have eqD (q : Fin r → K) : D q =
      (weightedEval c v (formalPrimitive (H*ofFn r q)) -
      N (weightedEval c v (H*ofFn r q))) + N (L q) := rfl
  refine ⟨L,D,?_,?_,?_⟩
  · intro q
    rw [eqL]
    have he : weightedEval c w (ofFn r q) = (fun i => (ofFn r q).eval (c i)*w i) := by
      ext i; simp
    rw [he]
    exact mulByBlock_mem c hU (fun a => (ofFn r q).eval a) hw
  · intro q
    have dQ := ofFn_natDegree_lt hr q
    have dH : H.natDegree = S.card := natDegree_nodalHull S
    have hd := natDegree_mul_le (p:=H) (q:=ofFn r q)
    rw [eqD,add_sub_cancel_right]
    exact by simpa only [neg_sub] using Z.neg_mem (hprim _ (by omega))
  · intro q hqu
    let Q := ofFn r q
    let F := formalPrimitive (H*Q)
    have hprefix (i : Fin s) (hi : i.val < k.val+1) : D q i=F.eval (c i)*v i := by
      have he : N (weightedEval c v (H*Q)) i=N (weightedEval c w Q) i := by
        apply hN
        intro j hj
        have hjk : j.val<k.val+1 := by change j.val ≤ i.val at hj; omega
        rw [weightedEval_apply,weightedEval_apply,hwP j hjk,eval_mul]
        ac_rfl
      rw [eqD,eqL]
      simp only [Pi.add_apply,Pi.sub_apply]
      change _ - N (weightedEval c v (H*Q)) i + N (weightedEval c w Q) i = _
      rw [he,sub_add_cancel,weightedEval_apply]
    have vanish (a : K) (ha : a∈B) : F.eval a=0 := by
      by_contra h
      apply (mem_failedNodes.mp ha).2
      refine ⟨(F.eval a)⁻¹ • D q,U.smul_mem _ hqu,?_⟩
      intro i hi hci
      change (F.eval a)⁻¹ * D q i = v i
      rw [hprefix i hi,hci,←mul_assoc,inv_mul_cancel₀ h,one_mul]
    apply injective_ofFn r
    rw [map_zero]
    apply inclusive_nodal_primitive_zero S Q
    · have hd := ofFn_natDegree_lt hr q
      dsimp [Q]
      omega
    · intro a ha han
      exact vanish a ((Finset.mem_insert.mp ha).resolve_left han)

theorem outgoing_inclusive_gain (c v : Fin s → K) (U Z : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : InclusiveCausal N)
    (hU : MaskInvariant c U) (hUZ : U≤Z) (hNU : ∀ w∈U, N w∈Z)
    (r : ℕ) (hcount : r≤(failedNodes c v U s).card)
    (hprim : ∀ P : K[X], P.natDegree+1≤2*r+1 →
      N (weightedEval c v P) - weightedEval c v (formalPrimitive P) ∈ Z) :
    Module.finrank K U+r≤Module.finrank K Z := by
  by_cases h : r=0
  · simpa [h] using Submodule.finrank_mono hUZ
  obtain ⟨L,D,hL,hDelta,hInd⟩ :=
    inclusive_nodal_lifts c v U Z N hN hU (Nat.pos_of_ne_zero h) hcount hprim
  exact finrank_add_of_independent_mod hUZ D (fun q => by
    simpa only [sub_add_cancel] using Z.add_mem (hDelta q) (hNU _ (hL q))) hInd

theorem incoming_inclusive_gain (c v : Fin s → K) (V U : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : InclusiveCausal N)
    (hU : MaskInvariant c U) (hVU : V≤U) (hNV : ∀ w∈V, N w∈U)
    (r : ℕ) (hcount : r≤(failedNodes c v U s).card)
    (hprim : ∀ P : K[X], P.natDegree+1≤2*r+1 →
      N (weightedEval c v P) - weightedEval c v (formalPrimitive P) ∈ U) :
    Module.finrank K V+r≤Module.finrank K U := by
  by_cases h : r=0
  · simpa [h] using Submodule.finrank_mono hVU
  obtain ⟨L,D,hL,hDelta,hInd⟩ :=
    inclusive_nodal_lifts c v U U N hN hU (Nat.pos_of_ne_zero h) hcount hprim
  exact finrank_add_of_independent_mod hVU L hL (fun q hq => hInd q (by
    simpa only [sub_add_cancel] using U.add_mem (hDelta q) (hNV _ hq)))

end
end RKCert.Endpoint

namespace RKCert.Paired
open RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

omit [CharZero K] in
theorem inclusiveCausal_mat (ha : ∀ i j : Fin s, i.val<j.val → A i j=0) :
    InclusiveCausal (mat A) := by
  intro i x y h
  simp only [mat_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j ≤ i
  · rw [h j hji]
  · rw [ha i j (lt_of_not_ge hji),zero_mul,zero_mul]

theorem dirk_forward_invariant_outgoing (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) {j : ℕ} (hj : j+1≤p)
    (U : Submodule K (Vec K s)) (hUF : U≤zeroSpace A j)
    (hC : ∀ v∈U,diag (nodes A) v∈U) :
    Module.finrank K U+j/2≤Module.finrank K (zeroSpace A (j+1)) := by
  have hmask := maskInvariant_of_diag hC
  apply outgoing_inclusive_gain (nodes A) (1:Vec K s) U (zeroSpace A (j+1)) (mat A)
    (inclusiveCausal_mat ha) hmask (hUF.trans (zeroSpace_mono A (Nat.le_succ j)))
    (fun v hv => mat_zeroSpace_charZero A j (hUF hv))
  · have h1 := activeNonzero_card_of_treeOrder ho
    have h2 := Finset.card_le_card (activeNodes_detect ho hj hUF hmask)
    omega
  · intro P hP
    rw [show weightedEval (nodes A) (1:Vec K s) P=evalNodes A P by ext i; simp,
      show weightedEval (nodes A) (1:Vec K s) (formalPrimitive P)=evalNodes A (formalPrimitive P) by
          ext i; simp,formalPrimitive_eq_treePrimitive]
    exact primitive_defect A P (by omega)

theorem dirk_forward_invariant_incoming (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) {j : ℕ} (hj : j+1≤p)
    (hC : ∀ v∈zeroSpace A j,diag (nodes A) v∈zeroSpace A j) :
    Module.finrank K (zeroSpace A (j-1))+(j-1)/2≤Module.finrank K (zeroSpace A j) := by
  cases j with
  | zero => simp
  | succ j =>
    have hmask := maskInvariant_of_diag hC
    apply incoming_inclusive_gain (nodes A) (1:Vec K s) (zeroSpace A j) (zeroSpace A (j+1)) (mat A)
      (inclusiveCausal_mat ha) hmask (zeroSpace_mono A (Nat.le_succ j)) (fun v hv => mat_zeroSpace_charZero A j hv)
    · have h1 := activeNonzero_card_of_treeOrder ho
      have h2 := Finset.card_le_card (activeNodes_detect ho hj (le_refl (zeroSpace A (j+1))) hmask)
      omega
    · intro P hP
      rw [show weightedEval (nodes A) (1:Vec K s) P=evalNodes A P by ext i; simp,
        show weightedEval (nodes A) (1:Vec K s) (formalPrimitive P)=evalNodes A (formalPrimitive P) by
            ext i; simp,formalPrimitive_eq_treePrimitive]
      exact primitive_defect A P (by omega)

end RKCert.Paired

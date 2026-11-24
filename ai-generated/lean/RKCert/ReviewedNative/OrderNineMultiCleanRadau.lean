module
public import RKCert.ReviewedNative.OrderNineMultiHighExclusion

@[expose] public section

/-! # Five clean nodes give an actual Radau hull and codimension-one interpolation -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

theorem order9_nodal_radau {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : (Fin (s+1)→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (hM : (cleanKnots A).card=5)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    nodalHull ((cleanKnots A).erase 0)=RKCert.Paired.radauQuartic := by
  let S := (cleanKnots A).erase 0
  let Q := nodalHull S
  have h0 := zero_mem_cleanKnots ha
  have hS : S.card+1=(cleanKnots A).card := Finset.card_erase_add_one h0
  have hd : Q.natDegree=4 := by
    change (nodalHull S).natDegree=4
    rw [natDegree_nodalHull]; omega
  have he := RKCert.Paired.radau_quartic_decoder Q hd.le (fun i => by
    apply anchor_probe_coeff ho Q hd.le (by have := i.isLt; omega)
    rw [← show nodalHull (cleanKnots A)=X*Q by
      rw [RKCert.Paired.nodalHull_erase_factor _ h0,map_zero,sub_zero]]
    exact probe_zero_of_clean_roots hoff _ (fun _ => nodalHull_eval_of_mem) i.val)
  have hc : Q.coeff 4=1 := hd ▸ (monic_nodalHull S).coeff_natDegree
  simpa [hc] using he

omit [CharZero K] in
theorem radau_on_root {A : Matrix (Fin s) (Fin s) K}
    (hQ : nodalHull ((cleanKnots A).erase 0)=RKCert.Paired.radauQuartic) {x : K}
    (hOn : x∈cleanKnots A) (hx : x≠0) : RKCert.Paired.radauQuartic.eval x=0 := by
  rw [←hQ]
  exact nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨hx,hOn⟩)

theorem order9_five_on_head_not_dvd {s:ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : (Fin (s+1)→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b) (hM : (cleanKnots A).card=5)
    (hOffWeights : ∀ x∈offKnots A, offMass A b x=0)
    (hF : zeroSpace A 4=band A 2) (P : K[X]) (hd : P.natDegree≤2)
    (off : ∀i, g A i≠0 → P.eval (nodes A i)=g A i) : ¬ P∣nodalHull (cleanKnots A) := by
  have rad := order9_nodal_radau ha ho hM hOffWeights
  obtain ⟨u,hu,nu,test⟩:=first_nonzero_clean_test ha hF P hd off
    (exists_nonzero_on_of_card (by omega))
  intro div
  rw [RKCert.Paired.nodalHull_erase_factor _ (zero_mem_cleanKnots ha),rad,map_zero,sub_zero] at div
  exact RKCert.FixedFactor.radau_divisor_first_moment div hd nu (radau_on_root rad hu nu) ((scalar_primitive (X*P)).symm ▸ test)

omit [CharZero K] in
section
noncomputable def pairBase (A : Matrix (Fin s) (Fin s) K) (q : ℕ) :
    ((Fin 5→K)×(Fin (q+1)→K)) →ₗ[K] (Fin s→K) :=
  (coeffEval A 4).coprod ((diag (g A)).comp (coeffEval A q))

theorem pairBase_apply (A : Matrix (Fin s) (Fin s) K) (q : ℕ) (v : (Fin 5→K)×(Fin (q+1)→K)) :
    pairBase A q v=evalNodes A (ofFn 5 v.1)+diag (g A) (evalNodes A (ofFn (q+1) v.2)) := by
  rw [ofFn_eval A 4,ofFn_eval A q]
  rfl

theorem pairBase_injective {q:ℕ} {A : Matrix (Fin s) (Fin s) K} (M : 5≤(cleanKnots A).card)
    (N : q+1≤(offKnots A).card) : Function.Injective (pairBase A q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let V:=ofFn 5 z.1
  let W:=ofFn (q+1) z.2
  have dV : V.natDegree<5:=ofFn_natDegree_lt (by decide) _
  have dW : W.natDegree<q+1:=ofFn_natDegree_lt (by omega) _
  have atAll (i : Fin s) : V.eval (nodes A i)+g A i*W.eval (nodes A i)=0 := by
    rw [pairBase_apply] at hz
    exact congrFun hz i
  have v0 : V=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' V (cleanKnots A)
    (fun x hx=>by obtain ⟨i,hi,rfl⟩:=mem_cleanKnots.mp hx; simpa [hi] using atAll i) (by omega)
  have w0 : W=0:=eq_zero_of_natDegree_lt_card_of_eval_eq_zero' W (offKnots A)
    (fun x hx=>by obtain ⟨i,hi,rfl⟩:=mem_offKnots.mp hx
                  exact (mul_eq_zero.mp (by simpa [v0] using atAll i)).resolve_left hi) (by omega)
  exact Prod.ext (injective_ofFn 5 (v0.trans (ofFn_zero _).symm))
    (injective_ofFn (q+1) (w0.trans (ofFn_zero _).symm))

theorem off_poly_of_base {q:ℕ} {A : Matrix (Fin s) (Fin s) K} (M:5≤(cleanKnots A).card)
    (P F : K[X]) (fit : ∀i,g A i≠0→P.eval (nodes A i)=g A i)
    (onF : ∀x∈cleanKnots A,F.eval x=0)
    (range : evalNodes A F∈LinearMap.range (pairBase A q)) :
    ∃ T:K[X], T.natDegree≤q ∧ ∀x∈offKnots A, F.eval x=P.eval x*T.eval x := by
  obtain ⟨v,hv⟩:=range
  rw [pairBase_apply] at hv
  let V:=ofFn 5 v.1
  let T:=ofFn (q+1) v.2
  have he (i : Fin s) : V.eval (nodes A i)+g A i*T.eval (nodes A i)=F.eval (nodes A i) :=
    congrFun hv i
  have v0 : V=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (cleanKnots A) (fun x hx=>by
    obtain ⟨i,hi,rfl⟩:=mem_cleanKnots.mp hx
    simpa [hi,onF _ hx] using he i) (by
      have dV : V.natDegree<5:=ofFn_natDegree_lt (by decide) _
      omega)
  refine ⟨T,Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _),?_⟩
  intro x hx
  obtain ⟨i,hi,rfl⟩:=mem_offKnots.mp hx
  simpa [v0,fit i hi] using (he i).symm



theorem pairBase_le_both {q : ℕ} (hq:4≤q) {A : Matrix (Fin s) (Fin s) K} (P:K[X])
    (fit:∀i,g A i≠0→P.eval (nodes A i)=g A i) :
    LinearMap.range (pairBase A q)≤treeSpace A (q+2) ⊓ onOffSpace A := by
  rintro _ ⟨v,rfl⟩
  rw [pairBase_apply]
  refine ⟨(treeSpace A (q+2)).add_mem ?_ ?_,pairProfile_mem_onOffSpace fit _ _⟩
  · apply evalNodes_mem_treeSpace; have:=ofFn_natDegree_lt (by decide : 0<5) v.1; omega
  · apply zeroSpace_le_treeSpace
    rw [Nat.add_comm q 2]
    apply band_le A q
    exact band_iff.mpr ⟨_,Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _),rfl⟩

end

/-- All (5+q+2) branch-state functions are representable in the actual
grade-(q+2) tree space when there are exactly five on and (q+2) off
sites, q≥4, and the degree-two-or-lower head does not divide the on hull. -/
theorem five_on_state_le {q:ℕ} (hq:4≤q) {A : Matrix (Fin s) (Fin s) K} (M:(cleanKnots A).card=5)
    (N:(offKnots A).card=q+2) (P : K[X]) (dP:P.natDegree≤2)
    (fit : ∀i,g A i≠0→P.eval (nodes A i)=g A i)
    (nondiv : ¬P∣nodalHull (cleanKnots A)) : onOffSpace A≤treeSpace A (q+2) := by
  let : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  let Q:=nodalHull (cleanKnots A)
  let V:=treeSpace A (q+2) ⊓ onOffSpace A
  have dQ : Q.natDegree=5 := (natDegree_nodalHull _).trans M
  have dr : finrank K (LinearMap.range (pairBase A q))=5+(q+1) := by
    rw [LinearMap.finrank_range_of_inj (pairBase_injective (by omega : 5≤(cleanKnots A).card)
        (by omega : q+1≤(offKnots A).card)),Module.finrank_prod,
        Module.finrank_fin_fun,Module.finrank_fin_fun]
  have hdim : 5+(q+2)≤finrank K V := by
    by_contra! small
    have inc : LinearMap.range (pairBase A q)≤V := pairBase_le_both hq P fit
    have e:=Submodule.eq_of_le_of_finrank_le inc (by omega)
    have mh (F:K[X]) (d:F.natDegree≤q+2) : evalNodes A F∈LinearMap.range (pairBase A q) := by
      rw [e]
      refine ⟨evalNodes_mem_treeSpace A F d,?_⟩
      have z : evalNodes A (0:K[X])=0 := by ext i; simp
      have hs := pairProfile_mem_onOffSpace fit F (0:K[X])
      rw [z,map_zero,add_zero] at hs
      exact hs
    obtain ⟨T,dT,tq⟩:=off_poly_of_base (by omega : 5≤(cleanKnots A).card) P Q fit
      (fun x h=>nodalHull_eval_of_mem h) (mh Q (by omega))
    have dx : (X*Q).natDegree≤q+2 := (natDegree_mul_le ..).trans (by rw [natDegree_X]; omega)
    obtain ⟨U,dU,tu⟩:=off_poly_of_base (by omega : 5≤(cleanKnots A).card) P (X*Q) fit
      (fun _ h=>by rw [eval_mul,show Q.eval _=0 from nodalHull_eval_of_mem h,mul_zero]) (mh _ dx)
    exact RKCert.FixedFactor.off_interpolation_pair _ N P Q dP (by omega) nondiv (fun _ hx=>by
      obtain ⟨i,hi,rfl⟩:=mem_offKnots.mp hx; rwa [fit i hi]) T U dT dU tq tu
  have eqv : V=onOffSpace A:=Submodule.eq_of_le_of_finrank_le inf_le_right (by
    rw [onOffSpace_rank,M,N]; exact hdim)
  exact eqv ▸ (show V≤treeSpace A (q+2) from inf_le_left)
end RKResearch.Certified.Graded.MultiOff

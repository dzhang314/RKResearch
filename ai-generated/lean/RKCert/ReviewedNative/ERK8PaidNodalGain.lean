module

public import RKCert.ReviewedNative.OrderedNodalGain
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Causal Hermite gain with a finite payment
This is the bounded-denominator version of the existing Hermite kernel
and both gain orientations. The only derivative calls have degree at
most twice the requested rank gain. -/
namespace RKResearch.Certified.Graded.ERK8PaidField

open RKResearch Polynomial Module RKCert.Endpoint
open scoped Matrix Classical

noncomputable section
variable {K : Type*} [Field K]

theorem primitive_derivative_paid {P : K[X]}
    (unit : ∀ n : ℕ, 0<n → n≤P.natDegree+1 → (n:K)≠0) :
    (primitive P).derivative=P := by
  ext j
  rw [Polynomial.coeff_derivative, primitive_coeff_succ]
  by_cases h : j ≤ P.natDegree
  · have nz := unit (j+1) (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using div_mul_cancel₀ (P.coeff j) nz
  · have e : P.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [e,zero_div,zero_mul]

theorem nodal_primitive_zero_paid (S : Finset K) {z : K} (hz : z ∉ S)
    (Q : K[X]) (hdeg : Q.natDegree < S.card)
    (unit : ∀ n : ℕ, 0<n → n≤2*S.card → (n:K)≠0)
    (obs : ∀ a ∈ S, a ≠ 0 → (primitive (nodalHull S * Q)).IsRoot a)
    (obsZ : (primitive (nodalHull S * Q)).IsRoot z) : Q=0 := by
  let F := primitive (nodalHull S * Q)
  have degree := natDegree_mul_le (p:=nodalHull S) (q:=Q)
  rw [natDegree_nodalHull] at degree
  have der : F.derivative=nodalHull S*Q :=
    primitive_derivative_paid (fun n pos lt => unit n pos (by omega))
  have hv (a : K) (ha : a ∈ S) : F.IsRoot a := by
    by_cases h : a = 0
    · subst a
      rw [IsRoot,←coeff_zero_eq_eval_zero,show F=primitive (nodalHull S*Q) from rfl,
        primitive_coeff_zero]
    · exact obs a ha h
  have hd (a : K) (ha : a ∈ S) : F.derivative.IsRoot a := by
    rw [der]
    simp [IsRoot,nodalHull_eval_of_mem ha]
  have hdiv := nodalHull_sq_extra_dvd S hz hv hd obsZ
  have hF : F.natDegree≤2*S.card :=
    (primitive_natDegree_le degree).trans (by omega)
  have hprod : (nodalHull S^2*(X-C z)).natDegree = 2*S.card+1 := by
    rw [natDegree_mul (pow_ne_zero _ (monic_nodalHull S).ne_zero) (monic_X_sub_C z).ne_zero,
      natDegree_pow,natDegree_nodalHull,natDegree_X_sub_C]
  have zero : F=0 := eq_zero_of_dvd_of_natDegree_lt hdiv (by omega)
  rw [zero,map_zero] at der
  exact (mul_eq_zero.mp der.symm).resolve_left (monic_nodalHull S).ne_zero

variable {s : ℕ}
/-- A common family of simultaneous prefix lifts: Bq is in the block-invariant
space U, Dq is N(Bq) minus one genuine primitive defect of degree at most
2r, and Dq in U forces q to vanish. The same family gives both directions
of the Hermite rank estimate, without choosing unrelated local rows. -/
theorem exists_causal_hermite_family_paid (c v : Fin s → K) (U : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : StrictlyCausal N) (hU : MaskInvariant c U)
    (r : ℕ) (units : ∀ n : ℕ, 0<n → n≤2*r → (n:K)≠0) (hrpos : 0<r) (hcount : r≤(failedNodes c v U s).card) :
    ∃ (m : ℕ), m=r ∧ ∃ (B D : (Fin m → K) →ₗ[K] (Fin s → K)),
      (∀ q, B q ∈ U) ∧
      (∀ q, ∃ P : K[X], P.natDegree+1 ≤ 2*r ∧ D q =
        weightedEval c v (primitive P) - N (weightedEval c v P) + N (B q)) ∧
      (∀ q, D q∈U → q=0) := by
  classical
  obtain ⟨k,hs,hnew,hkbad⟩ := exists_rth_failure c v U hrpos hcount
  let B := failedNodes c v U k.val
  let S := insert 0 B
  let z := c k
  have hz : z≠0 := (mem_failedNodes.mp hkbad).1
  have h0B : 0∉B := fun h => (mem_failedNodes.mp h).1 rfl
  have hScard : S.card=r := by simpa [S,B,Finset.card_insert_of_notMem h0B] using hs
  have hzS : z∉S := fun h => (Finset.mem_insert.mp h).elim hz hnew
  have h0S : 0∈S := Finset.mem_insert_self _ _
  let H := nodalHull S
  obtain ⟨w,hw,hwP⟩ := exists_masked_prefix_lift c v hU k.val H
    (nodalHull_eval_of_mem h0S) (fun a ha => nodalHull_eval_of_mem (Finset.mem_insert_of_mem ha))
  let Bv := weightedEval c v
  let Bw := weightedEval c w
  let LH := LinearMap.mulLeft K H
  let G := (Bv.comp primitive - N.comp Bv).comp LH + N.comp Bw
  let L := G.comp (ofFn S.card)
  have eqL (q : Fin S.card → K) : L q =
      weightedEval c v (primitive (H * ofFn S.card q)) -
      N (weightedEval c v (H*ofFn S.card q)) + N (weightedEval c w (ofFn S.card q)) := rfl
  have hker (q : Fin S.card → K) (hqu : L q∈U) : q=0 := by
    let Q := ofFn S.card q
    let F := primitive (H*Q)
    have hprefix (i : Fin s) (hi : i.val < k.val+1) : L q i = F.eval (c i)*v i := by
      have he : N (weightedEval c v (H*Q)) i = N (weightedEval c w Q) i := by
        apply hN
        intro j hj
        have hjk : j.val<k.val := by change j.val < i.val at hj; omega
        rw [weightedEval_apply,weightedEval_apply,hwP j hjk,eval_mul]
        ac_rfl
      rw [eqL]
      simp only [Pi.add_apply,Pi.sub_apply]
      change _ - N (weightedEval c v (H*Q)) i + N (weightedEval c w Q) i = _
      rw [he,sub_add_cancel,weightedEval_apply]
    have vanish (a : K) (ha : a∈failedNodes c v U (k.val+1)) : F.IsRoot a := by
      change F.eval a=0
      by_contra h
      apply (mem_failedNodes.mp ha).2
      refine ⟨(F.eval a)⁻¹ • L q,U.smul_mem _ hqu,?_⟩
      intro i hi hci
      change (F.eval a)⁻¹*L q i=v i
      rw [hprefix i hi,hci,← mul_assoc,inv_mul_cancel₀ h,one_mul]
    apply injective_ofFn S.card
    rw [map_zero]
    apply nodal_primitive_zero_paid S hzS Q (ofFn_natDegree_lt (by omega) q)
      (fun n pos lt => units n pos (by omega))
    · intro a ha han
      obtain hab := (Finset.mem_insert.mp ha).resolve_left han
      exact vanish a (failedNodes_mono c v U (Nat.le_succ _) hab)
    · exact vanish z hkbad
  let E := Bw.comp (ofFn S.card)
  refine ⟨S.card,hScard,E,L,?_,?_,hker⟩
  · intro q
    have e : E q = (fun i => (ofFn S.card q).eval (c i)*w i) := by
      ext i; exact weightedEval_apply .. 
    rw [e]; exact mulByBlock_mem c hU (fun a => (ofFn S.card q).eval a) hw
  · intro q
    refine ⟨H*ofFn S.card q,?_,eqL q⟩
    have dQ := ofFn_natDegree_lt (n:=S.card) (by omega) q
    have dH : H.natDegree = S.card := natDegree_nodalHull S
    have dHQ := natDegree_mul_le (p:=H) (q:=ofFn S.card q)
    omega

/-- General outgoing nodal Hermite gain. U need only be node-mask invariant.
Strictness is an actual prefix condition on N. Each primitive defect and N(U)
lies in Z, which also contains U. As soon as r distinct nonzero blocks detect
the base column, at least r new dimensions in Z/U are compulsory. -/
theorem outgoing_nodal_gain_paid (c v : Fin s → K) (U Z : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : StrictlyCausal N) (hU : MaskInvariant c U)
    (hUZ : U≤Z) (hNU : ∀ w∈U, N w∈Z) (r : ℕ) (units : ∀ n : ℕ, 0<n → n≤2*r → (n:K)≠0)
    (hcount : r≤(failedNodes c v U s).card)
    (hprim : ∀ P : K[X], P.natDegree+1 ≤ 2*r →
      N (weightedEval c v P) - weightedEval c v (primitive P) ∈ Z) :
    Module.finrank K U + r ≤ Module.finrank K Z := by
  by_cases hr : r=0
  · simpa [hr] using Submodule.finrank_mono hUZ
  obtain ⟨m,rfl,B,D,hB,hD,hker⟩ :=
    exists_causal_hermite_family_paid c v U N hN hU r units (Nat.pos_of_ne_zero hr) hcount
  apply finrank_add_of_independent_mod hUZ D _ hker
  intro q
  obtain ⟨P,hp,he⟩ := hD q
  rw [he]
  exact Z.add_mem (by simpa only [neg_sub] using Z.neg_mem (hprim P hp)) (hNU _ (hB q))

/-- Incoming nodal hull rank, with a merely invariant containing hull W.
The data NV and the primitive defects lie in W; V itself need not be invariant. -/
theorem incoming_nodal_gain_paid (c v : Fin s → K) (V W : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : StrictlyCausal N) (hW : MaskInvariant c W)
    (hVW : V≤W) (hNV : ∀ w∈V, N w∈W) (r : ℕ) (units : ∀ n : ℕ, 0<n → n≤2*r → (n:K)≠0)
    (hcount : r≤(failedNodes c v W s).card)
    (hprim : ∀ P : K[X], P.natDegree+1 ≤ 2*r →
      N (weightedEval c v P) - weightedEval c v (primitive P) ∈ W) :
    Module.finrank K V + r ≤ Module.finrank K W := by
  by_cases hr : r=0
  · simpa [hr] using Submodule.finrank_mono hVW
  obtain ⟨m,rfl,B,D,hB,hD,hker⟩ :=
    exists_causal_hermite_family_paid c v W N hN hW r units (Nat.pos_of_ne_zero hr) hcount
  apply finrank_add_of_independent_mod hVW B hB
  intro q hq
  apply hker
  obtain ⟨P,hp,he⟩ := hD q
  rw [he]
  exact W.add_mem (by simpa only [neg_sub] using W.neg_mem (hprim P hp)) (hNV _ hq)


end
end RKResearch.Certified.Graded.ERK8PaidField

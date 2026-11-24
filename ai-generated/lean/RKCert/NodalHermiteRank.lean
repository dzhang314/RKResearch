module
public import RKCert.NodalPrimitive

@[expose] public section

/-! # Prefix-detected Hermite gain for causal operators
The obstruction is simultaneous on all selected nodes. No spatial ordering
on nodes, no nonnegative weights, and no preselected independent rows occur. -/
namespace RKCert.Endpoint
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}

def blockMask (c : Fin s → K) (a : K) (v : Fin s → K) : Fin s → K :=
  fun i => if c i=a then v i else 0

def MaskInvariant (c : Fin s → K) (U : Submodule K (Fin s → K)) : Prop :=
  ∀ a v, v∈U → blockMask c a v ∈ U

/-- Rows in the same node block can be matched with an independent member of U. -/
def blockMatch (c v : Fin s → K) (U : Submodule K (Fin s → K))
    (a : K) (n : ℕ) : Prop :=
  ∃ w∈U, ∀ i : Fin s, i.val<n → c i=a → w i=v i

def failedNodes (c v : Fin s → K) (U : Submodule K (Fin s → K)) (n : ℕ) : Finset K :=
  (Finset.univ.image c).filter (fun a => a≠0 ∧ ¬blockMatch c v U a n)

theorem mem_failedNodes {c v : Fin s → K} {U : Submodule K (Fin s → K)} {a : K} {n : ℕ} :
    a ∈ failedNodes c v U n ↔ a≠0 ∧ ¬blockMatch c v U a n := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨?_,h⟩⟩
  by_contra hn
  apply h.2
  refine ⟨0,U.zero_mem,fun i _ hi => ?_⟩
  exact False.elim (hn (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩))

@[simp] theorem failedNodes_zero (c v : Fin s → K) (U : Submodule K (Fin s → K)) :
    failedNodes c v U 0=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a h
  apply (mem_failedNodes.mp h).2
  exact ⟨0,U.zero_mem,fun i hi => False.elim (Nat.not_lt_zero _ hi)⟩

theorem failedNodes_mono (c v : Fin s → K) (U : Submodule K (Fin s → K)) {m n : ℕ}
    (h : m≤n) : failedNodes c v U m ⊆ failedNodes c v U n := by
  intro a ha
  obtain ⟨hn,hm⟩ := mem_failedNodes.mp ha
  refine mem_failedNodes.mpr ⟨hn,fun ⟨w,hw,hwn⟩ => hm ⟨w,hw,?_⟩⟩
  exact fun i hi => hwn i (hi.trans_le h)

/-- Revealing one chronological coordinate can spoil at most its own local block. -/
theorem failedNodes_step (c v : Fin s → K) (U : Submodule K (Fin s → K)) (k : Fin s) :
    failedNodes c v U (k.val+1) ⊆ insert (c k) (failedNodes c v U k.val) := by
  intro a ha
  obtain ⟨hn,hbad⟩ := mem_failedNodes.mp ha
  by_cases eq : c k=a
  · exact Finset.mem_insert.mpr (Or.inl eq.symm)
  apply Finset.mem_insert_of_mem
  refine mem_failedNodes.mpr ⟨hn,fun ⟨w,hw,hmatch⟩ => hbad ⟨w,hw,?_⟩⟩
  intro i hi hci
  apply hmatch i _ hci
  by_contra! hh
  have e : i.val=k.val := by omega
  exact eq ((Fin.ext e) ▸ hci)

/-- At the r-th detected nonzero node, the old failures have size r−1,
and the new node is the one at the revealing row. -/
theorem exists_rth_failure (c v : Fin s → K) (U : Submodule K (Fin s → K))
    {r : ℕ} (hr : 0<r) (hc : r≤(failedNodes c v U s).card) :
    ∃ k : Fin s, (failedNodes c v U k.val).card + 1 = r ∧
      c k ∉ failedNodes c v U k.val ∧ c k ∈ failedNodes c v U (k.val+1) := by
  classical
  let B := failedNodes c v U
  have hExist : ∃ n : ℕ, r≤(B n).card := ⟨s,hc⟩
  let n := Nat.find hExist
  have hn : r≤(B n).card := Nat.find_spec hExist
  have hnle : n≤s := Nat.find_min' hExist hc
  have hnpos : 0<n := by
    by_contra! hh
    have he : n=0 := by omega
    simp [he,B] at hn
    omega
  let k : Fin s := ⟨n-1,by omega⟩
  have hk : k.val+1=n := by dsimp [k]; omega
  have hlo : (B k.val).card<r := lt_of_not_ge (Nat.find_min hExist (by omega : k.val<n))
  have sub : B n ⊆ insert (c k) (B k.val) := hk ▸ failedNodes_step c v U k
  have hhi := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  have hnew : c k ∉ B k.val := by
    intro hh
    have hl := Finset.card_le_card (Finset.insert_eq_of_mem hh ▸ sub : B n ⊆ B k.val)
    omega
  have had : c k∈B n := by
    by_contra hh
    have hsub : B n ⊆ B k.val := by
      intro x hx
      rcases Finset.mem_insert.mp (sub hx) with he|hr
      · exact False.elim (hh (he ▸ hx))
      · exact hr
    have := Finset.card_le_card hsub
    omega
  exact ⟨k,(show (B k.val).card+1=r by omega),hnew,hk ▸ had⟩

/-- Independent choices at the nodes combine by their disjoint masks. -/
def assembleBlocks (c : Fin s → K) (g : K → Fin s → K) : Fin s → K :=
  ∑ a ∈ Finset.univ.image c, blockMask c a (g a)

@[simp] theorem assembleBlocks_apply (c : Fin s → K) (g : K → Fin s → K) (i : Fin s) :
    assembleBlocks c g i = g (c i) i := by
  rw [assembleBlocks,Finset.sum_apply,Finset.sum_eq_single (c i)]
  · simp [blockMask]
  · intro a _ ha; simp [blockMask,Ne.symm ha]
  · intro ha; exact False.elim (ha (Finset.mem_image_of_mem _ (Finset.mem_univ _)))

theorem assembleBlocks_mem (c : Fin s → K) {U : Submodule K (Fin s → K)}
    (hU : MaskInvariant c U) (g : K → Fin s → K) (hg : ∀a,g a∈U) : assembleBlocks c g∈U :=
  U.sum_mem fun a _ => hU a (g a) (hg a)

theorem mulByBlock_mem (c : Fin s → K) {U : Submodule K (Fin s → K)}
    (hU : MaskInvariant c U) (g : K → K) {v : Fin s → K} (hv : v∈U) :
    (fun i => g (c i)*v i) ∈ U := by
  let w (a : K) := g a • v
  have h := assembleBlocks_mem c hU w (fun a => U.smul_mem _ hv)
  have he : assembleBlocks c w = fun i => g (c i)*v i := by ext i; simp [w]
  rwa [he] at h

/-- There is ONE simultaneous prefix lift of Hv in U, not one unrelated
choice per output functional. H only has to kill all already failed blocks. -/
theorem exists_masked_prefix_lift (c v : Fin s → K) {U : Submodule K (Fin s → K)}
    (hU : MaskInvariant c U) (k : ℕ) (H : K[X]) (h0 : H.eval 0=0)
    (hbad : ∀ a ∈ failedNodes c v U k, H.eval a=0) :
    ∃ w∈U, ∀ i : Fin s, i.val<k → w i=H.eval (c i)*v i := by
  classical
  have localMatch (a : K) : ∃ w∈U, ∀ i : Fin s, i.val<k → c i=a → w i=H.eval a*v i := by
    by_cases h : blockMatch c v U a k
    · obtain ⟨w,hw,hm⟩ := h
      exact ⟨H.eval a • w,U.smul_mem _ hw,fun i hi he => by simp [hm i hi he]⟩
    · have hz : H.eval a=0 := by
        by_cases he : a=0
        · simpa [he] using h0
        · exact hbad a (mem_failedNodes.mpr ⟨he,h⟩)
      exact ⟨0,U.zero_mem,by simp [hz]⟩
  choose w hw hmatch using localMatch
  refine ⟨assembleBlocks c w,assembleBlocks_mem c hU w hw,fun i hi => ?_⟩
  rw [assembleBlocks_apply,hmatch (c i) i hi rfl]

/-- Polynomial values multiplied by a (possibly signed or zero) base column. -/
def weightedEval (c v : Fin s → K) : K[X] →ₗ[K] (Fin s → K) :=
  LinearMap.pi (fun i => v i • Polynomial.leval (c i))

@[simp] theorem weightedEval_apply (c v : Fin s → K) (P : K[X]) (i : Fin s) :
    weightedEval c v P i = P.eval (c i) * v i := by simp [weightedEval,mul_comm]

def StrictlyCausal (N : (Fin s → K) →ₗ[K] (Fin s → K)) : Prop :=
  ∀ (i : Fin s) (x y : Fin s → K), (∀ j < i, x j=y j) → N x i=N y i

variable [CharZero K]

omit [CharZero K] in
/-- Additive rank from a family of jointly independent lifts modulo U. -/
theorem finrank_add_of_independent_mod {U Z : Submodule K (Fin s → K)}
    (hu : U≤Z) {n : ℕ} (L : (Fin n → K) →ₗ[K] (Fin s → K))
    (hl : ∀ q,L q∈Z) (hk : ∀ q,L q∈U → q=0) :
    Module.finrank K U + n ≤ Module.finrank K Z := by
  let M := U.subtype.comp (LinearMap.fst K U (Fin n → K)) + L.comp (LinearMap.snd K U (Fin n → K))
  let J := M.codRestrict Z (fun v => Z.add_mem (hu v.1.property) (hl v.2))
  have hin : Function.Injective J := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨v,q⟩ he
    have hzero : v.val+L q=0 := congrArg Subtype.val he
    have heq : L q = -v.val := eq_neg_of_add_eq_zero_right hzero
    have hq := hk q (heq ▸ U.neg_mem v.property)
    subst q
    have hv : v=0 := Subtype.ext (by simpa using hzero)
    simp [hv]
  have hr := LinearMap.finrank_le_finrank_of_injective hin
  simpa only [Module.finrank_prod,Module.finrank_pi,Fintype.card_fin] using hr

/-- A common family of simultaneous prefix lifts: Bq is in the block-invariant
space U, Dq is N(Bq) minus one genuine primitive defect of degree at most
2r, and Dq in U forces q to vanish. The same family gives both directions
of the Hermite rank estimate, without choosing unrelated local rows. -/
theorem exists_causal_hermite_family (c v : Fin s → K) (U : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : StrictlyCausal N) (hU : MaskInvariant c U)
    (r : ℕ) (hrpos : 0<r) (hcount : r≤(failedNodes c v U s).card) :
    ∃ (m : ℕ), m=r ∧ ∃ (B D : (Fin m → K) →ₗ[K] (Fin s → K)),
      (∀ q, B q ∈ U) ∧
      (∀ q, ∃ P : K[X], P.natDegree+1 ≤ 2*r ∧ D q =
        weightedEval c v (formalPrimitive P) - N (weightedEval c v P) + N (B q)) ∧
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
  let G := (Bv.comp formalPrimitiveLinear - N.comp Bv).comp LH + N.comp Bw
  let L := G.comp (ofFn S.card)
  have eqL (q : Fin S.card → K) : L q =
      weightedEval c v (formalPrimitive (H * ofFn S.card q)) -
      N (weightedEval c v (H*ofFn S.card q)) + N (weightedEval c w (ofFn S.card q)) := rfl
  have hker (q : Fin S.card → K) (hqu : L q∈U) : q=0 := by
    let Q := ofFn S.card q
    let F := formalPrimitive (H*Q)
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
    apply nodal_primitive_zero S hzS Q (ofFn_natDegree_lt (by omega) q)
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
theorem outgoing_nodal_gain (c v : Fin s → K) (U Z : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : StrictlyCausal N) (hU : MaskInvariant c U)
    (hUZ : U≤Z) (hNU : ∀ w∈U, N w∈Z) (r : ℕ)
    (hcount : r≤(failedNodes c v U s).card)
    (hprim : ∀ P : K[X], P.natDegree+1 ≤ 2*r →
      N (weightedEval c v P) - weightedEval c v (formalPrimitive P) ∈ Z) :
    Module.finrank K U + r ≤ Module.finrank K Z := by
  by_cases hr : r=0
  · simpa [hr] using Submodule.finrank_mono hUZ
  obtain ⟨m,rfl,B,D,hB,hD,hker⟩ :=
    exists_causal_hermite_family c v U N hN hU r (Nat.pos_of_ne_zero hr) hcount
  apply finrank_add_of_independent_mod hUZ D _ hker
  intro q
  obtain ⟨P,hp,he⟩ := hD q
  rw [he]
  exact Z.add_mem (by simpa only [neg_sub] using Z.neg_mem (hprim P hp)) (hNU _ (hB q))

/-- Incoming nodal hull rank, with a merely invariant containing hull W.
The data NV and the primitive defects lie in W; V itself need not be invariant. -/
theorem incoming_nodal_gain (c v : Fin s → K) (V W : Submodule K (Fin s → K))
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hN : StrictlyCausal N) (hW : MaskInvariant c W)
    (hVW : V≤W) (hNV : ∀ w∈V, N w∈W) (r : ℕ)
    (hcount : r≤(failedNodes c v W s).card)
    (hprim : ∀ P : K[X], P.natDegree+1 ≤ 2*r →
      N (weightedEval c v P) - weightedEval c v (formalPrimitive P) ∈ W) :
    Module.finrank K V + r ≤ Module.finrank K W := by
  by_cases hr : r=0
  · simpa [hr] using Submodule.finrank_mono hVW
  obtain ⟨m,rfl,B,D,hB,hD,hker⟩ :=
    exists_causal_hermite_family c v W N hN hW r (Nat.pos_of_ne_zero hr) hcount
  apply finrank_add_of_independent_mod hVW B hB
  intro q hq
  apply hker
  obtain ⟨P,hp,he⟩ := hD q
  rw [he]
  exact W.add_mem (by simpa only [neg_sub] using W.neg_mem (hprim P hp)) (hNV _ hq)


end
end RKCert.Endpoint

module

public import RKCert.ERKLowProfiles

@[expose] public section

/-! # First occurrences on the one-off chart

This layer is uniform in the order and stage counts. It neither assumes
constant defect amplitude nor fixes numerical prefix stage positions. -/
namespace RKCert.Paired.OneOff

open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

noncomputable abbrev g (A : Fin s → Fin s → K) : Vec K s := qdef A
noncomputable abbrev h (A : Fin s → Fin s → K) : Vec K s := mat A (qdef A)

/-- Monomial forward defect in its natural grade, including the literal
coefficient normalization used in the one-off calculations. -/
noncomputable def mDef (A : Fin s → Fin s → K) (j : ℕ) : Vec K s :=
  mat A ((nodes A)^j) - ((j+1:ℕ):K)⁻¹ • (nodes A)^(j+1)

theorem mDef_mem (A : Fin s → Fin s → K) (j : ℕ) : mDef A j ∈ zeroSpace A (j+1) := by
  have e0 : evalNodes A (monomial j (1:K)) = (nodes A)^j := by ext i; simp
  have e1 : evalNodes A (primitive (monomial j (1:K))) =
      ((j+1:ℕ):K)⁻¹ • (nodes A)^(j+1) := by
    ext i
    simp [primitive_monomial,div_eq_mul_inv]
  simpa only [mDef,e0,e1] using primitive_defect A (monomial j (1:K))
    (Polynomial.natDegree_monomial_le _)

omit [CharZero K] in
theorem mDef_apply (A : Fin s → Fin s → K) (j : ℕ) (i : Fin s) :
    mDef A j i = mat A ((nodes A)^j) i - nodes A i^(j+1)/((j+1:ℕ):K) := by
  simp [mDef,div_eq_mul_inv,mul_comm]

omit [CharZero K] in
theorem g_apply (A : Fin s → Fin s → K) (i : Fin s) :
    g A i = mat A (nodes A) i - nodes A i^2/2 := by
  simp [qdef,div_eq_mul_inv,mul_comm]

/-- Data of the earliest nonzero clock, which necessarily carries the
initial nonzero defect and identifies the unique support clock. -/
structure Origin (A : Fin s → Fin s → K) (a : K) (i : Fin s) : Prop where
  a_ne : a ≠ 0
  node : nodes A i = a
  earlier_node : ∀ j, j < i → nodes A j = 0
  defect : g A i = -a^2/2
  earlier_defect : ∀ j, j < i → g A j = 0
  off_support : ∀ j, g A j ≠ 0 → nodes A j = a

theorem origin_of_single_off (ha : StrictLower A)
    (hN : (supportedNodes A (g A)).card = 1)
    (hex : ∃ i, nodes A i≠0) : ∃ (a : K) (i : Fin s), Origin A a i := by
  let S : Set (Fin s) := {i | nodes A i≠0}
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min S (show S.Nonempty from hex)
  have pre (j : Fin s) (hj : j < i) : nodes A j=0 := by
    by_contra x
    exact hmin j x hj
  let a := nodes A i
  change a≠0 at hi
  have gi : g A i = -a^2/2 := by
    rw [g_apply,causal_mat ha i _ pre]
    change 0-a^2/2 = _
    ring
  have ng : g A i≠0 := by
    rw [gi]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hi)) (by norm_num)
  have pG (j : Fin s) (hj : j < i) : g A j=0 := by
    rw [g_apply,causal_mat ha j _ (fun k hk => pre k (hk.trans hj)),pre j hj]
    simp
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hN
  have u : a∈supportedNodes A (g A) := mem_supportedNodes.mpr ⟨i,ng,rfl⟩
  have vu : a=v := by simpa [hv] using u
  refine ⟨a,i,⟨hi,rfl,pre,gi,pG,fun j hgj => ?_⟩⟩
  have e : nodes A j ∈ supportedNodes A (g A) := mem_supportedNodes.mpr ⟨j,hgj,rfl⟩
  simpa [hv,vu] using e

theorem Origin.g_ne {a : K} {i : Fin s} (O : Origin A a i) : g A i≠0 := by
  rw [O.defect]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ O.a_ne)) (by norm_num)

omit [CharZero K] in
theorem Origin.h_first {a : K} {i : Fin s} (ha : StrictLower A) (O : Origin A a i) :
    h A i = 0 := causal_mat ha i _ O.earlier_defect

omit [CharZero K] in
theorem Origin.g_clock {a : K} {i : Fin s} (O : Origin A a i) :
    diag (nodes A) (g A)=a • g A := by
  ext j
  by_cases hj : g A j=0
  · simp [diag_apply,hj]
  · simp [diag_apply,O.off_support j hj]

theorem Origin.mDef_first {a : K} {i : Fin s} (ha : StrictLower A) (O : Origin A a i)
    {j : ℕ} (hj : j≠0) : mDef A j i = -a^(j+1)/((j+1:ℕ):K) := by
  rw [mDef_apply,causal_mat ha i _ (fun k hk => by simp [O.earlier_node k hk,hj]),O.node]
  ring

def twoSpan (u v : Vec K s) : Submodule K (Vec K s) :=
  Submodule.span K {u} ⊔ Submodule.span K {v}

omit [CharZero K] in
theorem mem_twoSpan {u v x : Vec K s} :
    x∈twoSpan u v ↔ ∃ α β : K, x=α • u+β • v := by
  constructor
  · intro hx
    obtain ⟨u',hu,v',hv,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨α,rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨β,rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨α,β,rfl⟩
  · rintro ⟨α,β,rfl⟩
    exact Submodule.mem_sup.mpr ⟨_,Submodule.mem_span_singleton.mpr ⟨α,rfl⟩,
      _,Submodule.mem_span_singleton.mpr ⟨β,rfl⟩,rfl⟩

/-- The independent primitive (Ag) is forced by explicitness. This does
not presume the one-off amplitude is constant, nor eliminate repeated rows. -/
theorem h_not_in_g_span (ha : StrictLower A) (hsep : Separated A 3)
    {a : K} {i : Fin s} (O : Origin A a i) :
    h A ∉ Submodule.span K {g A} := by
  intro hDep
  obtain ⟨ξ,eq⟩ := Submodule.mem_span_singleton.mp hDep
  have e := congrFun eq i
  simp only [Pi.smul_apply,smul_eq_mul,O.h_first ha] at e
  have x0 : ξ=0 := (mul_eq_zero.mp e).resolve_right O.g_ne
  have h0 : h A=0 := by rw [←eq,x0,zero_smul]
  let U : Submodule K (Vec K s) := Submodule.span K {g A}
  have gm : g A∈U := Submodule.mem_span_singleton_self _
  have hu : U ≤ zeroSpace A 3 := (Submodule.span_singleton_le_iff_mem ..).mpr
    (zeroSpace_mono A (by decide) (qdef_mem A))
  have h1 : diag (nodes A) (1:Vec K s) = nodes A := by ext j; simp
  apply nodes_not_zeroSpace hsep (by decide)
  apply hu
  rw [←h1]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 U
  · intro v hv
    obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,show mat A (g A)=0 from h0,smul_zero]
    exact U.zero_mem
  · intro v hv
    obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,O.g_clock]
    exact U.smul_mem _ (U.smul_mem _ gm)
  · rw [←qdef_seed]
    exact U.smul_mem _ gm

theorem rank_two_span (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (hp : 3≤p) (hsep : Separated A 3) (rank : finrank K (zeroSpace A 3)=2)
    {a : K} {i : Fin s} (O : Origin A a i) :
    zeroSpace A 3=twoSpan (g A) (h A) := by
  have gn : g A≠0 := fun e => O.g_ne (by rw [e]; rfl)
  have gm : g A∈zeroSpace A 3 := zeroSpace_mono A (by decide) (qdef_mem A)
  have hm : h A∈zeroSpace A 3 := mat_zeroSpace ho 2 hp (qdef_mem A)
  symm
  apply Submodule.eq_of_le_of_finrank_le
    (sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr gm) ((Submodule.span_singleton_le_iff_mem ..).mpr hm))
  have r := Submodule.finrank_sup_span_singleton (h_not_in_g_span ha hsep O)
  rw [finrank_span_singleton gn] at r
  change finrank K (zeroSpace A 3) ≤ finrank K (twoSpan (g A) (h A))
  rw [rank,twoSpan,r]

theorem quadratic_defect_form (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (hp : 3≤p) (hsep : Separated A 3) (rank : finrank K (zeroSpace A 3)=2)
    {a : K} {i : Fin s} (O : Origin A a i) :
    ∃ lam : K, mDef A 2=(2*a/3) • g A + lam • h A := by
  have hm := mDef_mem A 2
  rw [rank_two_span ha ho hp hsep rank O] at hm
  obtain ⟨ξ,lam,e⟩ := mem_twoSpan.mp hm
  have ep := congrFun e i
  have hi := O.mDef_first ha (j:=2) (by decide)
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hi,O.defect,O.h_first ha,
    mul_zero,add_zero,Nat.reduceAdd,Nat.cast_ofNat] at ep
  have hx : ξ=2*a/3 := by
    apply mul_right_cancel₀ (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 O.a_ne))
      (by norm_num) : -a^2/2 ≠ 0)
    linear_combination -ep
  exact ⟨lam,hx ▸ e⟩

end RKCert.Paired.OneOff

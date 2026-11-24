module

public import RKCert.CauchyKernel
public import RKCert.ForwardDefects
public import RKCert.StageBound

@[expose] public section

/-! # Polynomial separation in actual stage spaces

The exact order conditions themselves make all small integers units. A Cauchy
system therefore detects polynomial coefficients in any field, regardless of
characteristic, whenever its moment budget is paid. For an explicit tableau
one saves a probe at the left endpoint: the constant is the first coordinate.
-/

namespace RKCert.Paired
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- Polynomial evaluation in the nodes, from coefficients up to degree `q`. -/
noncomputable def polyEval (A : Fin s → Fin s → K) (q : ℕ) :
    (Fin (q+1) → K) →ₗ[K] Vec K s :=
  Fintype.linearCombination K (fun j : Fin (q+1) => normTree A (Tree.bush j.val))

theorem polyEval_apply (A : Fin s → Fin s → K) (q : ℕ) (a : Fin (q+1) → K) :
    polyEval A q a = ∑ j : Fin (q+1), a j • normTree A (Tree.bush j.val) := by
  rfl

theorem polyEval_mem_treeSpace (A : Fin s → Fin s → K) (q : ℕ) (a : Fin (q+1) → K) :
    polyEval A q a ∈ treeSpace A q := by
  rw [polyEval_apply]
  apply Submodule.sum_mem; intro j _
  apply Submodule.smul_mem
  exact (treeSpace A q).smul_mem _
    (stageWeight_mem_space A _ (by rw [Tree.order_bush]; omega))

theorem probe_polyEval (ho : HasTreeOrderAtLeast A b p) {k q : ℕ} (hk : k+q+1 ≤ p)
    (a : Fin (q+1) → K) :
    probe A b k (polyEval A q a) = ∑ j : Fin (q+1), a j / ((k+j.val+1 : ℕ):K) := by
  rw [polyEval_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := probe_normTree ho (Tree.bush j.val) k (by rw [Tree.order_bush]; omega)
  rw [Tree.order_bush, ← Nat.add_assoc] at h
  have hn := (IsUnit.of_mul_eq_one _ h).ne_zero
  rw [map_smul, smul_eq_mul]
  apply (eq_div_iff hn).mpr
  calc
    _ = a j * (((k+j.val+1 : ℕ):K) * probe A b k (normTree A (Tree.bush j.val))) := by ac_rfl
    _ = _ := by rw [h,mul_one]

/-- Univariate shifted moment systems have zero kernel, in every field in
which the indicated order has actually been attained. -/
theorem moments_detect (ho : HasTreeOrderAtLeast A b p) {n d : ℕ} (hd : 0 < d)
    (hn : n ≤ p+1) (hp : ∀ i j : Fin n, i.val+j.val+d ≤ p) (a : Fin n → K)
    (he : ∀ i : Fin n, (∑ j : Fin n, a j / ((i.val+j.val+d:ℕ):K))=0) : ∀ j, a j=0 := by
  have ne (l r : ℕ) (hlt : l<r) (hr : r-l≤p) : (l:K) ≠ (r:K) := by
    have hu := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho)
      (by omega : 0<r-l) hr).ne_zero
    intro eqn
    rw [Nat.cast_sub hlt.le, eqn, sub_self] at hu
    contradiction
  have inj : Function.Injective (fun i : Fin n => (i.val : K)) := by
    intro i j h
    apply Fin.ext
    change (i.val:K)=(j.val:K) at h
    rcases lt_trichotomy i.val j.val with h'|h'|h'
    · exact False.elim (ne _ _ h' (by omega) h)
    · exact h'
    · exact False.elim (ne _ _ h' (by omega) h.symm)
  refine cauchy_kernel (fun i : Fin n => (i.val:K)) (fun j : Fin n => (j.val:K)+(d:K)) a inj ?_ ?_ ?_
  · intro i j h; apply inj; exact add_right_cancel h
  · intro i j
    have hu := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho)
      (show 0 < i.val + j.val + d by omega) (hp i j)).ne_zero
    simpa only [Nat.cast_add, add_assoc] using hu
  · intro i; simpa only [Nat.cast_add, add_assoc] using he i

/-- With no explicitness and no sign conditions, the usual `q+1` moments
already separate the polynomial space from defects if `2q+1≤p`. -/
theorem poly_separated (ho : HasTreeOrderAtLeast A b p) {q : ℕ} (hp : 2*q+1≤p)
    (a : Fin (q+1) → K) (ha : polyEval A q a ∈ zeroSpace A q) : a = 0 := by
  ext j
  apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l => by omega) a _ j
  intro i
  have he : probe A b i.val (polyEval A q a) = 0 := probe_zeroSpace ho (by omega) ha
  rwa [probe_polyEval ho (by omega)] at he

theorem polyEval_first {A : Fin (s+1) → Fin (s+1) → K} (hs : StrictLower A)
    (q : ℕ) (a : Fin (q+1) → K) : polyEval A q a 0 = a 0 := by
  have hnode : nodes A 0=0 := by
    unfold nodes
    exact Finset.sum_eq_zero fun j _ => hs 0 j (Nat.zero_le _)
  rw [polyEval_apply, Fin.sum_univ_succ]
  simp [Finset.sum_apply, normTree_bush, hnode]

/-- At the even midpoint strict explicitness provides the missing endpoint
test. This uses only `q` scalar moments, of degrees `0,...,q−1`. -/
theorem explicit_poly_separated (hs : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    {q : ℕ} (hp : 2*q≤p) (hspos : 0 < s) (a : Fin (q+1) → K)
    (ha : polyEval A q a ∈ zeroSpace A q) : a = 0 := by
  cases s with
  | zero => contradiction
  | succ s =>
    have hv : polyEval A q a 0=0 := origin_zeroSpace A hs q ha
    rw [polyEval_first hs] at hv
    have he (i : Fin q) :
        (∑ j : Fin q, a j.succ / ((i.val+j.val+2:ℕ):K))=0 := by
      have hh : probe A b i.val (polyEval A q a)=0 := probe_zeroSpace ho (by omega) ha
      rw [probe_polyEval ho (by omega), Fin.sum_univ_succ, hv, zero_div,zero_add] at hh
      simpa only [Fin.val_succ, Nat.add_assoc] using hh
    have hh := moments_detect ho (d:=2) (by decide) (by omega)
      (fun i j => by omega) (fun j : Fin q => a j.succ) he
    ext j; exact Fin.cases hv hh j

/-- Finite-dimensional stage budget supplied by any proved separation. -/
theorem treeSpace_rank_of_separated (A : Fin s → Fin s → K) (q : ℕ)
    (hsep : ∀ a, polyEval A q a ∈ zeroSpace A q → a = 0) :
    q+1 + Module.finrank K (zeroSpace A q) ≤ Module.finrank K (treeSpace A q) := by
  let F := zeroSpace A q
  let E := treeSpace A q
  let f : ((Fin (q+1) → K) × F) →ₗ[K] Vec K s := (polyEval A q).coprod F.subtype
  let g : ((Fin (q+1) → K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem (polyEval_mem_treeSpace _ _ _) (zeroSpace_le_treeSpace _ _ z.2.property))
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have h : polyEval A q z.1 + (z.2 : Vec K s) = 0 :=
      congrArg (fun w : E => (w : Vec K s)) hz
    have hneg : polyEval A q z.1 = -(z.2 : Vec K s) := eq_neg_of_add_eq_zero_left h
    have hz₁ := hsep z.1 (hneg ▸ F.neg_mem z.2.property)
    have hz₂ : (z.2 : Vec K s) = 0 := by simpa [hz₁] using h
    exact Prod.ext hz₁ (Subtype.ext hz₂)
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_injective hg)

/-- The even-midpoint ERK dimension bound with arbitrary attained coefficient field. -/
theorem explicit_treeSpace_rank (hs : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    {q : ℕ} (hp : 2*q≤p) (hspos : 0<s) :
    q+1 + Module.finrank K (zeroSpace A q) ≤ Module.finrank K (treeSpace A q) :=
  treeSpace_rank_of_separated _ _ (explicit_poly_separated hs ho hp hspos)

/-- The corresponding unanchored rank bound, available to DIRK and SDIRK
without imposing any row-zero hypothesis. -/
theorem treeSpace_rank (ho : HasTreeOrderAtLeast A b p) {q : ℕ} (hp : 2*q+1≤p) :
    q+1 + Module.finrank K (zeroSpace A q) ≤ Module.finrank K (treeSpace A q) :=
  treeSpace_rank_of_separated _ _ (poly_separated ho hp)

/-- A coordinate coefficient recovers the actual normalized bush. -/
theorem polyEval_single (A : Fin s → Fin s → K) (q : ℕ) (j : Fin (q+1)) :
    polyEval A q (Pi.single j 1) = normTree A (Tree.bush j.val) := by
  simp [polyEval]

/-- Every column in the genuine tree span has a polynomial-plus-defect
decomposition. Uniqueness is a separate assertion requiring sufficient moments. -/
theorem exists_poly_zeroSpace (ho : HasTreeOrderAtLeast A b p) {q : ℕ} (hq : q+1≤p)
    {v : Vec K s} (hv : v ∈ treeSpace A q) :
    ∃ a : Fin (q+1) → K, v-polyEval A q a ∈ zeroSpace A q := by
  unfold treeSpace at hv
  induction hv using Submodule.span_induction with
  | mem v hg =>
    obtain ⟨t,ht,rfl⟩ := hg
    have hp := t.order_pos
    let j : Fin (q+1) := ⟨t.order-1,by omega⟩
    have he : t.order=j.val+1 := by dsimp [j]; omega
    have hd := treeDensity_isUnit_of_moments (hasMomentsThrough_of_treeOrder ho) t (by omega)
    rw [Tree.density,Nat.cast_mul] at hd
    obtain ⟨a,ha⟩ := isUnit_of_mul_isUnit_right hd
    have hs : (↑(a⁻¹):K) • normTree A t = stageWeight A t := by
      rw [normTree, ← ha, smul_smul, Units.inv_mul, one_smul]
    refine ⟨(↑(a⁻¹):K) • Pi.single j 1, ?_⟩
    rw [map_smul, polyEval_single]
    simpa only [smul_sub, hs] using (zeroSpace A q).smul_mem (↑(a⁻¹):K)
      (normDiff_mem A t (Tree.bush j.val) (by rw [Tree.order_bush]; exact he) ht)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha⟩ := hx; obtain ⟨b',hb'⟩ := hy
    refine ⟨a+b', ?_⟩
    rw [map_add]
    convert (zeroSpace A q).add_mem ha hb' using 1
    ext i; simp only [Pi.add_apply,Pi.sub_apply]; ring
  | smul r x _ hx =>
    obtain ⟨a,ha⟩ := hx
    refine ⟨r • a, ?_⟩
    rw [map_smul, ← smul_sub]
    exact (zeroSpace A q).smul_mem r ha

/-- Equality, not merely a rank lower bound, once the monomials separate:
the whole numerical tree space is their internal sum with the homogeneous
defect space. This statement is valid with either moment budget above. -/
theorem existsUnique_poly_zeroSpace (ho : HasTreeOrderAtLeast A b p) {q : ℕ} (hq : q+1≤p)
    (hsep : ∀ a, polyEval A q a ∈ zeroSpace A q → a=0)
    {v : Vec K s} (hv : v∈treeSpace A q) :
    ∃! a : Fin (q+1) → K, v-polyEval A q a ∈ zeroSpace A q := by
  obtain ⟨a,ha⟩ := exists_poly_zeroSpace ho hq hv
  refine ⟨a,ha,?_⟩
  intro d hd
  apply sub_eq_zero.mp
  apply hsep
  rw [map_sub]
  convert (zeroSpace A q).sub_mem ha hd using 1
  ext i; simp only [Pi.sub_apply]; ring

end RKCert.Paired

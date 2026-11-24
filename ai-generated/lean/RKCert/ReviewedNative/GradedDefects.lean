module
public import RKCert.ReviewedNative.GradedColumns

@[expose] public section

/-! # Native homogeneous graded defects on reviewed RKResearch data -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Differences of normalized actual trees of the same reviewed order. -/
def zeroSpace (A : Matrix ι ι R) (j : ℕ) : Submodule R (ι → R) :=
  Submodule.span R { v | ∃ t u : FiniteRootedTree,
    t.order=u.order ∧ (t.order:ℕ)≤j+1 ∧ v=normTree A t-normTree A u }

theorem normDiff_mem (A : Matrix ι ι R) {j : ℕ} (t u : FiniteRootedTree)
    (he : t.order=u.order) (ht : (t.order:ℕ)≤j+1) :
    normTree A t-normTree A u∈zeroSpace A j :=
  Submodule.subset_span ⟨t,u,he,ht,rfl⟩

theorem zeroSpace_mono (A : Matrix ι ι R) {j k : ℕ} (h : j≤k) :
    zeroSpace A j≤zeroSpace A k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  exact normDiff_mem A t u he (by omega)

theorem zeroSpace_le_treeSpace (A : Matrix ι ι R) (j : ℕ) :
    zeroSpace A j≤treeSpace A j := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  exact (treeSpace A j).sub_mem ((treeSpace A j).smul_mem _ (Φ_mem_treeSpace A t ht))
    ((treeSpace A j).smul_mem _ (Φ_mem_treeSpace A u (he ▸ ht)))

theorem probe_zeroSpace {A : Matrix ι ι R} {b : ι → R} {p j k : ℕ}
    (ho : HasOrder A b p) (pay : k+j+1≤p) :
    zeroSpace A j≤(probe A b k).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change probe A b k (_-_) = 0
  rw [map_sub,sub_eq_zero]
  have et := probe_normTree ho t k (by omega)
  have eu := probe_normTree ho u k (by rw [←he];omega)
  rw [←he] at eu
  exact (IsUnit.of_mul_eq_one _ et).mul_left_cancel (et.trans eu.symm)

theorem diag_zeroSpace (A : Matrix ι ι R) (j : ℕ) :
    zeroSpace A j≤(zeroSpace A (j+1)).comap (diag (nodes A)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change diag (nodes A) (normTree A t-normTree A u)∈zeroSpace A (j+1)
  rw [map_sub,←normTree_clock,←normTree_clock]
  exact normDiff_mem A _ _ (by simp only [order,he])
    (by simp only [order,PNat.add_coe,PNat.one_coe];omega)

theorem mat_zeroSpace_of_unit (A : Matrix ι ι R) (j : ℕ)
    (castUnit : ∀t : FiniteRootedTree, (t.order:ℕ)≤j+1 → IsUnit (((t.order:ℕ):R))) :
    zeroSpace A j≤(zeroSpace A (j+1)).comap (mat A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change mat A (normTree A t-normTree A u)∈zeroSpace A (j+1)
  have eq : (.leaf ◂ t).order=(.leaf ◂ u).order := by simp only [order,he]
  have e := normDiff_mem (j:=j+1) A (.leaf ◂ t) (.leaf ◂ u) eq
    (by simp only [order,PNat.add_coe,PNat.one_coe];omega)
  rw [normTree_unary,normTree_unary,←he,←smul_sub,←map_sub] at e
  exact ((zeroSpace A (j+1)).smul_mem_iff_of_isUnit (castUnit t ht)).mp e

theorem mat_zeroSpace {A : Matrix ι ι R} {b : ι → R} {p : ℕ}
    (ho : HasOrder A b p) (j : ℕ) (pay : j+1≤p) :
    zeroSpace A j≤(zeroSpace A (j+1)).comap (mat A) :=
  mat_zeroSpace_of_unit A j (fun t ht => ho.natCast_isUnit t.order.pos (ht.trans pay))

theorem mat_zeroSpace_charZero {K : Type*} [Field K] [CharZero K] (A : Matrix ι ι K) (j : ℕ) :
    zeroSpace A j≤(zeroSpace A (j+1)).comap (mat A) :=
  mat_zeroSpace_of_unit A j (fun t _ => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr t.order.ne_zero))

/-- The denominator-cleared degree-n monomial primitive defect. -/
theorem monomialStageDefect_mem (A : Matrix ι ι R) (n : ℕ) :
    monomialStageDefect A n∈zeroSpace A (n+1) := by
  change ((n+1:ℕ):R) • mat A (fun i => (nodes A i)^n) -
      (fun i => (nodes A i)^(n+1))∈zeroSpace A (n+1)
  let t := clockTree n
  have e : (.leaf ◂ t).order = (clockTree (n+1)).order := by
    apply PNat.eq
    simp only [t,order,PNat.add_coe,PNat.one_coe,order_clockTree]
    omega
  have ht : ((.leaf ◂ t).order:ℕ)≤n+1+1 := by
    simp only [t,order,order_clockTree,PNat.add_coe,PNat.one_coe]
    omega
  have h := normDiff_mem (j:=n+1) A (.leaf ◂ t) (clockTree (n+1)) e ht
  simpa only [t,normTree_unary,normTree_clockTree,order_clockTree] using h

theorem coe_order_eq_one_iff_leaf (t : FiniteRootedTree) : (t.order:ℕ)=1 ↔ t=.leaf := by
  cases t with
  | leaf => simp
  | butcherProduct t u =>
    have ht := t.order.pos
    have hu := u.order.pos
    simp only [order,PNat.add_coe,reduceCtorEq,iff_false]
    omega

/-- The initial physical row kills all non-leaf reviewed elementary weights. -/
theorem Φ_origin_nonleaf {s : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) R}
    (strict : ∀i j, i≤j→A i j=0) (t : FiniteRootedTree) (nt : t≠.leaf) :
    Φ t A 0=0 := by
  cases t with
  | leaf => exact (nt rfl).elim
  | butcherProduct t u =>
    have h (j : Fin (s+1)) : A 0 j=0 := strict 0 j (Fin.zero_le _)
    simp [Φ,Matrix.mulVec,dotProduct,h]

/-- Every native homogeneous defect has physical origin coordinate zero. -/
theorem origin_zeroSpace {s : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) R}
    (strict : ∀i j, i≤j→A i j=0) (n : ℕ) :
    zeroSpace A n≤(LinearMap.proj 0).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change normTree A t 0-normTree A u 0=0
  by_cases et:t=.leaf
  · have eu : u=.leaf := (coe_order_eq_one_iff_leaf u).mp (by rw [←he,et];rfl)
    rw [et,eu,sub_self]
  · have eu : u≠.leaf := by
      intro h
      exact et ((coe_order_eq_one_iff_leaf t).mp (by rw [he,h];rfl))
    simp [normTree,Φ_origin_nonleaf strict t et,Φ_origin_nonleaf strict u eu]

end RKResearch.Certified.Graded

module
public import RKCert.ReviewedNative.GradedDefects
public import Mathlib.Algebra.Algebra.Bilinear

@[expose] public section

/-! # Joining the roots of reviewed trees gives the graded product rules -/
namespace RKResearch.FiniteRootedTree

/-- Join roots without identifying or changing any branches. -/
def mergeRoots : FiniteRootedTree → FiniteRootedTree → FiniteRootedTree
  | .leaf,u => u
  | .butcherProduct t b,u => .butcherProduct (mergeRoots t u) b

theorem order_mergeRoots (t u : FiniteRootedTree) :
    ((mergeRoots t u).order:ℕ)+1=(t.order:ℕ)+(u.order:ℕ) := by
  induction t with
  | leaf => simp [mergeRoots,Nat.add_comm]
  | butcherProduct t b ih _ =>
    simp only [mergeRoots,order,PNat.add_coe]
    omega

@[simp] theorem forestFactorial_mergeRoots (t u : FiniteRootedTree) :
    (mergeRoots t u).forestFactorial=t.forestFactorial*u.forestFactorial := by
  induction t with
  | leaf => simp [mergeRoots]
  | butcherProduct t b ih _ =>
    simp only [mergeRoots,forestFactorial,ih]
    ac_rfl

end RKResearch.FiniteRootedTree

namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

section Semiring
variable {ι R : Type*} [Fintype ι] [CommSemiring R]

@[simp] theorem Φ_mergeRoots (A : Matrix ι ι R) (t u : FiniteRootedTree) :
    Φ (mergeRoots t u) A = Φ t A * Φ u A := by
  induction t with
  | leaf => simp [mergeRoots]
  | butcherProduct t b ih _ =>
    simp only [mergeRoots,Φ,ih]
    ac_rfl

theorem normTree_mergeRoots (A : Matrix ι ι R) (t u : FiniteRootedTree) :
    normTree A (mergeRoots t u) = normTree A t * normTree A u := by
  ext i
  simp only [normTree,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,forestFactorial_mergeRoots,
    PNat.mul_coe,Nat.cast_mul,Φ_mergeRoots]
  ac_rfl

theorem treeSpace_mul {A : Matrix ι ι R} {m n : ℕ} {v w : ι → R}
    (hv:v∈treeSpace A m) (hw:w∈treeSpace A n) :
    v*w∈treeSpace A (m+n) := by
  rw [←LinearMap.mul_apply' (R:=R)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ (LinearMap.mul R (ι→R)) _ _ _ hv hw
  rintro _ ⟨t,ht,rfl⟩ _ ⟨u,hu,rfl⟩
  rw [LinearMap.mul_apply' (R:=R),←Φ_mergeRoots]
  exact Φ_mem_treeSpace A _ (by have :=order_mergeRoots t u;omega)

end Semiring

section Ring
variable {ι R : Type*} [Fintype ι] [CommRing R]
variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

private theorem mul_normDiff {m n : ℕ} (t u r : FiniteRootedTree) (he:t.order=u.order)
    (ht:(t.order:ℕ)≤m+1) (hr:(r.order:ℕ)≤n+1) :
    (normTree A t-normTree A u)*normTree A r∈zeroSpace A (m+n) := by
  rw [sub_mul,←normTree_mergeRoots,←normTree_mergeRoots]
  have h1:=order_mergeRoots t r
  have h2:=order_mergeRoots u r
  apply normDiff_mem
  · apply PNat.eq
    have h := congrArg (fun x:ℕ+=>(x:ℕ)) he
    change ((mergeRoots t r).order:ℕ)=((mergeRoots u r).order:ℕ)
    omega
  · omega

theorem zeroSpace_mul {m n : ℕ} {v w : ι→R}
    (hv:v∈zeroSpace A m) (hw:w∈zeroSpace A n) : v*w∈zeroSpace A (m+n) := by
  rw [←LinearMap.mul_apply' (R:=R)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ (LinearMap.mul R (ι→R)) _ _ _ hv hw
  rintro _ ⟨t,u,eq,ht,rfl⟩ _ ⟨r,q,er,hr,rfl⟩
  rw [LinearMap.mul_apply' (R:=R),mul_sub]
  exact (zeroSpace A (m+n)).sub_mem (mul_normDiff _ _ _ eq ht hr)
    (mul_normDiff _ _ _ eq ht (er ▸ hr))

theorem zeroSpace_mul_treeSpace (ho:HasOrder p A b) {m n:ℕ} (pay:n+1≤p)
    {v w:ι→R} (hv:v∈zeroSpace A m) (hw:w∈treeSpace A n) :
    v*w∈zeroSpace A (m+n) := by
  rw [←LinearMap.mul_apply' (R:=R)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ (LinearMap.mul R (ι→R)) _ _ _ hv hw
  rintro _ ⟨t,u,eq,ht,rfl⟩ _ ⟨r,hr,rfl⟩
  rw [LinearMap.mul_apply' (R:=R)]
  have h := mul_normDiff (A:=A) t u r eq ht hr
  have nr : normTree A r=((r.forestFactorial:ℕ):R) • Φ r A := rfl
  rw [nr,mul_smul_comm] at h
  exact ((zeroSpace A (m+n)).smul_mem_iff_of_isUnit (forestFactorial_isUnit ho r (hr.trans pay))).mp h

end Ring
end RKResearch.Certified.Graded

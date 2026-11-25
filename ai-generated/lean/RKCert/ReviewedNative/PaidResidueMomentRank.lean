module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Lagrange

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Rank suppressed by the paid test rows on distinct fibres

The input is the finite clock set and its actual residue-column data.
The pair is the case with column index Fin 2. No statement about the
source of those residues or any tap-receipt recovery is used here. -/
namespace RKResearch.Certified.Graded.ResidueMomentRank

open Polynomial Module
open scoped Classical Matrix

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Incoming polynomial moments for each residue column, in matrix
multiplication orientation. -/
def PaidMoments (S : Finset K) (w : K → ι → K) (d : ℕ) : Prop :=
  ∀ (i : ι) (P : K[X]), P.natDegree ≤ d → (∑ x ∈ S, P.eval x * w x i) = 0

/-- Distinct physical clock labels index the rows of this data matrix. -/
def residueMatrix (S : Finset K) (w : K → ι → K) : Matrix (↥S) ι K :=
  fun x i => w x.1 i

/-- The actual column rank, not an input rank. -/
noncomputable def residueRank (S : Finset K) (w : K → ι → K) : ℕ :=
  finrank K (LinearMap.range (residueMatrix S w).mulVecLin)

noncomputable def activeFibres (S : Finset K) (w : K → ι → K) : Finset K :=
  S.filter (fun x => w x ≠ 0)

private noncomputable def lagrangeTest (S T : Finset K) : Matrix (↥T) (↥S) K :=
  fun x y => (Lagrange.basis T id x.1).eval y.1

/-- The tested columns indexed by T have a literal right inverse:
extend a vector on T by zero to S. -/
private theorem lagrangeTest_surjective {S T : Finset K} (hTS : T ⊆ S) :
    Function.Surjective (lagrangeTest S T).mulVecLin := by
  classical
  intro w
  let z : ↥S → K := fun y => if hy : y.1 ∈ T then w ⟨y.1,hy⟩ else 0
  refine ⟨z,?_⟩
  funext x
  let xS : ↥S := ⟨x.1,hTS x.2⟩
  change (∑ y : ↥S, (Lagrange.basis T id x.1).eval y.1 * z y) = w x
  rw [Finset.sum_eq_single xS]
  · have one : (Lagrange.basis T id x.1).eval x.1 = 1 :=
      Lagrange.eval_basis_self (Set.injOn_id _) x.2
    simp only [xS,z,dite_eq_left x.2,one,one_mul]
  · intro y _ ny
    by_cases hy : y.1 ∈ T
    · have different : x.1 ≠ y.1 := fun e => ny (Subtype.ext e.symm)
      have zero : (Lagrange.basis T id x.1).eval y.1 = 0 :=
        Lagrange.eval_basis_of_ne (v := (id : K → K)) different hy
      rw [zero,zero_mul]
    · simp only [z,dite_eq_right hy,mul_zero]
  · intro absent
    exact (absent (Finset.mem_univ xS)).elim

private theorem lagrangeTest_mul_residueMatrix {S T : Finset K} {w : K → ι → K} {d : ℕ}
    (paid : PaidMoments S w d) (size : T.card ≤ d+1) :
    lagrangeTest S T * residueMatrix S w = 0 := by
  classical
  ext x i
  change (∑ y : ↥S, (Lagrange.basis T id x.1).eval y.1 * w y.1 i) = 0
  have eq : (Lagrange.basis T id x.1).natDegree = T.card-1 :=
    Lagrange.natDegree_basis (Set.injOn_id _) x.2
  have degree : (Lagrange.basis T id x.1).natDegree ≤ d := by
    rw [eq]
    omega
  exact (Finset.sum_coe_sort S
    (fun y : K => (Lagrange.basis T id x.1).eval y * w y i)).trans (paid i _ degree)

private theorem finrank_clockFunctions (S : Finset K) :
    finrank K (↥S → K) = S.card :=
  (Module.finrank_fintype_fun_eq_card K).trans (Fintype.card_coe S)

/-- The full rank/nullity statement remains true for zero residues and
even the empty set. The selected test rows have full chosen rank. -/
theorem min_add_residueRank_le_card {S : Finset K} {w : K → ι → K} {d : ℕ}
    (paid : PaidMoments S w d) :
    min S.card (d+1) + residueRank S w ≤ S.card := by
  classical
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq
    (min_le_left S.card (d+1))
  have size : T.card ≤ d+1 := hT.trans_le (min_le_right _ _)
  let L := lagrangeTest S T
  let B := residueMatrix S w
  have z : L * B = 0 := lagrangeTest_mul_residueMatrix paid size
  have inside : LinearMap.range B.mulVecLin ≤ LinearMap.ker L.mulVecLin := by
    apply LinearMap.range_le_ker_iff.mpr
    rw [←Matrix.mulVecLin_mul,z,Matrix.mulVecLin_zero]
  have hker : residueRank S w ≤ finrank K (LinearMap.ker L.mulVecLin) :=
    Submodule.finrank_mono inside
  have top : LinearMap.range L.mulVecLin = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (lagrangeTest_surjective hTS)
  have equal := L.mulVecLin.finrank_range_add_finrank_ker
  rw [top,finrank_top,finrank_clockFunctions T,finrank_clockFunctions S] at equal
  rw [←hT]
  exact (Nat.add_le_add_left hker T.card).trans_eq equal

/-- Filtering a zero row does not change any paid column moment. -/
theorem paidMoments_active {S : Finset K} {w : K → ι → K} {d : ℕ}
    (paid : PaidMoments S w d) :
    PaidMoments (activeFibres S w) w d := by
  classical
  intro i P hd
  have sub : activeFibres S w ⊆ S := Finset.filter_subset _ _
  refine (Finset.sum_subset sub ?_).trans (paid i P hd)
  intro x hx hnx
  have wx : w x = 0 := by
    by_contra nz
    exact hnx (Finset.mem_filter.mpr ⟨hx,nz⟩)
  simp only [wx,Pi.zero_apply,mul_zero]

/-- A nonzero actual entry certifies positivity of the same rank. -/
theorem residueRank_pos_of_entry {S : Finset K} {w : K → ι → K} {x : K} {i : ι}
    (hx : x ∈ S) (nz : w x i ≠ 0) :
    0 < residueRank S w := by
  classical
  let B := residueMatrix S w
  let e : ι → K := Pi.single i 1
  let v : LinearMap.range B.mulVecLin := ⟨B.mulVecLin e,⟨e,rfl⟩⟩
  refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v,?_⟩
  intro h
  have t := congrArg (fun a : LinearMap.range B.mulVecLin => a.1 ⟨x,hx⟩) h
  change B.mulVecLin e ⟨x,hx⟩ = 0 at t
  rw [Matrix.mulVecLin_apply,show e = Pi.single i 1 from rfl,Matrix.mulVec_single_one] at t
  exact nz t

/-- For positive actual rank r, there are at least d+1+r active clocks. -/
theorem active_card_of_paid_rank_pos {S : Finset K} {w : K → ι → K} {d : ℕ}
    (paid : PaidMoments S w d)
    (pos : 0 < residueRank (activeFibres S w) w) :
    d+1+residueRank (activeFibres S w) w ≤ (activeFibres S w).card := by
  have h := min_add_residueRank_le_card (paidMoments_active paid)
  by_cases size : d+1 ≤ (activeFibres S w).card
  · simpa only [min_eq_right size] using h
  · rw [min_eq_left (by omega : (activeFibres S w).card ≤ d+1)] at h
    omega

theorem active_card_of_paid_nonzero_entry {S : Finset K} {w : K → ι → K} {d : ℕ}
    (paid : PaidMoments S w d) {x : K} {i : ι} (hx : x ∈ S) (nz : w x i ≠ 0) :
    d+1+residueRank (activeFibres S w) w ≤ (activeFibres S w).card := by
  apply active_card_of_paid_rank_pos paid
  apply residueRank_pos_of_entry (i := i) _ nz
  have notZero : w x ≠ 0 := fun e => nz (congrFun e i)
  exact Finset.mem_filter.mpr ⟨hx,notZero⟩

end RKResearch.Certified.Graded.ResidueMomentRank

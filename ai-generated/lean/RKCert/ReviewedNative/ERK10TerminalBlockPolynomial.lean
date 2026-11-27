module

public import RKResearch.OrderConditions
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed mixed-moment invariant for the terminal-deletion chart.
The scalar tests use only ordinary rooted conditions through nine. -/

namespace RKResearch.Certified.ERK10TerminalBlockPolynomial
open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- Polynomial \((6X-2)(6X-4)\), split by degree. -/
def pCoeff : Fin 3 → R := ![8,-36,36]

/-- Polynomial \(6X(6X-2)(6X-3)(6X-4)(6X-6)\),
with its zero constant term omitted. -/
def qCoeff : Fin 5 → R := ![864,-6480,17280,-19440,7776]

def pVec (x : ι → R) : ι → R :=
  ∑ j : Fin 3, (pCoeff j : R) • x^(j.val)

def qVec (x : ι → R) : ι → R :=
  ∑ k : Fin 5, (qCoeff k : R) • x^(k.val+1)

def testTree (j : Fin 3) (k : Fin 5) : FiniteRootedTree :=
  (bushyTree (Nat.succPNat j.val)) ◂ (bushyTree (Nat.succPNat (k.val+1)))

theorem test_size : ∀ (j : Fin 3) (k : Fin 5),
    ((testTree j k).order : ℕ) ≤ 9 := by decide +kernel

theorem test_pays : ∀ (j : Fin 3) (k : Fin 5),
    ((testTree j k).factorial : ℕ) ∣ (Nat.factorial 10)^2 := by decide +kernel

theorem test_profile (A : Matrix ι ι R) (j : Fin 3) (k : Fin 5) :
    Φ (testTree j k) A =
      (A *ᵥ 1)^j.val * (A *ᵥ ((A *ᵥ 1)^(k.val+1))) := by
  simp only [testTree,Φ]
  rw [Φ_bushyTree,Φ_bushyTree]
  rfl

theorem test_moment (hpay : IsUnit (Nat.factorial 10:R))
    {A B : Matrix ι ι R} {w v : ι→R}
    (hA : HasOrder 9 A w) (hB : HasOrder 9 B v)
    (j : Fin 3) (k : Fin 5) : (w ⬝ᵥ Φ (testTree j k) A) =
      (v ⬝ᵥ Φ (testTree j k) B) := by
  have hsq : IsUnit (((Nat.factorial 10)^2:ℕ):R) := by
    simpa only [Nat.cast_pow] using hpay.pow 2
  have hu : IsUnit (((testTree j k).factorial : ℕ):R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) (test_pays j k)) hsq
  apply hu.mul_left_cancel
  exact (hA _ (test_size j k)).trans (hB _ (test_size j k)).symm

def observation (A : Matrix ι ι R) (w : ι → R) : R :=
  w ⬝ᵥ (pVec (A *ᵥ 1) * (A *ᵥ qVec (A *ᵥ 1)))

theorem expand (A : Matrix ι ι R) (w : ι → R) :
    observation A w = ∑ j : Fin 3, ∑ k : Fin 5,
        ((pCoeff j : R)*qCoeff k)*(w ⬝ᵥ Φ (testTree j k) A) := by
  simp only [observation,pVec,qVec,Matrix.mulVec_sum,Matrix.mulVec_smul,
    Finset.sum_mul,Finset.mul_sum,dotProduct_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [test_profile]
  have h :
      ((pCoeff j : R) • (A *ᵥ 1)^j.val) *
        ((qCoeff k : R) • (A *ᵥ ((A *ᵥ 1)^(k.val+1)))) =
          ((pCoeff j : R)*(qCoeff k : R)) •
            ((A *ᵥ 1)^j.val * (A *ᵥ ((A *ᵥ 1)^(k.val+1)))) := by
    funext i
    simp only [Pi.smul_apply,Pi.mul_apply,smul_eq_mul]
    ring
  rw [h,dotProduct_smul,smul_eq_mul]

theorem observation_eq (hpay : IsUnit (Nat.factorial 10:R))
    {A B : Matrix ι ι R} {w v : ι→R}
    (hA : HasOrder 9 A w) (hB : HasOrder 9 B v) :
    observation A w = observation B v := by
  rw [expand,expand]
  simp_rw [test_moment hpay hA hB]

/-- If every surviving row's contribution is unchanged, deleting one
nonzero contribution is incompatible with ordinary rooted order nine. -/
theorem last_contribution_impossible (hpay : IsUnit (Nat.factorial 10:R))
    {A B : Matrix ι ι R} {w v : ι→R}
    (hA : HasOrder 9 A w) (hB : HasOrder 9 B v)
    (last : ι)
    (same : ∀ i, i≠last →
      w i*(pVec (A *ᵥ 1) i * (A *ᵥ qVec (A *ᵥ 1)) i) =
      v i*(pVec (B *ᵥ 1) i * (B *ᵥ qVec (B *ᵥ 1)) i))
    (h0 : v last=0)
    (hn : w last*(pVec (A *ᵥ 1) last * (A *ᵥ qVec (A *ᵥ 1)) last)≠0) :
    False := by
  classical
  let X := fun i => w i*(pVec (A *ᵥ 1) i * (A *ᵥ qVec (A *ᵥ 1)) i)
  let Y := fun i => v i*(pVec (B *ᵥ 1) i * (B *ᵥ qVec (B *ᵥ 1)) i)
  have heq : ∑ i, X i = ∑ i, Y i := observation_eq hpay hA hB
  have hs : (∑ i, (X i - Y i)) = 0 := by rw [Finset.sum_sub_distrib,heq,sub_self]
  have hSingle :
      (∑ i, (X i - Y i)) = X last - Y last :=
    Finset.sum_eq_single last
      (fun i _ h => sub_eq_zero.mpr (same i h))
      (fun hf => (hf (Finset.mem_univ last)).elim)
  rw [hSingle] at hs
  apply hn
  simpa only [X,Y,h0,zero_mul,sub_zero] using hs

end RKResearch.Certified.ERK10TerminalBlockPolynomial

#print axioms RKResearch.Certified.ERK10TerminalBlockPolynomial.observation_eq
#print axioms RKResearch.Certified.ERK10TerminalBlockPolynomial.last_contribution_impossible

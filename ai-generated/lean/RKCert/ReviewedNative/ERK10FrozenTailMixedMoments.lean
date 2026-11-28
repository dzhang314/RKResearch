module

public import RKCert.ReviewedNative.ERK10TerminalBlockHalfPort
import Mathlib.Tactic.Ring

@[expose] public section

/-! Arbitrary bivariate mixed bush moments of bounded total degree, and
exact grouping by the published ten-clock grid. -/
namespace RKResearch.Certified.ERK10FrozenTailMixedMoments
open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators
open ERK10TerminalBlockClockAdapter ERK10UniversalSeventeen ERK10TerminalBlockHalfPort
set_option maxHeartbeats 0
set_option maxRecDepth 30000

structure Monomial where
  outExp : Fin 9
  inExp : Fin 9
  coeff : ℤ

def ttree (j k : Fin 9) : FiniteRootedTree :=
  (bushyTree (Nat.succPNat j.val)) ◂ (bushyTree (Nat.succPNat k.val))

theorem tree_bound : ∀ j k : Fin 9, j.val+k.val+2≤10 →
    ((ttree j k).order:ℕ)≤10 := by decide +kernel

theorem tree_paid : ∀ j k : Fin 9, j.val+k.val+2≤10 →
    ((ttree j k).factorial:ℕ)∣(Nat.factorial 10)^2 := by decide +kernel

variable {R ι : Type*} [CommRing R] [Fintype ι]

theorem ttree_read (A : Matrix ι ι R) (j k : Fin 9) :
    Φ (ttree j k) A = (A *ᵥ 1)^j.val * (A *ᵥ ((A *ᵥ 1)^k.val)) := by
  simp only [ttree,Φ]
  rw [Φ_bushyTree,Φ_bushyTree]
  rfl

theorem single_read (hpay : IsUnit (Nat.factorial 10:R))
    {A B : Matrix ι ι R} {w v : ι → R}
    (hA : HasOrder 10 A w) (hB : HasOrder 10 B v)
    (j k : Fin 9) (h : j.val+k.val+2≤10) :
    (w ⬝ᵥ Φ (ttree j k) A) = (v ⬝ᵥ Φ (ttree j k) B) := by
  have H : IsUnit (((Nat.factorial 10)^2:ℕ):R) := by
    simpa only [Nat.cast_pow] using hpay.pow 2
  have U : IsUnit (((ttree j k).factorial:ℕ):R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) (tree_paid j k h)) H
  exact U.mul_left_cancel
    ((hA _ (tree_bound j k h)).trans (hB _ (tree_bound j k h)).symm)

variable {n : ℕ}
def eval (T : Fin n → Monomial) (x z : R) : R :=
  ∑ t, ((T t).coeff:R)*x^(T t).outExp.val*z^(T t).inExp.val

def score (T : Fin n → Monomial) (A : Matrix ι ι R) (i : ι) : R :=
  ∑ j, A i j * eval T ((6:R)*(A *ᵥ 1) i) ((6:R)*(A *ᵥ 1) j)

theorem score_expand (T : Fin n → Monomial) (A : Matrix ι ι R) (i : ι) :
    score T A i = ∑ t, (((T t).coeff:R)*(6:R)^(T t).outExp.val*
        (6:R)^(T t).inExp.val)* Φ (ttree (T t).outExp (T t).inExp) A i := by
  simp only [score,eval,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ttree_read,Pi.mul_apply,Pi.pow_apply,mul_pow]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.pow_apply,Matrix.mulVec,dotProduct]
  ring

theorem dot_expand (T : Fin n → Monomial) (A : Matrix ι ι R) (w : ι→R) :
    (w ⬝ᵥ score T A) = ∑ t, (((T t).coeff:R)*(6:R)^(T t).outExp.val*
        (6:R)^(T t).inExp.val)*(w ⬝ᵥ Φ (ttree (T t).outExp (T t).inExp) A) := by
  simp only [dotProduct,score_expand,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem score_agrees (T : Fin n → Monomial)
    (hT : ∀ t, (T t).outExp.val+(T t).inExp.val+2≤10)
    (hpay : IsUnit (Nat.factorial 10:R))
    {A B : Matrix ι ι R} {w v : ι→R}
    (hA : HasOrder 10 A w) (hB : HasOrder 10 B v) :
    (w ⬝ᵥ score T A) = (v ⬝ᵥ score T B) := by
  rw [dot_expand,dot_expand]
  exact Finset.sum_congr rfl fun t _ => by rw [single_read hpay hA hB _ _ (hT t)]

def loadInt (T : Fin n → Monomial) (i j : Fin 17) : ℤ :=
  eval T (node (sixClockIndex i)) (node (sixClockIndex j))

theorem score_grid (T : Fin n → Monomial) {A : Matrix (Fin 17) (Fin 17) R}
    (h : GridClocks (A *ᵥ 1)) (i : Fin 17) :
    score T A i = ∑ j, A i j * (loadInt T i j:R) := by
  simp only [score]
  apply Finset.sum_congr rfl
  intro j _
  rw [h i,h j]
  simp only [loadInt,eval,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_id]

def aScore (T : Fin n → Monomial) (i : Fin 17) : ℤ :=
  ∑ j, aNum i j*loadInt T i j
def uScore (T : Fin n → Monomial) (i : Fin 17) : ℤ :=
  ∑ j, uNum i j*loadInt T i j
def vScore (T : Fin n → Monomial) (i : Fin 17) : ℤ :=
  ∑ j, vNum i j*loadInt T i j

theorem score_family (T : Fin n → Monomial) (d l m : R) (hd : (D:R)*d=1) (i : Fin 17) :
    score T (familyA d l m) i = d*((aScore T i:R)+l*(uScore T i:R)+m*(vScore T i:R)) := by
  rw [score_grid T (family_clock d l m hd)]
  simp only [aScore,uScore,vScore,Int.cast_sum,Int.cast_mul,familyA]
  calc
    _ = ∑ j, d*((aNum i j:R)*(loadInt T i j:R) +
        l*((uNum i j:R)*(loadInt T i j:R)) +
        m*((vNum i j:R)*(loadInt T i j:R))) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum]

def groupWeight (b : Fin 17→R) (g : Fin 10) : R :=
  ∑ i, if sixClockIndex i=g then b i else 0

theorem card_group {c b : Fin 17→R} (hc : GridClocks c) (g : Fin 10) :
    (b ⬝ᵥ cardVec g c) = groupWeight b g*(pivot g:R) := by
  rw [cardVec_grid g hc,dotProduct,groupWeight,Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : sixClockIndex i=g
  · simp only [h,ite_true]
  · have H : g≠sixClockIndex i := fun a => h a.symm
    simp only [h,H,ite_false,mul_zero,zero_mul]

theorem weight_group_agrees {c e b v : Fin 17→R}
    (hpay : IsUnit (Nat.factorial 10:R))
    (hc : GridClocks c) (he : GridClocks e)
    (h : HasQuadratureOrder 10 b c) (h' : HasQuadratureOrder 10 v e)
    (g : Fin 10) :
    groupWeight b g=groupWeight v g := by
  have H := card_agrees g h h'
  rw [card_group hc g,card_group he g] at H
  exact (pivot_unit hpay g).mul_right_cancel H

theorem integrate_groups (b : Fin 17→R) (f : Fin 10→R) :
    (b ⬝ᵥ fun i => f (sixClockIndex i)) = ∑ g, groupWeight b g*f g := by
  simp only [dotProduct,groupWeight,Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  symm
  calc
    _ = (if sixClockIndex i=sixClockIndex i then b i else 0)*f (sixClockIndex i) := by
      refine Finset.sum_eq_single (sixClockIndex i) ?_ (fun h => (h (Finset.mem_univ _)).elim)
      intro g _ hg
      have H : sixClockIndex i≠g := fun h => hg h.symm
      simp only [H,ite_false,zero_mul]
    _ = _ := by simp only [ite_true]

theorem grid_integrate_agrees {c e b v : Fin 17→R}
    (hpay : IsUnit (Nat.factorial 10:R))
    (hc : GridClocks c) (he : GridClocks e)
    (h : HasQuadratureOrder 10 b c) (h' : HasQuadratureOrder 10 v e)
    (f : Fin 10→R) :
    (b ⬝ᵥ fun i => f (sixClockIndex i)) = (v ⬝ᵥ fun i => f (sixClockIndex i)) := by
  simp only [integrate_groups,weight_group_agrees hpay hc he h h']

end RKResearch.Certified.ERK10FrozenTailMixedMoments

#print axioms RKResearch.Certified.ERK10FrozenTailMixedMoments.score_agrees
#print axioms RKResearch.Certified.ERK10FrozenTailMixedMoments.grid_integrate_agrees

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-!
A scalar obstruction for one order-eleven splice design:
seven fixed centered reverse sites cannot be augmented by
only three new scalar sites over the prime field of order thirteen.
This is not a stage-count theorem for arbitrary tableaux.
-/

namespace RKResearch.Certified.ERK11FixedSevenPortsF13

abbrev F := ZMod 13
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The monic hull of the seven fixed sites, in characteristic thirteen. -/
def H (x : F) : F := x^7-x^5+4*x^3+9*x

theorem fixed_roots :
    ∀ x : F, H x=0 ↔
      x=0 ∨ x=1 ∨ x=(-1) ∨ x=6 ∨ x=(-6) ∨ x=4 ∨ x=(-4) := by
  decide +kernel

def moment (k : ℕ) : F := if k%2=0 then ((k+1:ℕ):F)⁻¹ else 0
def xpower (k : ℕ) : F→F := fun x => x^k
def hpower (k : ℕ) : F→F := fun x => H x*x^k
def HasMoments (μ : (F→F) →ₗ[F] F) : Prop :=
  ∀ k ≤ 10, μ (xpower k)=moment k

def SupportedPair (μ : (F→F) →ₗ[F] F) (a b : F) : Prop :=
  ∀ f, (∀ x, H x=0 → f x=0) → f a=0 → f b=0 → μ f=0

def SupportedTriple (μ : (F→F) →ₗ[F] F) (a b c : F) : Prop :=
  ∀ f, (∀ x, H x=0 → f x=0) → f a=0 → f b=0 → f c=0 → μ f=0

private theorem readH {μ : (F→F) →ₗ[F] F} (hm : HasMoments μ)
    (k : ℕ) (hk : k ≤ 3) :
    μ (hpower k)=moment (k+7)-moment (k+5)+4*moment (k+3)+9*moment (k+1) := by
  have h : hpower k = xpower (k+7)-xpower (k+5)+(4:F)•xpower (k+3)+(9:F)•xpower (k+1) := by
    funext x
    simp only [hpower,H,xpower,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pow_add]
    ring
  rw [h,map_add,map_add,map_sub,map_smul,map_smul,
    hm (k+7) (by omega),hm (k+5) (by omega),hm (k+3) (by omega),hm (k+1) (by omega)]
  norm_num

private theorem h0 {μ : (F→F) →ₗ[F] F} (hm : HasMoments μ) : μ (hpower 0)=0 := by
  rw [readH hm 0 (by decide)]
  decide +kernel
private theorem h1 {μ : (F→F) →ₗ[F] F} (hm : HasMoments μ) : μ (hpower 1)=10 := by
  rw [readH hm 1 (by decide)]
  decide +kernel
private theorem h2 {μ : (F→F) →ₗ[F] F} (hm : HasMoments μ) : μ (hpower 2)=0 := by
  rw [readH hm 2 (by decide)]
  decide +kernel
private theorem h3 {μ : (F→F) →ₗ[F] F} (hm : HasMoments μ) : μ (hpower 3)=5 := by
  rw [readH hm 3 (by decide)]
  decide +kernel

private theorem readPair (μ : (F→F) →ₗ[F] F) (a b : F) (k : ℕ) :
    μ (fun x => H x*x^k*(x-a)*(x-b)) =
      μ (hpower (k+2))-(a+b)*μ (hpower (k+1))+a*b*μ (hpower k) := by
  have h : (fun x => H x*x^k*(x-a)*(x-b)) =
      hpower (k+2)-(a+b)•hpower (k+1)+(a*b)•hpower k := by
    funext x
    simp only [hpower,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pow_add,pow_one]
    ring
  rw [h,map_add,map_sub,map_smul,map_smul]
  rfl

private theorem readTriple (μ : (F→F) →ₗ[F] F) (a b c : F) :
    μ (fun x => H x*(x-a)*(x-b)*(x-c)) =
      μ (hpower 3)-(a+b+c)*μ (hpower 2)+(a*b+a*c+b*c)*μ (hpower 1)-a*b*c*μ (hpower 0) := by
  have h : (fun x => H x*(x-a)*(x-b)*(x-c)) =
      hpower 3-(a+b+c)•hpower 2+(a*b+a*c+b*c)•hpower 1-(a*b*c)•hpower 0 := by
    funext x
    simp only [hpower,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [h,map_sub,map_add,map_sub,map_smul,map_smul,map_smul]
  rfl

private theorem pairs :
    ∀ a b : F, a+b=0 → a*b≠6 := by decide +kernel

private theorem triples :
    ∀ a b c : F, a*b+a*c+b*c=6 →
      H a=0 ∨ H b=0 ∨ H c=0 ∨ a=b ∨ a=c ∨ b=c := by
  decide +kernel

private theorem ordinary_six : (10:F)*(-6)=5 := by decide +kernel

private theorem cancel_ten (x : F) (h : (10:F)*x=0) : x=0 := by
  calc
    x = (4:F)*((10:F)*x) := by rw [←mul_assoc,show (4:F)*10=1 by decide +kernel,one_mul]
    _ = 0 := by rw [h,mul_zero]

theorem no_pair (μ : (F→F) →ₗ[F] F) (hm : HasMoments μ)
    (a b : F) (hs : SupportedPair μ a b) : False := by
  have hz (k : ℕ) : μ (fun x => H x*x^k*(x-a)*(x-b))=0 := by
    apply hs
    · intro x hx
      simp [hx]
    · simp
    · simp
  have z0 := hz 0
  have z1 := hz 1
  rw [readPair, h2 hm, h1 hm, h0 hm] at z0
  rw [readPair, h3 hm, h2 hm, h1 hm, ←ordinary_six] at z1
  have u : (10:F)*(a+b)=0 := by linear_combination -z0
  have v : (10:F)*(a*b-6)=0 := by linear_combination z1
  apply pairs a b (cancel_ten _ u)
  exact sub_eq_zero.mp (cancel_ten _ v)

theorem no_triple (μ : (F→F) →ₗ[F] F) (hm : HasMoments μ)
    (a b c : F) (hs : SupportedTriple μ a b c) : False := by
  have hz : μ (fun x => H x*(x-a)*(x-b)*(x-c))=0 := by
    apply hs
    · intro x hx
      simp [hx]
    · simp
    · simp
    · simp
  rw [readTriple, h3 hm, h2 hm, h1 hm, h0 hm, ←ordinary_six] at hz
  have v : (10:F)*(a*b+a*c+b*c-6)=0 := by linear_combination hz
  have hv := sub_eq_zero.mp (cancel_ten _ v)
  rcases triples a b c hv with ha|hb|hc|hab|hac|hbc
  · exact no_pair μ hm b c (fun f h fb fc => hs f h (h a ha) fb fc)
  · exact no_pair μ hm a c (fun f h fa fc => hs f h fa (h b hb) fc)
  · exact no_pair μ hm a b (fun f h fa fb => hs f h fa fb (h c hc))
  · exact no_pair μ hm b c (fun f h fb fc => hs f h (by simpa [hab] using fb) fb fc)
  · exact no_pair μ hm b c (fun f h fb fc => hs f h (by simpa [hac] using fc) fb fc)
  · exact no_pair μ hm a c (fun f h fa fc => hs f h fa (by simpa [hbc] using fc) fc)

open scoped BigOperators

/-- No degree-ten centered quadrature, even with signed weights or
colliding labels, supported by the seven fixed ports and three others. -/
theorem no_weighted_rule {ι : Type*} [Fintype ι] (x w : ι → F)
    (a b c : F)
    (hsite : ∀ i, H (x i)=0 ∨ x i=a ∨ x i=b ∨ x i=c)
    (hm : ∀ k ≤ 10, ∑ i, w i*(x i)^k = moment k) : False := by
  let μ : (F→F) →ₗ[F] F :=
    { toFun := fun f => ∑ i, w i*f (x i)
      map_add' := by
        intro f g
        simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro s f
        change (∑ i, w i*(s*f (x i)))=s*(∑ i, w i*f (x i))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  apply no_triple μ (by intro k hk; exact hm k hk) a b c
  intro f hp ha hb hc
  apply Finset.sum_eq_zero
  intro i _
  rcases hsite i with h0|h1|h2|h3
  · rw [hp _ h0,mul_zero]
  · rw [h1,ha,mul_zero]
  · rw [h2,hb,mul_zero]
  · rw [h3,hc,mul_zero]

end RKResearch.Certified.ERK11FixedSevenPortsF13

#print axioms RKResearch.Certified.ERK11FixedSevenPortsF13.no_triple

#print axioms RKResearch.Certified.ERK11FixedSevenPortsF13.no_weighted_rule

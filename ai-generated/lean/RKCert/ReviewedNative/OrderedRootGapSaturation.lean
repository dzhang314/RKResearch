module

public import RKCert.ReviewedNative.FiniteRootSeparator
public import Mathlib.Algebra.Polynomial.Eval.Coeff
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Fill all selected polynomial sign gaps by finite root saturation

Draft. The only new field-theoretic input is a single-gap extension.
Maximize the *finite number of distinct roots*, not the field itself.
-/
namespace RKCert.ReviewedNative.OrderedRootGapSaturation

open Polynomial Set
open RKCert.ReviewedNative.FiniteRootSeparator

universe u

/-- An explicitly ordered extension in the same universe. -/
structure OrderedExtension (K : Type u) [Field K] [LinearOrder K] where
  carrier : Type u
  [field : Field carrier]
  [order : LinearOrder carrier]
  [strict : IsStrictOrderedRing carrier]
  embed : K →+* carrier
  mono : StrictMono embed

attribute [instance] OrderedExtension.field OrderedExtension.order OrderedExtension.strict

noncomputable section

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def identity (K : Type u) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    OrderedExtension K where
  carrier := K
  embed := RingHom.id K
  mono := strictMono_id

abbrev followedBy (E : OrderedExtension K) (F : OrderedExtension E.carrier) :
    OrderedExtension K where
  carrier := F.carrier
  field := F.field
  order := F.order
  strict := F.strict
  embed := F.embed.comp E.embed
  mono := F.mono.comp E.mono

def rootInGap (E : OrderedExtension K) (p : K[X]) (a b : K) : Prop :=
  ∃ x : E.carrier, E.embed a<x ∧ x<E.embed b ∧ (p.map E.embed).IsRoot x

/-- This is the single ordered-algebraic extension obligation; polynomial
degree, other roots, and saturation do not appear in its interface. -/
def SingleGapFactory : Prop :=
  ∀ (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (p : F[X]) (a b : F), a<b → Opposite (p.eval a) (p.eval b) →
    ∃ E : OrderedExtension F, rootInGap E p a b

def distinctRoots (E : OrderedExtension K) (p : K[X]) : Finset E.carrier :=
  (p.map E.embed).roots.toFinset

theorem distinctRoots_card_le (E : OrderedExtension K) (p : K[X]) :
    (distinctRoots E p).card ≤ p.natDegree := by
  unfold distinctRoots
  calc
    (p.map E.embed).roots.toFinset.card ≤ (p.map E.embed).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (p.map E.embed).natDegree := Polynomial.card_roots' _
    _ = p.natDegree := natDegree_map_eq_of_injective E.embed.injective p

private theorem eval_in_embedded_gap (E : OrderedExtension K) (p : K[X]) {a b : K}
    (s : Opposite (p.eval a) (p.eval b)) :
    Opposite ((p.map E.embed).eval (E.embed a)) ((p.map E.embed).eval (E.embed b)) := by
  rw [eval_on_base,eval_on_base]
  rcases s with ⟨ap,bn⟩ | ⟨an,bp⟩
  · exact Or.inl ⟨by simpa only [map_zero] using E.mono ap,
      by simpa only [map_zero] using E.mono bn⟩
  · exact Or.inr ⟨by simpa only [map_zero] using E.mono an,
      by simpa only [map_zero] using E.mono bp⟩

private theorem opposite_ne_zero_polynomial {p : K[X]} {a b : K}
    (s : Opposite (p.eval a) (p.eval b)) : p ≠ 0 := by
  intro h
  rcases s with ⟨hp,_⟩ | ⟨hn,_⟩
  · simpa only [h,eval_zero,lt_irrefl] using hp
  · simpa only [h,eval_zero,lt_irrefl] using hn

/-- A genuinely new gap root strictly increases the distinct-root count.
This is the only purpose of considering extensions of the current field. -/
theorem grow_distinctRoots (factory : SingleGapFactory.{u})
    (E : OrderedExtension K) (p : K[X]) (a b : K) (ab : a<b)
    (opp : Opposite (p.eval a) (p.eval b)) (missing : ¬ rootInGap E p a b) :
    ∃ F : OrderedExtension K, (distinctRoots E p).card < (distinctRoots F p).card := by
  classical
  obtain ⟨D,r,ar,rb,rr⟩ := factory E.carrier (p.map E.embed) (E.embed a) (E.embed b)
    (E.mono ab) (eval_in_embedded_gap E p opp)
  let G := followedBy E D
  let em : E.carrier ↪ G.carrier := ⟨D.embed,D.embed.injective⟩
  have poly : (p.map E.embed).map D.embed = p.map G.embed := by
    simp only [G,followedBy,map_map]
  have pn : p≠0 := opposite_ne_zero_polynomial opp
  have pnE : p.map E.embed ≠ 0 := (Polynomial.map_ne_zero_iff E.embed.injective).2 pn
  have pnG : p.map G.embed ≠ 0 := (Polynomial.map_ne_zero_iff G.embed.injective).2 pn
  have oldRoot {x : E.carrier} : x ∈ distinctRoots E p ↔ (p.map E.embed).IsRoot x := by
    simp only [distinctRoots,Multiset.mem_toFinset,Polynomial.mem_roots pnE]
  have newRoot {x : G.carrier} : x ∈ distinctRoots G p ↔ (p.map G.embed).IsRoot x := by
    simp only [distinctRoots,Multiset.mem_toFinset,Polynomial.mem_roots pnG]
  have oldImage : (distinctRoots E p).map em ⊆ distinctRoots G p := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    apply newRoot.mpr
    change (p.map G.embed).eval (D.embed x)=0
    rw [← poly,eval_on_base,show (p.map E.embed).eval x=0 from oldRoot.mp hx,map_zero]
  have found : r ∈ distinctRoots G p := by
    apply newRoot.mpr
    rwa [← poly]
  have fresh : r ∉ (distinctRoots E p).map em := by
    intro old
    obtain ⟨x,hx,eq⟩ := Finset.mem_map.mp old
    change D.embed x=r at eq
    rw [← eq] at ar rb
    exact missing ⟨x,D.mono.lt_iff_lt.mp ar,D.mono.lt_iff_lt.mp rb,oldRoot.mp hx⟩
  have incl : insert r ((distinctRoots E p).map em) ⊆ distinctRoots G p :=
    Finset.insert_subset_iff.2 ⟨found,oldImage⟩
  have hc := Finset.card_le_card incl
  rw [Finset.card_insert_of_notMem fresh,Finset.card_map] at hc
  exact ⟨G,Nat.lt_of_succ_le hc⟩

/-- Saturate all base gaps for one p by requesting a maximal distinct
root count. No real-closure object or completeness of the base is used. -/
theorem unitRootSource_of_singleGapFactory (factory : SingleGapFactory.{u}) (p : K[X]) :
    ∃ E : OrderedExtension K, UnitRootSource E.embed p := by
  classical
  let S := (Finset.range (p.natDegree+1)).filter
    (fun n => ∃ E : OrderedExtension K, (distinctRoots E p).card=n)
  have mem (E : OrderedExtension K) : (distinctRoots E p).card ∈ S :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (distinctRoots_card_le E p)),⟨E,rfl⟩⟩
  have Sne : S.Nonempty := ⟨_,mem (identity K)⟩
  let n := S.max' Sne
  obtain ⟨E,hE⟩ := (Finset.mem_filter.mp (Finset.max'_mem S Sne)).2
  refine ⟨E,?_⟩
  intro a b _ _ ab opp
  by_contra missing
  obtain ⟨F,larger⟩ := grow_distinctRoots factory E p a b ab opp missing
  have leMax : (distinctRoots F p).card ≤ n := Finset.le_max' S _ (mem F)
  change (distinctRoots E p).card=n at hE
  omega

end
end RKCert.ReviewedNative.OrderedRootGapSaturation

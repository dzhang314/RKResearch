module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Endpoint debit for signed ordinary moment supports

The physical rows in `D` are already charged, and the other physical
origin/terminal rows are distinct. Either the off-reference count leaves
room for another row, or the only uncharged on-reference rows are the
two endpoints and the terminal residual is exactly zero. -/
namespace RKResearch.Certified.Graded.OneClockEndpointDebit

open Polynomial
open scoped BigOperators
noncomputable section

variable {K ι : Type*} [Field K]

/-- Aggregate mass on one literal clock fiber of a finite physical set. -/
def fiberMass (I : Finset ι) (c b : ι → K) (x : K) : K := by
  classical
  exact ∑ i ∈ I.filter (fun i => c i=x), b i

private theorem fiberMass_zero_of_absent (I : Finset ι) (c b : ι → K) (x : K)
    (off : ∀ i∈I, c i≠x) : fiberMass I c b x=0 := by
  classical
  unfold fiberMass
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hm,e⟩ := Finset.mem_filter.mp hi
  exact (off i hm e).elim

/-- A spent collection of physical rows leaves one more support debit
than simple row counting, when the actual last physical weight matches
the reference terminal weight. No ordered or infinite field is needed. -/
theorem exists_endpoint_debited_support [Fintype ι] [DecidableEq ι] (D : Finset ι) (L : Finset K)
    (c b : ι → K) (ν : K → K) {o t : ι} (apart : o≠t)
    (oc : c o=0) (tc : c t=1) (zero : (0:K)∈L) (one : (1:K)∈L)
    (oD : o∉D) (tD : t∉D) (atOne : b t=ν 1) (ref : ∀ x∉L,ν x=0) :
    ∃ J : Finset K, J.card+D.card+3≤Fintype.card ι+L.card ∧
      ∀ x∉J, fiberMass (Finset.univ \ D) c b x=ν x := by
  classical
  let E : Finset ι := {o,t}
  let B : Finset ι := (Finset.univ \ D).filter (fun i => c i∉L)
  let C := B.image c
  let U := D∪E
  have Ec : E.card=2 := Finset.card_pair apart
  have DE : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro i hi em
    rcases Finset.mem_insert.mp em with rfl | hu
    · exact oD hi
    · have e := Finset.mem_singleton.mp hu
      subst i
      exact tD hi
  have Uc : U.card = D.card+2 := by
    rw [Finset.card_union_of_disjoint DE,Ec]
  have sub : B ⊆ Finset.univ \ U := by
    intro i hi
    obtain ⟨s,m⟩ := Finset.mem_filter.mp hi
    have no : i∉U := by
      intro u
      rcases Finset.mem_union.mp u with d | ee
      · exact (Finset.mem_sdiff.mp s).2 d
      · rcases Finset.mem_insert.mp ee with rfl | h
        · exact m (oc.symm ▸ zero)
        · have e := Finset.mem_singleton.mp h
          subst i
          exact m (tc.symm ▸ one)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,no⟩
  have Dsum : (Finset.univ \ U).card + (D.card+2) = Fintype.card ι := by
    rw [←Uc,Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),Finset.card_univ]
  have count := Finset.card_le_card sub
  have Cc : C.card≤B.card := Finset.card_image_le
  have drop (x : K) (off : x∉L) (no : x∉C) : fiberMass (Finset.univ \ D) c b x=ν x := by
    rw [ref x off]
    apply fiberMass_zero_of_absent
    intro i hi e
    apply no
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,e.symm ▸ off⟩,e⟩
  by_cases full : B.card=(Finset.univ \ U).card
  · have beq := Finset.eq_of_subset_of_card_le sub full.ge
    have tOnly (i : ι) (iD : i∉D) (ci : c i=1) : i=t := by
      by_contra ne
      have io : i≠o := by intro e; subst i; exact zero_ne_one (oc.symm.trans ci)
      have notU : i∉U := by
        intro iu
        have e := (Finset.mem_union.mp iu).resolve_left iD
        exact (Finset.mem_insert.mp e).elim io (fun x=>ne (Finset.mem_singleton.mp x))
      have h : i∈B := by rw [beq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,notU⟩
      exact (Finset.mem_filter.mp h).2 (ci.symm ▸ one)
    have mt : fiberMass (Finset.univ \ D) c b (1:K)=b t := by
      unfold fiberMass
      have single : (Finset.univ \ D).filter (fun i => c i=1)={t} := by
        ext i
        constructor
        · intro m
          obtain ⟨u,ci⟩ := Finset.mem_filter.mp m
          exact Finset.mem_singleton.mpr (tOnly i (Finset.mem_sdiff.mp u).2 ci)
        · intro m
          have e := Finset.mem_singleton.mp m
          subst i
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,tD⟩,tc⟩
      rw [single,Finset.sum_singleton]
    let J := C∪L.erase 1
    have jc : J.card≤C.card+(L.erase 1).card := Finset.card_union_le _ _
    have lc := Finset.card_erase_of_mem one
    have lp : 0<L.card := Finset.card_pos.mpr ⟨1,one⟩
    have lm : (L.erase 1).card+1=L.card := by omega
    refine ⟨J,by omega,?_⟩
    intro x hx
    by_cases ex : x=1
    · subst x
      exact mt.trans atOne
    · refine drop x ?_ (fun h=>hx (Finset.mem_union_left _ h))
      intro h
      exact hx (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ex,h⟩))
  · let J := C∪L
    have jc : J.card≤C.card+L.card := Finset.card_union_le _ _
    refine ⟨J,by omega,?_⟩
    intro x hx
    exact drop x (fun h=>hx (Finset.mem_union_right _ h)) (fun h=>hx (Finset.mem_union_left _ h))

private def nodal (S : Finset K) : K[X] := ∏ x∈S,(X-C x)

/-- A field measure on at most d+1 distinct sites that kills all degree-d
polynomials is zero. This certificate uses a test at each site, not a
positivity assumption. -/
theorem small_support_polynomial_test (J : Finset K) (w : K → K) (d : Nat)
    (small : J.card≤d+1)
    (tests : ∀ P : K[X], P.natDegree≤d → (∑ x∈J,w x * P.eval x)=0) :
    ∀ x∈J,w x=0 := by
  classical
  intro x hx
  let S := J.erase x
  let P := nodal S
  have dp : P.natDegree≤d := by
    have nd : P.natDegree=S.card := natDegree_finsetProd_X_sub_C_eq_card S id
    rw [nd]
    have h := Finset.card_erase_of_mem hx
    dsimp only [S]
    omega
  have test := tests P dp
  have van (y : K) (hy : y∈J) (ne : y≠x) : P.eval y = 0 := by
    rw [show P=nodal S from rfl,nodal,eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ne,hy⟩)
    simp
  rw [Finset.sum_eq_single x] at test
  · have pn : P.eval x≠0 := by
      rw [show P=nodal S from rfl,nodal,eval_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro z hz
      simp only [eval_sub,eval_X,eval_C,sub_ne_zero]
      exact (Finset.ne_of_mem_erase hz).symm
    exact (mul_eq_zero.mp test).resolve_right pn
  · intro y hy ne
    rw [van y hy ne,mul_zero]
  · exact fun n => (n hx).elim

/-- Transfer ordinary power tests to all scalar polynomials of matching
degree. The weights can already contain cleared reciprocal denominators. -/
theorem powers_to_poly (D : Finset ι) (c b : ι→K) {k : Nat}
    (m : ∀ n≤k, (∑ i∈D,b i*(c i)^n)=0) (P : K[X])
    (dp : P.natDegree≤k) : (∑ i∈D,b i*P.eval (c i))=0 := by
  have expansion (x : K) : P.eval x = ∑ n∈Finset.range (k+1),P.coeff n*x^n := by
    conv_lhs => rw [P.as_sum_range' (k+1) (by omega)]
    simp only [eval_finsetSum,eval_monomial]
  simp only [expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  calc
    _ = P.coeff n*(∑ i∈D,b i*(c i)^n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    _ = 0 := by rw [m n (by simpa using hn),mul_zero]

/-- Apply the paid endpoint support debit to an arbitrary scaled residual.
The scale may vanish on already matching sites (for example at the
singularity of a formally zero reciprocal contribution). -/
theorem endpoint_debit_closes_power_tests [Fintype ι] [DecidableEq ι]
    (D : Finset ι) (L W : Finset K) (c b : ι → K) (ν scale : K → K)
    {o t : ι} (apart : o≠t) (oc : c o=0) (tc : c t=1) (zero : (0:K)∈L) (one : (1:K)∈L)
    (oD : o∉D) (tD : t∉D) (atOne : b t=ν 1) (ref : ∀ x∉L,ν x=0)
    (cover : ∀ x∉W, fiberMass (Finset.univ \ D) c b x=ν x)
    (neScale : ∀ x∈W, fiberMass (Finset.univ \ D) c b x≠ν x → scale x≠0)
    {k : Nat} (budget : Fintype.card ι+L.card ≤ (k+1)+D.card+3)
    (tests : ∀ n≤k, (∑ x∈W, (scale x*(fiberMass (Finset.univ \ D) c b x-ν x))*x^n)=0) :
    ∀ x, fiberMass (Finset.univ \ D) c b x=ν x := by
  classical
  obtain ⟨J,jc,matchOut⟩ := exists_endpoint_debited_support D L c b ν apart oc tc zero one oD tD atOne ref
  let T := J∩W
  let w : K → K := fun x => scale x*(fiberMass (Finset.univ \ D) c b x-ν x)
  have Ts : T ⊆ W := Finset.inter_subset_right
  have small : T.card≤k+1 := by
    have cT : T.card≤J.card := Finset.card_le_card Finset.inter_subset_left
    omega
  have testT (n : Nat) (hn : n≤k) : (∑ x∈T, w x*x^n)=0 := by
    have equal : (∑ x∈T,w x*x^n)=(∑ x∈W,w x*x^n) := by
      apply Finset.sum_subset Ts
      intro y hy bad
      have out : y∉J := fun h => bad (Finset.mem_inter.mpr ⟨h,hy⟩)
      simp [w,matchOut y out]
    rw [equal]
    exact tests n hn
  have smallZero : ∀ x∈T,w x=0 :=
    small_support_polynomial_test T w k small (fun P hp => powers_to_poly T id w testT P hp)
  intro x
  by_cases xW : x∈W
  · by_cases xJ : x∈J
    · by_contra mismatch
      have off := smallZero x (Finset.mem_inter.mpr ⟨xJ,xW⟩)
      exact (mul_ne_zero (neScale x xW mismatch) (sub_ne_zero.mpr mismatch)) off
    · exact matchOut x xJ
  · exact cover x xW

/-- Simple reciprocal plus the ordinary reads through degree d gives
one more cleared moment through degree d+1. -/
theorem simple_pole_clears (W : Finset K) (Δ : K → K) (τ : K) (d : Nat)
    (noMass : Δ τ=0)
    (ord : ∀ n≤d, (∑ x∈W,Δ x*x^n)=0)
    (pole : (∑ x∈W,Δ x/(x-τ))=0) :
    ∀ k≤d+1, (∑ x∈W,(Δ x/(x-τ))*x^k)=0 := by
  let M (k : Nat) := ∑ x∈W,(Δ x/(x-τ))*x^k
  have pay (n : Nat) (hn : n≤d) : M (n+1)-τ*M n=0 := by
    dsimp only [M]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←ord n hn]
    apply Finset.sum_congr rfl
    intro x _
    have identity (x : K) : Δ x/(x-τ)*(x-τ)=Δ x := by
      by_cases h : x=τ
      · simp [h,noMass]
      · exact div_mul_cancel₀ _ (sub_ne_zero.mpr h)
    calc
      _ = (Δ x/(x-τ)*(x-τ))*x^n := by rw [pow_succ]; ring
      _ = _ := by rw [identity]
  change ∀ k≤d+1,M k=0
  intro k
  induction k with
  | zero => intro _; simpa [M] using pole
  | succ n ih =>
    intro hn
    have e := pay n (by omega)
    rw [ih (by omega),mul_zero,sub_zero] at e
    exact e

/-- Both reciprocal reads add two cleared moments. A matched pole is
allowed in the ambient finite set, with literal field division at zero. -/
theorem double_pole_clears (W : Finset K) (Δ : K → K) (τ : K) (d : Nat)
    (noMass : Δ τ=0)
    (ord : ∀ n≤d, (∑ x∈W,Δ x*x^n)=0)
    (simple : (∑ x∈W,Δ x/(x-τ))=0)
    (double : (∑ x∈W,Δ x/(x-τ)^2)=0) :
    ∀ k≤d+2, (∑ x∈W,(Δ x/(x-τ)^2)*x^k)=0 := by
  let D (x : K) := Δ x/(x-τ)
  have D0 : D τ=0 := by simp [D]
  have Dpay (n : Nat) (hn : n≤d+1) : (∑ x∈W,D x*x^n)=0 := simple_pole_clears W Δ τ d noMass ord simple n hn
  have eq (x : K) : D x/(x-τ)=Δ x/(x-τ)^2 := by simp [D,div_div,pow_two]
  have pole : (∑ x∈W,D x/(x-τ))=0 := by simpa only [eq] using double
  intro k hk
  have h := simple_pole_clears W D τ (d+1) D0 Dpay pole k (by omega)
  simpa only [eq] using h

end
end RKResearch.Certified.Graded.OneClockEndpointDebit

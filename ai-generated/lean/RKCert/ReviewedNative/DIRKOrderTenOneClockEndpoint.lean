module

public import RKCert.ReviewedNative.DIRKOrderTenSaturation
public import RKCert.ReviewedNative.DIRKOneClockEndpointDebit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Terminal mass on the actual eleven-stage equality tableau

The grade-five clean endpoint hypothesis is the specific band input from
one-physical-dirty-clock analysis. The actual coordinate and normalized
weight are derived below from `HasOrder 10` and the literal DIRK ranks. -/
namespace RKResearch.Certified.Graded.CrossedOrderTen.OneClockEndpoint

open RKResearch Module Reverse
open scoped Matrix BigOperators

variable {K : Type*} [Field K] {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}

/-- The two authentic reverse dimensions at grade three exhaust the
annihilator of grade five. -/
theorem terminal_coordinate_mem (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    coordinate (K:=K) (Fin.last 10) ∈ treeSpace A 5 := by
  let S := saturated ha ho
  let t := Fin.last 10
  have ht : LastActive b t := ⟨S.last_live,fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim⟩
  have inc := primitiveBack_annih ho 5 3 (by decide)
  have lo := dirk_primitiveBack_rank_gain ha ho (r:=1) (n:=3) (by decide) (by decide) (by decide)
  have cap := finrank_annih (treeSpace A 5)
  rw [Fintype.card_fin,S.e5] at cap
  have full : primitiveBack A b 3=annih (treeSpace A 5) := by
    apply Submodule.eq_of_le_of_finrank_le inc
    omega
  rw [←annih_annih (treeSpace A 5),←full]
  apply mem_annih.mpr
  intro v hv
  have z := mem_tailZero.mp (ht.dirk_primitiveBack_tail ha S.d1 S.d2 3 hv) t le_rfl
  rw [row_apply,dotProduct_comm,←row_apply,row_coordinate,z]

variable [CharZero K]

/-- Positive-degree coefficients of thirty times the normalized terminal
Jacobi polynomial: 30X−420X²+1680X³−2520X⁴+1260X⁵. -/
private def coeffs (K : Type*) [Field K] : Fin 5 → K
  | 0 => 30
  | 1 => -420
  | 2 => 1680
  | 3 => -2520
  | _ => 1260

private theorem coeffs_moments (i : Fin 5) :
    (∑ j : Fin 5, coeffs K j / ((i.val+j.val+2:ℕ):K)) = 1 := by
  fin_cases i <;> rw [Fin.sum_univ_five] <;> norm_num [coeffs]

omit [CharZero K] in
private theorem coeffs_sum : (∑ j : Fin 5, coeffs K j) = 30 := by
  rw [Fin.sum_univ_five]
  simp only [coeffs]
  ring

/-- A literal order-ten eleven-stage tableau whose terminal is clean
through grade five has the exact physical terminal mass `1/30`. -/
theorem terminal_weight_eq (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (clean : ∀ f∈zeroSpace A 5, f (Fin.last 10)=0) : b (Fin.last 10)=(1:K)/30 := by
  classical
  let S := saturated ha ho
  let t := Fin.last 10
  have nt : (0 : Fin 11) ≠ t := by decide
  have e0 : coordinate (K:=K) t 0 = 0 := by simp [coordinate,nt]
  have ht := terminal_coordinate_mem ha ho
  rw [treeSpace_coeff_sup ho (by decide : 5+1≤10)] at ht
  obtain ⟨v,hv,f,hf,e⟩ := Submodule.mem_sup.mp ht
  obtain ⟨a,rfl⟩ := hv
  have a0 : a 0=0 := by
    have h := congrFun e 0
    have f0 : f 0 = 0 := zeroSpace_at_zero_row S.physical_origin 5 hf
    rwa [Pi.add_apply,coeffEval_at_zero_row S.physical_origin,f0,add_zero,e0] at h
  have test (i : Fin 5) :
      (∑ j : Fin 5, a j.succ/((i.val+j.val+2:ℕ):K))=b t := by
    have h := congrArg (probe A b i.val) e
    have f0 : probe A b i.val f = 0 := probe_zeroSpace ho (by have := i.isLt; omega) hf
    have ct : probe A b i.val (coordinate t)=b t := by
      change row _ (coordinate t)=b t
      rw [row_coordinate,S.last_node,one_pow,mul_one]
    rw [map_add,f0,add_zero,probe_coeffEval ho (by have := i.isLt; omega),
      Fin.sum_univ_succ,a0,zero_div,zero_add,ct] at h
    simpa only [Fin.val_succ,Nat.add_assoc] using h
  let d : Fin 5 → K := fun j => a j.succ - b t * coeffs K j
  have vanish (i : Fin 5) : (∑ j : Fin 5,d j / ((i.val+j.val+2:ℕ):K))=0 := by
    simp only [d,sub_div,mul_div_assoc,Finset.sum_sub_distrib,←Finset.mul_sum,
      test i,coeffs_moments i,mul_one,sub_self]
  have zero := moments_detect ho (n:=5) (d:=2) (by decide) (by decide)
    (fun i j=>by have := i.isLt; have := j.isLt; omega) d vanish
  have eq (j : Fin 5) : a j.succ = b t * coeffs K j := sub_eq_zero.mp (zero j)
  have top : (∑ j : Fin 5,a j.succ)=1 := by
    have h := congrFun e t
    rw [Pi.add_apply,clean f hf,add_zero] at h
    change coeffEval A 5 a t = coordinate (K:=K) t t at h
    rw [coeffEval_apply,Finset.sum_apply] at h
    have one : nodes A t = 1 := S.last_node
    simp only [Pi.smul_apply,smul_eq_mul,normTree_clockTree,
      one,one_pow,mul_one,coordinate,Pi.single_eq_same] at h
    rw [Fin.sum_univ_succ,a0,zero_add] at h
    exact h
  rw [show (∑ j : Fin 5,a j.succ)=(∑ j : Fin 5,b t*coeffs K j) from Finset.sum_congr rfl (fun j _=>eq j),
    ←Finset.mul_sum,coeffs_sum] at top
  exact (eq_div_iff (by norm_num : (30:K)≠0)).mpr top

open OneClockEndpointDebit

omit [CharZero K] in
/-- Removing signed-zero aggregate on a clock does not silently remove
nonzero mass from some other physical occurrence of the same clock. -/
theorem fiberMass_remove_dark (D : Finset (Fin 11)) (c b : Fin 11 → K)
    (dark : ∀ x, fiberMass D c b x=0) (x : K) :
    fiberMass (Finset.univ \ D) c b x=fiberMass Finset.univ c b x := by
  classical
  let U : Finset (Fin 11) := Finset.univ \ D
  have union : U∪D=Finset.univ := by ext i; simp [U]
  have disj : Disjoint U D := by
    apply Finset.disjoint_left.mpr
    exact fun _ h d => (Finset.mem_sdiff.mp h).2 d
  have add : fiberMass U c b x+fiberMass D c b x=fiberMass (U∪D) c b x := by
    unfold fiberMass
    rw [Finset.filter_union,Finset.sum_union]
    exact disj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rwa [dark x,add_zero,union] at add

omit [CharZero K] in
/-- Cancellation at a single numerical clock removes the dirty pair, not
any clean occurrence or other physical endpoint at that same clock. -/
theorem dirty_pair_has_zero_fibers (c b : Fin 11 → K) (i j : Fin 11)
    (apart : i≠j) (clock : c i=c j) (cancel : b i+b j=0) :
    ∀ x, fiberMass ({i,j} : Finset (Fin 11)) c b x=0 := by
  classical
  intro x
  unfold fiberMass
  by_cases hit : c j=x
  · have hi := clock.trans hit
    rw [show ({i,j} : Finset (Fin 11)).filter (fun k => c k=x) = {i,j} from by simp [hi,hit],
      Finset.sum_pair apart,cancel]
  · have hi : c i≠x := fun e => hit (clock.symm.trans e)
    have empty : ({i,j} : Finset (Fin 11)).filter (fun k => c k=x)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k mem
      obtain ⟨km,ct⟩ := Finset.mem_filter.mp mem
      rcases Finset.mem_insert.mp km with rfl | hj
      · exact hi ct
      · have e := Finset.mem_singleton.mp hj
        subst k
        exact hit ct
    rw [empty,Finset.sum_empty]

/-- Actual terminal debit, over any characteristic-zero field. `D`
contains only rows whose signed ordinary contributions vanish as a
collection. The only independent tableau hypothesis besides reviewed
order and lower triangularity is terminal cleanliness at grade five.
`scale` may represent no pole, a simple pole, or a double pole. -/
theorem dark_rows_ordinary_measure_eq (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (clean : ∀ f∈zeroSpace A 5, f (Fin.last 10)=0)
    (D : Finset (Fin 11)) (L W : Finset K) (ν scale : K → K)
    (zero : (0:K)∈L) (one : (1:K)∈L) (oD : 0∉D) (tD : Fin.last 10∉D)
    (refLast : ν 1=(1:K)/30) (ref : ∀ x∉L,ν x=0)
    (dark : ∀ x,fiberMass D (nodes A) b x=0)
    (cover : ∀ x∉W,fiberMass Finset.univ (nodes A) b x=ν x)
    (neScale : ∀ x∈W,fiberMass Finset.univ (nodes A) b x≠ν x → scale x≠0)
    {k : Nat} (budget : 11+L.card ≤ (k+1)+D.card+3)
    (tests : ∀ n≤k, (∑ x∈W,(scale x*(fiberMass Finset.univ (nodes A) b x-ν x))*x^n)=0) :
    ∀ x, fiberMass Finset.univ (nodes A) b x=ν x := by
  classical
  let S := saturated ha ho
  have start : nodes A (0:Fin 11)=0 := by simp [nodes,Matrix.mulVec,dotProduct,S.physical_origin]
  have last : b (Fin.last 10)=ν 1 := (terminal_weight_eq ha ho clean).trans refLast.symm
  have rem := fiberMass_remove_dark D (nodes A) b dark
  have matched := endpoint_debit_closes_power_tests D L W (nodes A) b ν scale
    (o:=0) (t:=Fin.last 10) (by decide) start S.last_node zero one oD tD last ref
    (fun x hx => (rem x).trans (cover x hx))
    (fun x hx m => neScale x hx (fun eq => m ((rem x).trans eq)))
    (by simpa using budget) (fun n hn => by simpa only [rem] using tests n hn)
  intro x
  exact (rem x).symm.trans (matched x)

/-- In the paid two-dirty-stage skeleton, two reciprocal moments (or the
ordinary reads after no-pole clearing) close the whole residual. They do
not need nonzero weights at the origin or each reference node. -/
theorem cancelled_pair_measure_eq_of_scaled11 (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (clean : ∀ f∈zeroSpace A 5, f (Fin.last 10)=0)
    (i j : Fin 11) (apart : i≠j) (coclock : nodes A i=nodes A j) (cancel : b i+b j=0)
    (L W : Finset K) (ν scale : K → K)
    (zero : (0:K)∈L) (one : (1:K)∈L) (oD : 0∉({i,j} : Finset (Fin 11)))
    (tD : Fin.last 10∉({i,j} : Finset (Fin 11)))
    (refLast : ν 1=(1:K)/30) (ref : ∀ x∉L,ν x=0) (refBudget : L.card≤6)
    (cover : ∀ x∉W,fiberMass Finset.univ (nodes A) b x=ν x)
    (neScale : ∀ x∈W,fiberMass Finset.univ (nodes A) b x≠ν x → scale x≠0)
    (tests : ∀ n≤11, (∑ x∈W,(scale x*(fiberMass Finset.univ (nodes A) b x-ν x))*x^n)=0) :
    ∀ x, fiberMass Finset.univ (nodes A) b x=ν x := by
  have card : ({i,j} : Finset (Fin 11)).card=2 := Finset.card_pair apart
  exact dark_rows_ordinary_measure_eq ha ho clean {i,j} L W ν scale zero one oD tD refLast ref
    (dirty_pair_has_zero_fibers (nodes A) b i j apart coclock cancel) cover neScale (by omega) tests

/-- One reciprocal read at a matched pole suffices if at least three
physical dark rows have already been spent. -/
theorem three_dark_rows_measure_eq_of_simple_pole (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (clean : ∀ f∈zeroSpace A 5, f (Fin.last 10)=0)
    (D : Finset (Fin 11)) (L W : Finset K) (ν : K → K) (τ : K)
    (zero : (0:K)∈L) (one : (1:K)∈L) (oD : 0∉D) (tD : Fin.last 10∉D)
    (refLast : ν 1=(1:K)/30) (ref : ∀ x∉L,ν x=0) (refBudget : L.card≤6) (dcount : 3≤D.card)
    (dark : ∀ x,fiberMass D (nodes A) b x=0)
    (cover : ∀ x∉W,fiberMass Finset.univ (nodes A) b x=ν x)
    (matchedPole : fiberMass Finset.univ (nodes A) b τ=ν τ)
    (ordinary : ∀ n≤9, (∑ x∈W,(fiberMass Finset.univ (nodes A) b x-ν x)*x^n)=0)
    (pole : (∑ x∈W,(fiberMass Finset.univ (nodes A) b x-ν x)/(x-τ))=0) :
    ∀ x, fiberMass Finset.univ (nodes A) b x=ν x := by
  let Δ := fun x => fiberMass Finset.univ (nodes A) b x-ν x
  have d0 : Δ τ=0 := sub_eq_zero.mpr matchedPole
  refine dark_rows_ordinary_measure_eq ha ho clean D L W ν (fun x => (x-τ)⁻¹) zero one oD tD
    refLast ref dark cover (k:=10) ?_ (by omega) ?_
  · intro x _ m
    exact inv_ne_zero (sub_ne_zero.mpr (fun h=>m (h.symm ▸ matchedPole)))
  · intro n hn
    calc
      _ = ∑ x∈W,(Δ x/(x-τ))*x^n := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [Δ,div_eq_mul_inv]
        ring
      _ = 0 := simple_pole_clears W Δ τ 9 d0 ordinary pole n hn

/-- Two reciprocal reads at a matched pole suffice after spending the
physical cancelling pair. This is the pole specialization of the
actual order-ten pair closure. -/
theorem cancelled_pair_measure_eq_of_double_pole (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (clean : ∀ f∈zeroSpace A 5, f (Fin.last 10)=0)
    (i j : Fin 11) (apart : i≠j) (coclock : nodes A i=nodes A j) (cancel : b i+b j=0)
    (L W : Finset K) (ν : K → K) (τ : K)
    (zero : (0:K)∈L) (one : (1:K)∈L) (oD : 0∉({i,j} : Finset (Fin 11)))
    (tD : Fin.last 10∉({i,j} : Finset (Fin 11)))
    (refLast : ν 1=(1:K)/30) (ref : ∀ x∉L,ν x=0) (refBudget : L.card≤6)
    (cover : ∀ x∉W,fiberMass Finset.univ (nodes A) b x=ν x)
    (matchedPole : fiberMass Finset.univ (nodes A) b τ=ν τ)
    (ordinary : ∀ n≤9, (∑ x∈W,(fiberMass Finset.univ (nodes A) b x-ν x)*x^n)=0)
    (simple : (∑ x∈W,(fiberMass Finset.univ (nodes A) b x-ν x)/(x-τ))=0)
    (double : (∑ x∈W,(fiberMass Finset.univ (nodes A) b x-ν x)/(x-τ)^2)=0) :
    ∀ x, fiberMass Finset.univ (nodes A) b x=ν x := by
  let Δ := fun x => fiberMass Finset.univ (nodes A) b x-ν x
  have d0 : Δ τ=0 := sub_eq_zero.mpr matchedPole
  apply cancelled_pair_measure_eq_of_scaled11 ha ho clean i j apart coclock cancel L W ν
    (fun x => ((x-τ)^2)⁻¹) zero one oD tD refLast ref refBudget cover
  · intro x _ m
    exact inv_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (fun h=>m (h.symm ▸ matchedPole))))
  · intro n hn
    calc
      _ = ∑ x∈W,(Δ x/(x-τ)^2)*x^n := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [Δ,div_eq_mul_inv]
        ring
      _ = 0 := double_pole_clears W Δ τ 9 d0 ordinary simple double n hn

end RKResearch.Certified.Graded.CrossedOrderTen.OneClockEndpoint

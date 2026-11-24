module

public import RKCert.ReviewedNative.DIRKCubicCleanTrace
public import RKCert.ReviewedNative.ClockSignatureFold
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Algebraic pivots in a native cubic head
The reduced donor count uses actual first occurrences of clock/head
signatures. A row sum may fold repeated columns, but no time coordinate,
matrix row, or proof of order is removed. -/
namespace RKResearch.Certified.Graded.HeadFiber

open Polynomial RKCert.OneEscape RKCert.Endpoint Signature
open scoped Matrix Classical

variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K}
variable {b w : Fin s → K}

/-- The five earliest represented dirty rows, with strictly increasing
physical positions and no repeated numerical clock among them. -/
theorem first_five_dirty
    (P : K[X]) (fit : ∀ i, w i≠0 → w i=P.eval (nodes A i))
    (many : 4<(physicalSites (nodes A) w).card) :
    ∃ d : Fin 5 → Fin s, StrictMono d ∧
      Function.Injective (fun k => nodes A (d k)) ∧
      (∀ k, first (nodes A) w (d k)=d k ∧ w (d k)≠0) ∧
      ∀ (i : Fin s), first (nodes A) w i=i → w i≠0 → ∀ k, i≤d k →
        ∃ l : Fin 5, d l=i ∧ l≤k := by
  classical
  let c := nodes A
  let S := (Finset.univ : Finset (Fin s)).filter (fun i => first c w i=i ∧ w i≠0)
  have se : physicalSites c w ⊆ S.image c := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have nz : w i≠0 := (Finset.mem_filter.mp hi).2
    have hw : w (first c w i)=w i := congrArg Prod.snd (first_signature c w i)
    refine Finset.mem_image.mpr ⟨first c w i,?_,congrArg Prod.fst (first_signature c w i)⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,first_idempotent c w i,hw.symm ▸ nz⟩
  have size : 5≤S.card := (Nat.succ_le_of_lt many).trans
    ((Finset.card_le_card se).trans Finset.card_image_le)
  let e := S.orderEmbOfFin rfl
  let d : Fin 5 → Fin s := fun i => e (Fin.castLE size i)
  have mono := e.strictMono.comp (Fin.strictMono_castLE size)
  have hd (k : Fin 5) : first c w (d k)=d k ∧ w (d k)≠0 :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl (Fin.castLE size k))).2
  refine ⟨d,mono,?_,hd,?_⟩
  · intro i j eq
    change c (d i)=c (d j) at eq
    have h : w (d i)=w (d j) := by
      rw [fit _ (hd i).2,fit _ (hd j).2]
      exact congrArg (fun z => P.eval z) eq
    apply mono.injective
    change d i=d j
    exact (hd i).1.symm.trans ((first_congr (Prod.ext eq h)).trans (hd j).1)
  · intro i rep dirty k le
    have m : i∈Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rep,dirty⟩
    obtain ⟨j,rfl⟩ := m
    have bound : j.val≤k.val := e.le_iff_le.mp le
    exact ⟨⟨j.val,bound.trans_lt k.isLt⟩,rfl,bound⟩

variable [CharZero K]

omit [CharZero K] in
/-- Check a paid Volterra output against the minimal number of distinct
dirty clock evaluations that detects its next head polynomial. -/
theorem paid_volterra_zero (ho : HasOrder A b p) {k : ℕ} (pay : 5+k≤p)
    (band : ∀ l≤3, zeroSpace A (3+l)=chain (diag (nodes A)) ⊥ w (1+l))
    (k1 : k≤1) {f q : K[X]} (df : f.natDegree≤3+k) (dq : q.natDegree≤k)
    (D : Fin (3+k) → Fin s) (dist : Function.Injective (fun j=>nodes A (D j)))
    (dirty : ∀ j, w (D j)≠0)
    (tests : ∀ j, volterra A (headInput A w f q) (D j)=0) :
    volterra A (headInput A w f q)=0 := by
  have inV := headInput_mem_treeSpace (band k (by omega)) df dq
  have inR := volterra_treeSpace ho (3+k) (by omega) inV
  have inPure : volterra A (headInput A w f q) ∈zeroSpace A (3+(k+2)) := by
    change volterra A (headInput A w f q)∈zeroSpace A (3+k+2) at inR
    simpa only [Nat.add_assoc] using inR
  obtain ⟨Q,d,eq⟩ := pure_head_repr (band (k+2) (by omega)) inPure
  have vals (j : Fin (3+k)) : Q.eval (nodes A (D j))=0 := by
    have t := tests j
    rw [eq,weightedEval_apply] at t
    exact (mul_eq_zero.mp t).resolve_right (dirty j)
  have Q0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q dist vals (by
    rw [Fintype.card_fin]; omega)
  rw [eq,Q0,map_zero]

/-- A prefix-zero test with nonzero value at the next dirty row. Packing
the origin-cleared scalar and the head into one interpolation allows one
extra clean clock at grade four, without adding any hypothesized row. -/
theorem dirty_pivot_test (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    (band : ∀ l≤3, zeroSpace A (3+l)=chain (diag (nodes A)) ⊥ w (1+l))
    (P : K[X]) (Pd : P.natDegree≤3) (P0 : P.eval 0≠0)
    (fit : ∀ i, w i≠0 → w i=P.eval (nodes A i))
    {k : ℕ} (k1 : k≤1) (pay : 5+k≤p)
    {i : Fin s} (iDirty : w i≠0)
    (D : Fin (3+k) → Fin s) (pre : ∀ j, D j < i)
    (dist : Function.Injective (fun j=>nodes A (D j))) (dirty : ∀ j, w (D j)≠0)
    (fresh : ∀ j, nodes A (D j)≠nodes A i)
    (dcover : ∀ j < i, w j≠0 → ∃ l, nodes A (D l)=nodes A j)
    (ccover : (∀ j < i, w j=0 → nodes A j=0) ∨
      (k=1 ∧ ∃ u : K, u≠0 ∧ P.eval u≠0 ∧
        ∀ j < i, w j=0 → nodes A j≠0 → nodes A j=u)) :
    ∃ f q : K[X], f.natDegree≤3+k ∧ f.eval 0=0 ∧ q.natDegree≤k ∧
      headInput A w f q i≠0 ∧ (∀ j < i, headInput A w f q j=0) ∧
      volterra A (headInput A w f q)=0 ∧ A i i=0 := by
  classical
  let S := Finset.univ.image (fun j => nodes A (D j))
  let H := nodalHull S
  let t := H.eval 0/P.eval 0
  let f := H-C t*P
  have hd : H.natDegree=3+k := by
    rw [natDegree_nodalHull,Finset.card_image_of_injective _ dist,Finset.card_univ,Fintype.card_fin]
  have df : f.natDegree≤3+k := (natDegree_sub_le _ _).trans
    (max_le hd.le ((natDegree_C_mul_le _ _).trans (by omega)))
  have fz : f.eval 0=0 := by simp [f,t,div_mul_cancel₀ _ P0]
  have freshH : H.eval (nodes A i)≠0 := by
    change (nodalHull S).eval (nodes A i)≠0
    rw [nodalHull,eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro a mem
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp mem
    simpa using sub_ne_zero.mpr (fresh l).symm
  obtain ⟨a,a0,matchA⟩ : ∃ (a : K), (k=0 → a=0) ∧
      ∀ j < i, w j=0 → nodes A j≠0 →
        f.eval (nodes A j)+a*(nodes A j*P.eval (nodes A j))=0 := by
    rcases ccover with none|⟨hk,u,un,up,cover⟩
    · exact ⟨0,fun _=>rfl,fun j hj wj zj => (zj (none j hj wj)).elim⟩
    · refine ⟨-(f.eval u)/(u*P.eval u),fun h => (by omega),?_⟩
      intro j hj wj cj
      rw [cover j hj wj cj,div_mul_cancel₀ _ (mul_ne_zero un up),add_neg_cancel]
  let F := f+C a*(X*P)
  let Q := C t-C a*X
  have dF : F.natDegree≤3+k := by
    by_cases e : k=0
    · simpa [F,a0 e] using df
    apply (natDegree_add_le _ _).trans
    refine max_le df ((natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_))
    rw [natDegree_X]; omega
  have dQ : Q.natDegree≤k := by
    by_cases e : k=0
    · simp [Q,a0 e,e]
    exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X]; omega)))
  have F0 : F.eval 0=0 := by simp [F,fz]
  have valDirty (j : Fin s) (wj : w j≠0) :
      headInput A w F Q j=H.eval (nodes A j) := by
    rw [headInput_apply,fit j wj]
    simp only [F,Q,f,eval_add,eval_sub,eval_mul,eval_C,eval_X]
    ring
  have vn : headInput A w F Q i≠0 := (valDirty i iDirty).symm ▸ freshH
  have vz (j : Fin s) (hj : j < i) : headInput A w F Q j=0 := by
    by_cases jn : w j≠0
    · obtain ⟨l,e⟩ := dcover j hj jn
      rw [valDirty j jn,←e]
      exact nodalHull_eval_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l))
    · have jw := not_ne_iff.mp jn
      rw [headInput_apply,jw,mul_zero,add_zero]
      by_cases zero : nodes A j=0
      · rw [zero,F0]
      · simpa [F] using matchA j hj jw zero
  have rz := paid_volterra_zero ho pay band k1 dF dQ D dist dirty (fun j => by
    rw [volterra_pivot ha _ _ (fun l hl => vz l (hl.trans (pre j))),vz _ (pre j),mul_zero])
  have z := congrFun rz i
  rw [volterra_pivot ha i _ vz,Pi.zero_apply] at z
  exact ⟨F,Q,dF,F0,dQ,vn,vz,rz,
    sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp z).resolve_right vn))⟩

end RKResearch.Certified.Graded.HeadFiber

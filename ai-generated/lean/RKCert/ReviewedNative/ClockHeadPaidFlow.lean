module

public import RKCert.ReviewedNative.ClockHeadSupport

@[expose] public section

/-! # Exact native primitive flow of a pure single clock head

The profile is just the actual native polynomial evaluation plus a genuine
head column. No masked tableau is claimed to attain order. -/
namespace RKResearch.Certified.Graded.HeadFiber

open Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Matrix Classical

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {w : Fin s → K}

/-- A scalar polynomial and a head correction evaluated on the *same*
physical stage rows. -/
noncomputable abbrev headInput (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K)
    (f q : K[X]) : Fin s → K :=
  evalNodes A f + weightedEval (nodes A) w q

@[simp] theorem headInput_apply (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K)
    (f q : K[X]) (i : Fin s) :
    headInput A w f q i = f.eval (nodes A i) + q.eval (nodes A i)*w i := by
  simp [headInput]

/-- A bounded polynomial in the clock applied to a head stays in the
same paid native chain. -/
theorem weighted_head_mem {k : ℕ}
    (bk : zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    (q : K[X]) (dq : q.natDegree≤k) :
    weightedEval (nodes A) w q ∈ zeroSpace A (3+k) := by
  have pays (l : ℕ) (hl : l≤k) : (diag (nodes A)^l) w ∈ zeroSpace A (3+k) :=
    ((clock_chain_le_iff _).mp bk.ge).2 l (by omega)
  have mono (l : ℕ) (hl : l≤k) (a : K) :
      weightedEval (nodes A) w (monomial l a) ∈ zeroSpace A (3+k) := by
    convert (zeroSpace A (3+k)).smul_mem a (pays l hl) using 1
    ext i
    simp [mul_assoc]
  rw [q.as_sum_range' (k+1) (Nat.lt_succ_of_le dq),map_sum]
  exact (zeroSpace A (3+k)).sum_mem (fun l hl => mono l (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) _)

private theorem natDegree_le_of_degree_lt {f : K[X]} {k : ℕ} (b : f.degree < ((k+1:ℕ): WithBot ℕ)) :
    f.natDegree≤k := by
  by_cases zero : f=0
  · simp [zero]
  exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt zero).mpr b)

theorem pure_head_repr {k : ℕ}
    (bk : zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    {v : Fin s → K} (mem : v∈zeroSpace A (3+k)) :
    ∃ q : K[X], q.natDegree≤k ∧ v=weightedEval (nodes A) w q := by
  rw [bk] at mem
  obtain ⟨u,hu,q,d,eq⟩ := exists_poly mem
  have uz : u=0 := by simpa only [Submodule.mem_bot] using hu
  rw [uz,zero_add] at eq
  exact ⟨q,natDegree_le_of_degree_lt (by simpa [Nat.add_comm] using d),eq⟩

theorem headInput_mem_treeSpace {k : ℕ}
    (bk : zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    {f q : K[X]} (df : f.natDegree≤3+k) (dq : q.natDegree≤k) :
    headInput A w f q ∈ treeSpace A (3+k) :=
  (treeSpace A _).add_mem (evalNodes_mem_treeSpace A f df)
    (zeroSpace_le_treeSpace A _ (weighted_head_mem bk q dq))

/-- The actual A action on a scalar polynomial with a head correction.
The primitive is the reviewed primitive and the residual belongs to the
genuine next defect space before any polynomial representation is chosen. -/
theorem headInput_mat [CharZero K] {k : ℕ}
    (bk : zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    (bn : zeroSpace A (3+(k+1))=chain (diag (nodes A)) ⊥ w (1+(k+1)))
    {f q : K[X]} (df : f.natDegree≤3+k) (dq : q.natDegree≤k) :
    ∃ r : K[X], r.natDegree≤k+1 ∧ mat A (headInput A w f q) = headInput A w (primitive f) r := by
  have hp := primitive_defect A f df
  have hq' := mat_zeroSpace_charZero A _ (weighted_head_mem bk q dq)
  have add := (zeroSpace A (3+(k+1))).add_mem hp hq'
  have act : mat A (headInput A w f q)-evalNodes A (primitive f)∈zeroSpace A (3+(k+1)) := by
    convert add using 1
    rw [show headInput A w f q=evalNodes A f + weightedEval (nodes A) w q from rfl,map_add]
    abel
  obtain ⟨r,dr,eq⟩ := pure_head_repr bn act
  refine ⟨r,dr,?_⟩
  change mat A (headInput A w f q)=evalNodes A (primitive f)+weightedEval (nodes A) w r
  rw [←eq]; abel

/-- The same moment-exact polynomial can assign arbitrary values at three
distinct physical donor clocks. -/
theorem fit_three_donors (D : Fin 3 → Fin s)
    (dist : Function.Injective (fun i => nodes A (D i))) (dirty : ∀ i, w (D i)≠0)
    (f : K[X]) :
    ∃ q : K[X], q.natDegree≤2 ∧ ∀ i, headInput A w f q (D i)=0 := by
  let a : Fin 3 → K := fun i => nodes A (D i)
  let g : Fin 3 → K := fun i => -f.eval (a i)/w (D i)
  let q := Lagrange.interpolate Finset.univ a g
  have dq : q.natDegree≤2 := by
    by_cases z : q=0
    · simp [z]
    have d := Lagrange.degree_interpolate_lt (s:=Finset.univ) (v:=a) g dist.injOn
    rw [Finset.card_univ,Fintype.card_fin] at d
    exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr d)
  refine ⟨q,dq,fun i => ?_⟩
  have h : q.eval (nodes A (D i))=g i :=
    Lagrange.eval_interpolate_at_node g dist.injOn (Finset.mem_univ i)
  rw [headInput_apply,h]
  dsimp [g,a]
  rw [div_mul_cancel₀ _ (dirty i),add_neg_cancel]

/-- Three independently movable donor values cannot support five dirty
receivers whose next pure grade contains only one cubic head band.
The proof spends actual grade 5→6. In particular, a dirty clock may be
zero; an origin double root is not charged as two sampled rows. -/
theorem five_dirty_three_donor_impossible [CharZero K]
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    (r : Fin 5 → Fin s)
    (distinct : Function.Injective (fun i => nodes A (r i)))
    (dirty : ∀ i, w (r i)≠0)
    (D : Fin 3 → Fin s)
    (distD : Function.Injective (fun i => nodes A (D i)))
    (dirtyD : ∀ i, w (D i)≠0)
    (flow : ∀ f q : K[X], f.natDegree≤5 → f.eval 0=0 → q.natDegree≤2 →
      (∀ i : Fin 3, headInput A w f q (D i)=0) →
      ∀ i : Fin 5, mat A (headInput A w f q) (r i)=0) :
    False := by
  classical
  let z : Fin 5 → K := fun i => nodes A (r i)
  have nonzero : ∃ i, z i≠0 := by
    by_contra! h
    exact (show (0:Fin 5)≠1 by decide) (distinct ((h 0).trans (h 1).symm))
  obtain ⟨i,zi⟩ := nonzero
  let S := (Finset.univ.image z).erase (z i)
  have memI : z i ∈ Finset.univ.image z := Finset.mem_image_of_mem z (Finset.mem_univ i)
  have four : S.card=4 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem memI,Finset.card_image_of_injective _ distinct,Finset.card_univ,Fintype.card_fin]
  let H := X^2 * nodalHull S
  let f := H.derivative
  have Hdeg : H.natDegree≤6 := by
    have h := natDegree_mul_le (p:=(X^2:K[X])) (q:=nodalHull S)
    rw [natDegree_nodalHull,four,natDegree_pow,natDegree_X] at h
    exact h.trans (by decide)
  have fdeg : f.natDegree≤5 := (natDegree_derivative_le H).trans (by omega)
  have f0 : f.eval 0=0 := by simp [f,H,derivative_mul,derivative_pow]
  have H0 : H.coeff 0=0 := by rw [coeff_zero_eq_eval_zero]; simp [H]
  have Jh : primitive f = H := primitive_derivative H H0
  obtain ⟨q,qdeg,atD⟩ := fit_three_donors (A:=A) D distD dirtyD f
  obtain ⟨T,dT,action⟩ := headInput_mat (band 2 (by decide)) (band 3 (by decide)) fdeg qdeg
  have rel (j : Fin 5) : H.eval (z j)+T.eval (z j)*w (r j)=0 := by
    have p := flow f q fdeg f0 qdeg atD j
    rw [action,headInput_apply,Jh] at p
    exact p
  have roots (a : K) (ha : a∈S) : T.eval a=0 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase ha)
    have Hz : H.eval (z j)=0 := by simp [H,nodalHull_eval_of_mem ha]
    have p := rel j
    rw [Hz,zero_add] at p
    exact (mul_eq_zero.mp p).resolve_right (dirty j)
  have T0 := eq_zero_of_degree_lt_of_eval_finset_eq_zero S
    (T.degree_le_natDegree.trans_lt (by exact_mod_cast (show T.natDegree<S.card by omega))) roots
  have Hz : H.eval (z i)=0 := by simpa [T0] using rel i
  have nonroot : (nodalHull S).eval (z i) ≠0 := by
    rw [nodalHull,eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    simpa only [eval_sub,eval_X,eval_C] using
      sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm
  exact (mul_ne_zero (pow_ne_zero 2 zi) nonroot) (by simpa only [H,eval_mul,eval_pow,eval_X] using Hz)

end RKResearch.Certified.Graded.HeadFiber

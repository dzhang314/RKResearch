module

public import RKCert.ReviewedNative.ERKOrder16WeakRankThreeForward
public import RKCert.ReviewedNative.NativeSymplecticPairing
public import RKCert.ReviewedNative.FiveNodalDiagonal
public import RKCert.ReviewedNative.PositiveIntervalGrid19
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiveNodalDiagonal
open scoped Classical BigOperators Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b θ : Fin 24→K}
variable {q Q P : K[X]}

private theorem reflected_evalNodes (R : K[X]) (i : Fin 24) :
    evalNodes A (R.comp (1-X)) i=R.eval (reflectedClock A i) := by
  simp only [evalNodes_apply,eval_comp,eval_sub,eval_one,eval_X]
  rfl

private theorem reflected_degree (R : K[X]) {n : ℕ} (d : R.natDegree≤n) :
    (R.comp (1-X)).natDegree≤n := by
  have h : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (by simpa only [mul_one] using Nat.mul_le_mul d h)

/-- Exact global unweighted mass on the genuine grade-four source;
the reflected multiplier costs eleven, not a new moment table. -/
theorem Width24RankThreeWeakMask.unweighted_mass
    (W : Width24RankThreeWeakMask A b q Q P θ)
    (src : ∃ z∈zeroSpace A 4, θ=evalNodes A q-z)
    (ho : HasOrder 16 A b) (qd : Q.natDegree≤4)
    (R : K[X]) (rd : R.natDegree≤11) :
    integral 0 1 (Q*R)=∑ i, b i*θ i*R.eval (reflectedClock A i) := by
  obtain ⟨z,z4,repr⟩ := src
  let R' := evalNodes A (R.comp (1-X))
  have zv : z*R'∈zeroSpace A 15 :=
    zeroSpace_mul_treeSpace ho (by decide : 11+1≤16) z4
      (evalNodes_mem_treeSpace A _ (reflected_degree R rd))
  have zw : row b (z*R')=0 := by
    have e := probe_zeroSpace ho (k:=0) (by decide : 0+15+1≤16) zv
    change probe A b 0 (z*R')=0 at e
    simpa only [probe,pow_zero,mul_one] using e
  have vec : θ*R'=(fun i=>Q.eval (reflectedClock A i)*R.eval (reflectedClock A i))-z*R' := by
    ext i
    rw [repr]
    simp only [R',Pi.mul_apply,Pi.sub_apply,evalNodes_apply,eval_comp,eval_sub,
      eval_one,eval_X,W.reflected,reflectedClock,Pi.one_apply]
    ring
  have mass := reflected_polynomial_mass ho (Q*R)
    (by have h := natDegree_mul_le (p:=Q) (q:=R);omega)
  have eq₁ : row b (θ*R')=∑ i, b i*θ i*R.eval (reflectedClock A i) := by
    rw [row_apply,dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply,R',reflected_evalNodes,mul_assoc]
  rw [←eq₁,vec,map_sub,zw,sub_zero,integral_zero_left,formalPrimitive_eq_native,←mass]
  rw [row_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply,eval_mul]
  ring

/-- Full seed-band support, not only a projection of E8. -/
theorem Width24QuadraticCover.coordinate_in_treeSpace8
    (W : Width24QuadraticCover A b) {i : Fin 24}
    (off : quadraticSeed A b i=0) : coordinate (K:=K) i∈treeSpace A 8 := by
  rw [←annih_annih (treeSpace A 8)]
  apply mem_annih.mpr
  intro u hu
  rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
  rw [W.band] at hu
  obtain ⟨R,_,rfl⟩ := mem_weightedBand.mp hu
  simp [off]

private theorem supported_singleton_sum
    (f : Fin 5→Fin 24) (inj : Function.Injective f) {u : Fin 24→K}
    (off : ∀ i, (∀ j, f j≠i) → u i=0) :
    (∑ j, u (f j) • coordinate (K:=K) (f j))=u := by
  classical
  ext i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases h : ∃ j, f j=i
  · obtain ⟨j,rfl⟩ := h
    calc
      _ = u (f j)*coordinate (K:=K) (f j) (f j) := by
        apply Finset.sum_eq_single j
        · intro k _ kj
          have e : f j≠f k := fun eq=>kj (inj eq.symm)
          simp [coordinate,e]
        · simp
      _ = _ := by simp [coordinate]
  · have all : ∀ j, f j≠i := fun j hj=>h ⟨j,hj⟩
    rw [off i all]
    apply Finset.sum_eq_zero
    intro j _
    simp [coordinate,(all j).symm]

/-- True five-label kernel on a supported grade-four mask. -/
theorem Width24RankThreeWeakMask.diagonal_on_actual_five
    (W : Width24RankThreeWeakMask A b q Q P θ)
    (src : ∃ z∈zeroSpace A 4, θ=evalNodes A q-z)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (f : Fin 5→Fin 24) (fi : Function.Injective f)
    (yi : Function.Injective (fun i : Fin 5 => reflectedClock A (f i)))
    (supported : ∀ i, (∀ j, f j≠i) → θ i=0)
    (seedOff : ∀ i : Fin 5, quadraticSeed A b (f i)=0) :
    ∃ H : K[X], H.natDegree≤2 ∧ ∀ i : Fin 5,
      H.eval (reflectedClock A (f i)) =
        (b (f i)*θ (f i)*slope (fun j=>reflectedClock A (f j)) i)^2 := by
  classical
  let y (i : Fin 5) := reflectedClock A (f i)
  let a (i : Fin 5) := b (f i)*θ (f i)
  let e (i : Fin 5) := coordinate (K:=K) (f i)
  let T (i j : Fin 5) := θ (f i)*θ (f j)*symplecticPair A b (e i) (e j)
  have e8 (i : Fin 5) : e i∈treeSpace A 8 :=
    (width24_quadratic_cover ha ho).coordinate_in_treeSpace8 (seedOff i)
  have th4 : θ∈treeSpace A 4 := by
    obtain ⟨z,hz,hq⟩ := src
    rw [hq]
    exact (treeSpace A 4).sub_mem (evalNodes_mem_treeSpace A q W.degree)
      (zeroSpace_le_treeSpace A 4 hz)
  apply exists_diagonal_quadratic yi T ?_ a ?_ ?_
  · intro i j
    dsimp only [T]
    rw [symplecticPair_comm A b (e i) (e j),mul_comm (θ (f i)) (θ (f j))]
  · intro i
    have ee : symplecticPair A b (e i) (e i)=-(b (f i)*b (f i)) := by
      dsimp only [e,coordinate]
      rw [@symplecticPair_coordinate (Fin 24) K _ _ (Classical.decEq _) A b (f i) (f i),
        ha _ _ le_rfl,mul_zero,zero_add,zero_sub]
    dsimp only [T,a]
    rw [ee]
    ring
  · intro i k kd
    let u : Fin 24→K := θ*evalNodes A ((X^k:K[X]).comp (1-X))
    have r2 : ((X^k:K[X]).comp (1-X)).natDegree≤2 :=
      reflected_degree _ (by rwa [natDegree_X_pow])
    have u6 : u∈treeSpace A 6 :=
      treeSpace_mul th4 (evalNodes_mem_treeSpace A _ r2)
    have up (j : Fin 24) : u j=θ j*(reflectedClock A j)^k := by
      simp only [u,Pi.mul_apply,reflected_evalNodes,eval_pow,eval_X]
    have rep := supported_singleton_sum f fi (u:=u) (fun j hj => by rw [up,supported j hj,zero_mul])
    have v := symplecticPair_zero_on_paid_tree_spaces ho (by decide : 8+6+2≤16) (e8 i) u6
    rw [←rep,map_sum] at v
    simp only [map_smul,smul_eq_mul,up] at v
    have scaled := congrArg (fun x : K => θ (f i)*x) v
    rw [Finset.mul_sum,mul_zero] at scaled
    rw [←scaled]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [T,y,e]
    ring

end
end RKResearch.Certified.ERK16

module
public import RKCert.ReviewedNative.ERKOrder16WeakFourPhysicalSymplectic
public import RKCert.ReviewedNative.NodalOddDiagonal
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.NodalOddDiagonal
open scoped Classical BigOperators Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b θ : Fin 24→K} {q Q : K[X]}

/-- Physical support for a reflected polynomial minus a genuine F4 defect. -/
structure WeakFourGradedMask (A : Matrix (Fin 24) (Fin 24) K) (b θ : Fin 24→K)
    (q Q : K[X]) (S : Finset (Fin 24)) : Prop where
  qDegree : q.natDegree≤4
  reflects : ∀ x,q.eval x=Q.eval (1-x)
  source : ∃ z∈zeroSpace A 4, θ=evalNodes A q-z
  outside : ∀ i,i∉S→θ i=0
  seedOff : ∀ i∈S,quadraticSeed A b i=0

theorem weak_four_reflected_eval (R : K[X]) (i : Fin 24) :
    evalNodes A (R.comp (1-X)) i=R.eval (reflectedClock A i) := by
  simp only [evalNodes_apply,eval_comp,eval_sub,eval_one,eval_X]
  rfl

theorem weak_four_reflected_degree (R : K[X]) {n : ℕ} (d : R.natDegree≤n) :
    (R.comp (1-X)).natDegree≤n := by
  have h : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (by simpa only [mul_one] using Nat.mul_le_mul d h)

theorem WeakFourGradedMask.row_mass {S : Finset (Fin 24)}
    (W : WeakFourGradedMask A b θ q Q S)
    (ho : HasOrder 16 A b) (qd : Q.natDegree≤4) (R : K[X]) (rd : R.natDegree≤11) :
    integral 0 1 (Q*R)=row b (θ*evalNodes A (R.comp (1-X))) := by
  obtain ⟨z,z4,repr⟩ := W.source
  let R' := evalNodes A (R.comp (1-X))
  have zv : z*R'∈zeroSpace A 15 :=
    zeroSpace_mul_treeSpace ho (by decide : 11+1≤16) z4
      (evalNodes_mem_treeSpace A _ (weak_four_reflected_degree R rd))
  have e := probe_zeroSpace ho (k:=0) (by decide : 0+15+1≤16) zv
  change probe A b 0 (z*R')=0 at e
  have zw : row b (z*R')=0 := by simpa only [probe,pow_zero,mul_one] using e
  have vec : θ*R'=(fun i=>Q.eval (reflectedClock A i)*R.eval (reflectedClock A i))-z*R' := by
    ext i
    rw [repr]
    simp only [R',Pi.mul_apply,Pi.sub_apply,evalNodes_apply,eval_comp,eval_sub,eval_one,eval_X,
      W.reflects,reflectedClock,Pi.one_apply]
    ring
  have mass := reflected_polynomial_mass ho (Q*R)
    (by have h := natDegree_mul_le (p:=Q) (q:=R);omega)
  change integral 0 1 (Q*R)=row b (θ*R')
  rw [vec,map_sub,zw,sub_zero,integral_zero_left,formalPrimitive_eq_native,←mass,row_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply,eval_mul]
  ring

def weakFourGroupColumn (A : Matrix (Fin 24) (Fin 24) K) (θ : Fin 24→K)
    (S : Finset (Fin 24)) (x : K) : Fin 24→K :=
  ∑ i∈S.filter (fun i=>reflectedClock A i=x), θ i • coordinate (K:=K) i

theorem weakFourGroupColumn_apply (S : Finset (Fin 24)) (x : K) (i : Fin 24) :
    weakFourGroupColumn A θ S x i=if i∈S ∧ reflectedClock A i=x then θ i else 0 := by
  classical
  let R := S.filter (fun j=>reflectedClock A j=x)
  change (∑ j∈R, θ j • coordinate (K:=K) j) i=_
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases h : i∈R
  · rw [if_pos (Finset.mem_filter.mp h)]
    rw [Finset.sum_eq_single_of_mem i h]
    · simp [coordinate]
    · intro j _ ji
      simp [coordinate,ji,ji.symm]
  · rw [if_neg (fun e=>h (Finset.mem_filter.mpr e))]
    apply Finset.sum_eq_zero
    intro j hj
    have ji : j≠i := fun e=>h (e ▸ hj)
    simp [coordinate,ji,ji.symm]

theorem weakFourGroupColumn_singleton {S : Finset (Fin 24)} {x : K} {i : Fin 24}
    (h : S.filter (fun j=>reflectedClock A j=x)={i}) :
    weakFourGroupColumn A θ S x=θ i • coordinate (K:=K) i := by
  rw [weakFourGroupColumn,h,Finset.sum_singleton]

private theorem reconstruct_weak_four_groups {n : ℕ} {S : Finset (Fin 24)}
    (off : ∀ i,i∉S→θ i=0) (y : Fin n→K) (simple : Function.Injective y)
    (covers : ∀ i∈S,∃ j,y j=reflectedClock A i) (R : K[X]) :
    (∑ j,R.eval (y j) • weakFourGroupColumn A θ S (y j))=
      θ*evalNodes A (R.comp (1-X)) := by
  classical
  ext i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,weak_four_reflected_eval,
    weakFourGroupColumn_apply]
  by_cases hi : i∈S
  · obtain ⟨j,hj⟩ := covers i hi
    rw [Finset.sum_eq_single j]
    · simp [hi,hj] <;> ring
    · intro k _ kj
      have ne : reflectedClock A i≠y k := fun e=>kj (simple ((hj.trans e).symm))
      simp [hi,show 1 - nodes A i ≠ y k from ne]
    · simp
  · simp [hi,off i hi]

/-- The paid diagonal and mass on the chosen numerical labels. At
a singleton fibre the native strict diagonal is earned, not assumed. -/
theorem WeakFourGradedMask.grouped_diagonal {d : ℕ} (dp : 1≤d)
    {S : Finset (Fin 24)} (W : WeakFourGradedMask A b θ q Q S)
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 16 A b) (qd : Q.natDegree≤4)
    (y : Fin (d+4)→K) (inj : Function.Injective y)
    (covers : ∀ i∈S,∃ j,y j=reflectedClock A i) :
    ∃ H : K[X], H.natDegree≤2*d-1 ∧
      (∀ R : K[X],R.natDegree≤11 →
        integral 0 1 (Q*R)=∑ j,row b (weakFourGroupColumn A θ S (y j))*R.eval (y j)) ∧
      ∀ j i, S.filter (fun k=>reflectedClock A k=y j)={i} →
        H.eval (y j)=(b i*θ i*slope y j)^2 ∧ row b (weakFourGroupColumn A θ S (y j))=b i*θ i := by
  classical
  let g (j : Fin (d+4)) := weakFourGroupColumn A θ S (y j)
  let T (i j : Fin (d+4)) := symplecticPair A b (g i) (g j)
  have t8 (j : Fin (d+4)) : g j∈treeSpace A 8 := by
    dsimp only [g,weakFourGroupColumn]
    apply (treeSpace A 8).sum_mem
    intro i hi
    exact (treeSpace A 8).smul_mem _
      ((width24_quadratic_cover ha ho).coordinate_in_treeSpace8
        (W.seedOff i (Finset.mem_filter.mp hi).1))
  have th4 : θ∈treeSpace A 4 := by
    obtain ⟨z,hz,hq⟩ := W.source
    rw [hq]
    exact (treeSpace A 4).sub_mem (evalNodes_mem_treeSpace A _ W.qDegree)
      (zeroSpace_le_treeSpace A 4 hz)
  have expand (k : ℕ) :
      (∑ j,(y j)^k • g j)=θ*evalNodes A ((X^k:K[X]).comp (1-X)) := by
    simpa only [eval_pow,eval_X,g] using
      reconstruct_weak_four_groups W.outside y inj covers (X^k:K[X])
  have ux (k m : ℕ) (pay : k≤m) :
      θ*evalNodes A ((X^k:K[X]).comp (1-X))∈treeSpace A (4+m) := by
    have pd : ((X^k:K[X]).comp (1-X)).natDegree≤m :=
      weak_four_reflected_degree _ (by rwa [natDegree_X_pow])
    exact treeSpace_mul th4 (evalNodes_mem_treeSpace A _ pd)
  have sm (i j : Fin (d+4)) : T i j=T j i := symplecticPair_comm A b (g i) (g j)
  have ker (i : Fin (d+4)) (k : ℕ) (pay : k≤2) : ∑ j,T i j*(y j)^k=0 := by
    have p := symplecticPair_zero_on_paid_tree_spaces ho (by decide : 8+6+2≤16) (t8 i) (ux k 2 pay)
    rw [←expand k,map_sum] at p
    simp only [map_smul,smul_eq_mul] at p
    simpa only [T,mul_comm] using p
  have iso : (∑ i,(y i)^3*(∑ j,T i j*(y j)^3))=0 := by
    have p := symplecticPair_zero_on_paid_tree_spaces ho (by decide : 7+7+2≤16)
      (ux 3 3 le_rfl) (ux 3 3 le_rfl)
    rw [←expand 3] at p
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul] at p
    convert p using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [sm i j]
    dsimp only [T]
    ring
  obtain ⟨H,Hd,HH⟩ := exists_odd_diagonal dp inj T sm ker iso
  refine ⟨H,Hd,?_,?_⟩
  · intro R rd
    have e := W.row_mass ho qd R rd
    rw [←reconstruct_weak_four_groups W.outside y inj covers R,map_sum] at e
    simp only [map_smul,smul_eq_mul] at e
    simpa only [mul_comm] using e
  · intro j i hs
    have M : g j=θ i • coordinate (K:=K) i := weakFourGroupColumn_singleton hs
    have pair : symplecticPair A b (coordinate (K:=K) i) (coordinate (K:=K) i)=
        -(b i*b i) := by
      dsimp only [coordinate]
      rw [@symplecticPair_coordinate (Fin 24) K _ _ (Classical.decEq _) A b i i,
        ha _ _ le_rfl,mul_zero,zero_add,zero_sub]
    refine ⟨?_,?_⟩
    · rw [HH]
      dsimp only [T]
      rw [M]
      simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,pair]
      ring
    · change row b (g j)=_
      rw [M,map_smul,smul_eq_mul,row_coordinate,mul_comm]

end
end RKResearch.Certified.ERK16

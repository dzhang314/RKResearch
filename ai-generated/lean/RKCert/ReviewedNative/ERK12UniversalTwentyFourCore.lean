module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDataAll
public import RKResearch.ERK
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact sparse entries and the unit-defect transfer for the
twenty-four-stage ERK order-twelve tableau. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour

open RKResearch RootedTreeGram FiniteRootedTree
open scoped Matrix FiniteRootedTree
set_option maxRecDepth 40000
set_option maxHeartbeats 0
set_option Elab.async false

def idx (n j : ℕ) (hn : 0<n) : Fin n := ⟨j%n,Nat.mod_lt _ hn⟩
def tag (j : ℕ) : Fin 25 := idx 25 j (by decide)
def lSupp (i : Fin 25) : List (Fin 25) := lSupport[i.val]!.map tag
def aSupp (i : Fin 24) : List (Fin 24) := aSupport[i.val]!.map fun j => idx 24 j (by decide)
def bSupp : List (Fin 24) := bSupport.map fun j => idx 24 j (by decide)

def sparseDot {n : ℕ} : List (Fin n) → (Fin n → ℤ) → (Fin n → ℤ) → ℤ
  | [], _, _ => 0
  | j::js, a, v => a j*v j+sparseDot js a v

theorem sparseDot_eq {n : ℕ} (ls : List (Fin n)) (a v : Fin n → ℤ)
    (hn : ls.Nodup) (hz : ∀ j ∉ ls, a j=0) : sparseDot ls a v = a ⬝ᵥ v := by
  let f := fun j => a j*v j
  have hb : ∀ L : List (Fin n), L.Nodup →
      sparseDot L a v = ∑ j ∈ L.toFinset, f j := by
    intro L hl
    induction L with
    | nil => simp [sparseDot]
    | cons j L ih =>
      obtain ⟨h1,h2⟩ := List.nodup_cons.mp hl
      have hj : j ∉ L.toFinset := by simpa using h1
      simp only [sparseDot,List.toFinset_cons,Finset.sum_insert hj,ih h2,f]
  rw [hb ls hn,dotProduct]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
    simp [f,hz j (by simpa using hj)]

def suppOK {n : ℕ} (ls : List (Fin n)) (v : Fin n → ℤ) : Bool :=
  decide ls.Nodup &&
    (List.finRange n).all fun j => decide (j ∉ ls → v j=0)

theorem sparse_from_check {n : ℕ} (ls : List (Fin n)) (a v : Fin n → ℤ)
    (h : suppOK ls a=true) : sparseDot ls a v = a ⬝ᵥ v := by
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
  exact sparseDot_eq _ _ _ (of_decide_eq_true h1) fun j hj =>
    of_decide_eq_true (List.all_eq_true.mp h2 j (List.mem_finRange j)) hj

private theorem lSupp_ok (i : Fin 25) : suppOK (lSupp i) (branch M D 1 i) = true :=
  List.all_eq_true.mp
    (show (List.finRange 25).all
      (fun j => suppOK (lSupp j) (branch M D 1 j)) = true by decide +kernel)
    i (List.mem_finRange i)
private theorem aSupp_ok (i : Fin 24) : suppOK (aSupp i) (M i) = true :=
  List.all_eq_true.mp
    (show (List.finRange 24).all (fun j => suppOK (aSupp j) (M j)) = true by decide +kernel)
    i (List.mem_finRange i)
private theorem bSupp_ok : suppOK bSupp w = true := by decide +kernel

def leftEntry (X : Cov 24) (i j : Fin 25) : ℤ :=
  sparseDot (lSupp i) (branch M D 1 i) (fun k => X k j)

def rightEntry (X : Cov 24) (i j : Fin 25) : ℤ :=
  sparseDot (lSupp j) (branch M D 1 j) (X i)

theorem leftEntry_matrix (X : Cov 24) :
    (fun i j => leftEntry X i j) = branch M D 1 * X := by
  ext i j
  simpa only [leftEntry,Matrix.mul_apply,dotProduct] using
    sparse_from_check (lSupp i) (branch M D 1 i) (fun k => X k j) (lSupp_ok i)

theorem rightEntry_matrix (X : Cov 24) :
    (fun i j => rightEntry X i j) = X * (branch M D 1)ᵀ := by
  ext i j
  simp only [rightEntry,sparse_from_check _ _ _ (lSupp_ok j),dotProduct,
    Matrix.mul_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

def matrixBlock (X Y : Cov 24) (b : ℕ) : Bool :=
  (List.range' (b*5) 5).all fun i =>
    (List.finRange 25).all fun j => decide (X (tag i) j = Y (tag i) j)

theorem extOfBlocks {X Y : Cov 24} (h : ∀ k : Fin 5, matrixBlock X Y k.val=true) :
    X = Y := by
  ext i j
  let q : ℕ := i.val/5
  have hq : q<5 := by have := i.isLt; dsimp [q]; omega
  have hmem : i.val ∈ List.range' (q*5) 5 := by
    rw [List.mem_range']
    exact ⟨i.val%5, by omega, by dsimp [q]; omega⟩
  have hi := List.all_eq_true.mp (h ⟨q,hq⟩) _ hmem
  have a := of_decide_eq_true (List.all_eq_true.mp hi j (List.mem_finRange j))
  have ht : tag i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rwa [ht] at a

def factoredStep (n : ℕ) : Cov 24 :=
  ((List.finRange (n+1)).map fun i => coeff n i.val •
    entryMul (cov i.val) (reweight (n-i.val+1) (right (n-i.val)))).sum

theorem sparseA (i : Fin 24) (v : Fin 24→ℤ) :
    sparseDot (aSupp i) (M i) v = (M *ᵥ v) i :=
  sparse_from_check (aSupp i) (M i) v (aSupp_ok i)

theorem sparseB (v : Fin 24→ℤ) : sparseDot bSupp w v = w ⬝ᵥ v :=
  sparse_from_check bSupp w v bSupp_ok

theorem clocks : M *ᵥ (1 : Fin 24→ℤ) = c := by
  funext i
  have h : (List.finRange 24).all
      (fun i => decide (sparseDot (aSupp i) (M i) 1=c i)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))
  rwa [sparseA] at hh

theorem action_c5 : M *ᵥ (c^5) = ac5 := by
  funext i
  have h : (List.finRange 24).all
      (fun i => decide (sparseDot (aSupp i) (M i) (c^5)=ac5 i)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))
  rwa [sparseA] at hh

def nextTree1 : FiniteRootedTree := bushyTree 13
def nextTree2 : FiniteRootedTree := (bushyTree 7) ◂ (bushyTree 6)

theorem nextNum1 :
    (1373847552:ℤ)*((nextTree1.factorial:ℤ)*(w ⬝ᵥ Φ nextTree1 M))=
      (1161187+1373847552)*D^13 := by
  simp only [nextTree1,factorial_bushyTree,Φ_bushyTree,clocks]
  change (1373847552:ℤ)*(13*(w ⬝ᵥ (c^12)))=_
  rw [←sparseB]
  decide +kernel

theorem nextNum2 :
    (351704973312:ℤ)*((nextTree2.factorial:ℤ)*(w ⬝ᵥ Φ nextTree2 M))=
      (24764718696320825821075+351704973312)*D^13 := by
  rw [show (nextTree2.factorial:ℤ)=78 by decide +kernel]
  simp only [nextTree2,Φ,Φ_bushyTree,clocks]
  change (351704973312:ℤ)*(78*(w ⬝ᵥ (c^6*(M *ᵥ c^5)))) = _
  rw [action_c5,←sparseB]
  decide +kernel

variable {R : Type*} [CommRing R]
def A (d : R) : Matrix (Fin 24) (Fin 24) R := d • M.map (Int.castRingHom R)
def b (d : R) : Fin 24 → R := d • (Int.castRingHom R ∘ w)

theorem explicit (d : R) : ERK (A d) := by
  intro i j h
  change d*((M i j:ℤ):R)=0
  simp [M,Fin.not_lt.mpr h]

theorem order_from_trace (tr : FactoredTrace M D 12)
    (h : ∀ n < 12, energy (tr.cov n) (output w D (n+1))=0)
    (d : R) (hd : (D:R)*d=1) : HasOrder 12 (A d) (b d) := by
  let f := Int.castRingHom R
  have hfd : f D*d=1 := hd
  have hA : M.map f = f D • A d := by
    change M.map f = f D • (d • M.map f)
    rw [smul_smul,hfd,one_smul]
  have hb : f ∘ w = f D • b d := by
    change f ∘ w = f D • (d • (f ∘ w))
    rw [smul_smul,hfd,one_smul]
  have hu : IsUnit (f D) := IsUnit.of_mul_eq_one _ hd
  exact tr.hasOrder h f (A d) (b d) hA hb hu hu

theorem scaled_defect (d : R) (hd : (D:R)*d=1)
    (t : FiniteRootedTree) (ht : (t.order:ℕ)=13) (m z : ℤ)
    (H : m*((t.factorial:ℤ)*(w ⬝ᵥ Φ t M))=(z+m)*D^13) :
    (m:R)*((t.factorial:R)*(b d ⬝ᵥ Φ t (A d))-1)=(z:R) := by
  let f := Int.castRingHom R
  have hmap := congrArg f H
  change f (m*((t.factorial:ℤ)*(w ⬝ᵥ Φ t M)))=f ((z+m)*D^13) at hmap
  simp only [map_mul,map_pow,map_natCast,RingHom.map_dotProduct,RKResearch.map_Φ] at hmap
  have hs : ((t.order:ℕ)-1)=12 := by omega
  simp only [A,b,Φ_matrix_smul,hs,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  calc
    _ = ((m:R)*((t.factorial:R)*((f ∘ w) ⬝ᵥ Φ t (M.map f))))*d^13-(m:R) := by ring
    _ = (z:R) := by
      change (f m*((t.factorial:R)*((f ∘ w) ⬝ᵥ Φ t (M.map f))))*d^13-f m=f z
      rw [hmap,mul_assoc,←mul_pow]
      change f (z+m)*((D:R)*d)^13-f m=f z
      rw [hd,one_pow,mul_one,map_add,add_sub_cancel_right]

theorem not_order_thirteen [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 13 (A d) (b d) := by
  intro h
  have H1 := scaled_defect d hd nextTree1 (by decide) _ _ nextNum1
  have H2 := scaled_defect d hd nextTree2 (by decide) _ _ nextNum2
  rw [h nextTree1 (by decide),sub_self,mul_zero] at H1
  rw [h nextTree2 (by decide),sub_self,mul_zero] at H2
  have H := congrArg (Int.castRingHom R)
    (show (12225658687008318314473:ℤ)*1161187-573246*24764718696320825821075=1 by
      decide +kernel)
  simp only [map_mul,map_sub,map_one] at H
  change ((12225658687008318314473:ℤ):R) * ((1161187:ℤ):R) -
    ((573246:ℤ):R) * ((24764718696320825821075:ℤ):R) = 1 at H
  rw [←H1,←H2,mul_zero,mul_zero,sub_zero] at H
  exact zero_ne_one H

end RKResearch.Certified.ERK12UniversalTwentyFour

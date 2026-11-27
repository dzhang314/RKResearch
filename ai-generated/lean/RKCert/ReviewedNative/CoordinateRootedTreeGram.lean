module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Coordinate traces for the reviewed rooted trees

The tensor recurrence is entirely over integers. The finite-dimensional
coefficient algebra enters only through the soundness interface; no order
or positivity is required there. Positivity is applied to integer
coordinate squares, never to squares in the coefficient algebra. -/
namespace RKResearch.Certified.CoordinateRootedTreeGram

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

abbrev Cov (J : Type*) := Matrix J J ℤ

/-- Integer components of a bilinear multiplication operation. -/
structure Machine (J : Type*) where
  tensor : J → J → J → ℤ
  leaf : J → ℤ
  branch : ℕ → Cov J

variable {J κ : Type*} [Fintype J] [Fintype κ]

def featureMul (X : Machine J) (x y : J → ℤ) : J → ℤ :=
  fun a => ∑ i, ∑ j, X.tensor a i j * x i * y j

def tensorMul (X : Machine J) (V W : Cov J) : Cov J :=
  fun a b => ∑ k, ∑ l, ∑ i, ∑ j, X.tensor a i j * X.tensor b k l * V i k * W j l

def outer (x : J → ℤ) : Cov J := Matrix.vecMulVec x x

private theorem tensorMul_zero (X : Machine J) (V : Cov J) :
    tensorMul X V 0 = 0 := by
  ext a b; simp [tensorMul]

private theorem zero_tensorMul (X : Machine J) (V : Cov J) :
    tensorMul X 0 V = 0 := by
  ext a b; simp [tensorMul]

private theorem tensorMul_add (X : Machine J) (U V W : Cov J) :
    tensorMul X U (V+W) = tensorMul X U V + tensorMul X U W := by
  ext a b
  simp only [tensorMul, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem add_tensorMul (X : Machine J) (U V W : Cov J) :
    tensorMul X (U+V) W = tensorMul X U W + tensorMul X V W := by
  ext a b
  simp only [tensorMul, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem outer_mul (X : Machine J) (x y : J → ℤ) :
    outer (featureMul X x y) = tensorMul X (outer x) (outer y) := by
  ext a b
  simp only [outer, Matrix.vecMulVec_apply, featureMul, tensorMul,
    Finset.sum_mul, Finset.mul_sum]
  congr! 4
  ring

private theorem outer_branch (B : Cov J) (v : J → ℤ) :
    outer (B *ᵥ v) = B * outer v * Bᵀ := by
  simp only [outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

omit [Fintype J] in
private theorem outer_scale (c : ℤ) (v : J → ℤ) :
    outer (c • v) = c^2 • outer v := by
  ext i j
  simp only [outer, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

def attachScale (left right : ℕ) : ℕ := (left+right-1).choose right

/-- Forest-factorial features are multiplied by the binomial normalization
at each attachment, giving the order-factorial scaling of the controls. -/
def feature (X : Machine J) : FiniteRootedTree → J → ℤ
  | .leaf => X.leaf
  | .butcherProduct t u =>
      (attachScale t.order u.order : ℤ) •
        featureMul X (feature X t) (X.branch u.order *ᵥ feature X u)

/-- Positive scalar relating the binomial feature to the corresponding
known forest-factorial feature. -/
def treeScale : FiniteRootedTree → ℕ
  | .leaf => 1
  | .butcherProduct t u => attachScale t.order u.order * treeScale t * treeScale u

theorem treeScale_pos (t : FiniteRootedTree) : 0 < treeScale t := by
  induction t with
  | leaf => decide
  | butcherProduct t u ht hu =>
    have hpos := t.order.pos
    have hz : 0 < attachScale t.order u.order := Nat.choose_pos (by omega)
    exact Nat.mul_pos (Nat.mul_pos hz ht) hu

private theorem factorial_from_pred {k : ℕ} (hk : 0 < k) :
    k * (k-1).factorial = k.factorial := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Nat.factorial_succ]
  rfl

/-- The binomial factors change the archived forest-factorial normalization
into the ordinary factorial of the size minus one, not the tree factorial. -/
theorem treeScale_forest (t : FiniteRootedTree) :
    treeScale t * (t.forestFactorial : ℕ) = ((t.order : ℕ)-1).factorial := by
  induction t with
  | leaf => decide
  | butcherProduct t u ht hu =>
    let j : ℕ := t.order
    let k : ℕ := u.order
    have hj : 0 < j := t.order.pos
    have hk : 0 < k := u.order.pos
    have hdegree : ((t ◂ u).order : ℕ)-1 = j+k-1 := by
      simp only [order,PNat.add_coe,j,k]
    have hsub : (j+k-1)-k = j-1 := by omega
    have hc := Nat.choose_mul_factorial_mul_factorial (show k ≤ j+k-1 by omega)
    rw [hsub] at hc
    calc
      _ = (j+k-1).choose k * (treeScale t * (t.forestFactorial : ℕ)) *
          (k * (treeScale u * (u.forestFactorial : ℕ))) := by
        simp only [treeScale,attachScale,forestFactorial,PNat.mul_coe,j,k]
        ac_rfl
      _ = (j+k-1).choose k * (j-1).factorial * k.factorial := by
        rw [ht,hu,factorial_from_pred hk]
      _ = (j+k-1).choose k * k.factorial * (j-1).factorial := by ac_rfl
      _ = _ := hdegree ▸ hc

/-- Applied to a tree-factorial cleared residual, the additional integer
factor is exactly the quotient of the ordinary size factorial. -/
theorem treeScale_factorial (t : FiniteRootedTree) :
    treeScale t * (t.factorial : ℕ) = (t.order : ℕ).factorial := by
  rw [factorial,PNat.mul_coe,← mul_left_comm,treeScale_forest,
    factorial_from_pred t.order.pos]

def covList (X : Machine J) (ts : List FiniteRootedTree) : Cov J :=
  (ts.map (outer ∘ feature X)).sum

@[simp] theorem cov_nil (X : Machine J) : covList X [] = 0 := rfl
@[simp] theorem cov_cons (X : Machine J) (t : FiniteRootedTree) (ts : List FiniteRootedTree) :
    covList X (t :: ts) = outer (feature X t) + covList X ts := rfl
@[simp] theorem cov_append (X : Machine J) (ts us : List FiniteRootedTree) :
    covList X (ts ++ us) = covList X ts + covList X us := by
  simp [covList, List.sum_append]

theorem cov_map_attach (X : Machine J) (t : FiniteRootedTree) (us : List FiniteRootedTree)
    (k : ℕ) (hu : ∀ u ∈ us, (u.order : ℕ) = k) :
    covList X (us.map (butcherProduct t)) =
      ((attachScale t.order k : ℤ)^2) • tensorMul X (outer (feature X t))
        (X.branch k * covList X us * (X.branch k)ᵀ) := by
  induction us with
  | nil => simp [tensorMul_zero]
  | cons u us ih =>
    simp only [List.map_cons,cov_cons,Matrix.mul_add,Matrix.add_mul,tensorMul_add,
      feature,outer_scale,outer_mul,outer_branch,hu u List.mem_cons_self,smul_add]
    rw [ih (fun v hv => hu v (List.mem_cons_of_mem _ hv))]

theorem cov_flatMap_attach (X : Machine J) (ts us : List FiniteRootedTree)
    (j k : ℕ) (ht : ∀ t ∈ ts, (t.order : ℕ) = j) (hu : ∀ u ∈ us, (u.order : ℕ) = k) :
    covList X (ts.flatMap (fun t => us.map (butcherProduct t))) =
      ((attachScale j k : ℤ)^2) • tensorMul X (covList X ts)
        (X.branch k * covList X us * (X.branch k)ᵀ) := by
  induction ts with
  | nil => simp [zero_tensorMul]
  | cons t ts ih =>
    simp only [List.flatMap_cons,cov_append,cov_map_attach X t us k hu,
      ih (fun v hv => ht v (List.mem_cons_of_mem _ hv)),
      cov_cons,ht t List.mem_cons_self,add_tensorMul,smul_add]

def covTrees (X : Machine J) (n : ℕ) : Cov J := covList X (treesOfOrderSucc n)

def step (X : Machine J) (C : ℕ → Cov J) (n : ℕ) : Cov J :=
  ((List.finRange (n+1)).map fun i =>
    let k := n-i.val+1
    let B := X.branch k
    ((attachScale (i.val+1) k : ℤ)^2) •
      tensorMul X (C i.val) (B * C (n-i.val) * Bᵀ)).sum


/-- The finite support of one row of the integral multiplication table. -/
def support (X : Machine J) (a : J) : Finset (J × J) :=
  Finset.univ.filter fun x => X.tensor a x.1 x.2 ≠ 0

/-- Evaluate only the nonzero structure constants. -/
def tensorMulSparse (X : Machine J) (V W : Cov J) : Cov J :=
  fun a b => ∑ k ∈ support X b, ∑ i ∈ support X a,
    X.tensor a i.1 i.2 * X.tensor b k.1 k.2 * V i.1 k.1 * W i.2 k.2

theorem tensorMul_eq_sparse (X : Machine J) (V W : Cov J) :
    tensorMul X V W = tensorMulSparse X V W := by
  ext a b
  let f := fun (k i : J × J) =>
    X.tensor a i.1 i.2 * X.tensor b k.1 k.2 * V i.1 k.1 * W i.2 k.2
  have ha (k : J × J) :
      (∑ i ∈ support X a, f k i) = ∑ i, f k i := by
    unfold support
    apply Finset.sum_filter_of_ne
    intro i _ h hz
    exact h (by simp [f,hz])
  have hb :
      (∑ k ∈ support X b, ∑ i, f k i) = ∑ k, ∑ i, f k i := by
    unfold support
    apply Finset.sum_filter_of_ne
    intro k _ h hz
    exact h (by simp [f,hz])
  change _ = ∑ k ∈ support X b, ∑ i ∈ support X a, f k i
  simp_rw [ha]
  rw [hb]
  simp only [tensorMul, Fintype.sum_prod_type,f]

/-- Sparse evaluation of the same exact grade step. -/
def stepSparse (X : Machine J) (C : ℕ → Cov J) (n : ℕ) : Cov J :=
  ((List.finRange (n+1)).map fun i =>
    let k := n-i.val+1
    let B := X.branch k
    ((attachScale (i.val+1) k : ℤ)^2) •
      tensorMulSparse X (C i.val) (B * C (n-i.val) * Bᵀ)).sum

theorem step_eq_sparse (X : Machine J) (C : ℕ → Cov J) (n : ℕ) :
    step X C n = stepSparse X C n := by
  simp only [step,stepSparse,tensorMul_eq_sparse]

theorem covTrees_zero (X : Machine J) : covTrees X 0 = outer X.leaf := by
  simp [covTrees,treesOfOrderSucc,feature]

theorem covTrees_succ (X : Machine J) (n : ℕ) :
    covTrees X (n+1) = step X (covTrees X) n := by
  unfold covTrees
  rw [treesOfOrderSucc]
  unfold step
  generalize List.finRange (n+1) = is
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons,cov_append,List.map_cons,List.sum_cons,ih]
    rw [cov_flatMap_attach X _ _ (i.val+1) (n-i.val+1)]
    · intro u hu; exact (mem_treesOfOrderSucc _ _).mp hu
    · intro u hu; exact (mem_treesOfOrderSucc _ _).mp hu

structure Trace (X : Machine J) (p : ℕ) where
  cov : ℕ → Cov J
  base : cov 0 = outer X.leaf
  next : ∀ n, n+1 < p → cov (n+1) = step X cov n

theorem Trace.correct {X : Machine J} {p : ℕ} (C : Trace X p) (n : ℕ) (hn : n < p) :
    C.cov n = covTrees X n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [C.base,covTrees_zero]
    | succ n =>
      rw [C.next n hn,covTrees_succ]
      unfold step
      congr 1
      apply List.map_congr_left
      intro i _
      have h := i.isLt
      rw [ih i.val (by omega) (by omega),ih (n-i.val) (by omega) (by omega)]

/-- Ordinary coordinate trace after applying the output on both axes. -/
def energy (C : Cov J) (O : Matrix κ J ℤ) : ℤ :=
  ∑ r, (O r) ⬝ᵥ (C *ᵥ O r)

theorem energy_outer (v : J → ℤ) (O : Matrix κ J ℤ) :
    energy (outer v) O = ∑ r, (O *ᵥ v) r ^ 2 := by
  simp only [energy,outer,Matrix.vecMulVec_mulVec,dotProduct_smul,
    MulOpposite.smul_eq_mul_unop,MulOpposite.unop_op,Matrix.mulVec,pow_two,dotProduct_comm v]

private theorem energy_add (U V : Cov J) (O : Matrix κ J ℤ) :
    energy (U+V) O = energy U O + energy V O := by
  simp only [energy,Matrix.add_mulVec,dotProduct_add,Finset.sum_add_distrib]

theorem energy_covList (X : Machine J) (ts : List FiniteRootedTree) (O : Matrix κ J ℤ) :
    energy (covList X ts) O = (ts.map fun t => ∑ r, (O *ᵥ feature X t) r ^ 2).sum := by
  induction ts with
  | nil => simp [energy]
  | cons t ts ih => rw [cov_cons,energy_add,energy_outer,ih,List.map_cons,List.sum_cons]

private theorem sum_coords_zero {α : Type*} (u : α → κ → ℤ) (ts : List α) :
    (ts.map fun t => ∑ r, (u t r)^2).sum = 0 ↔ ∀ t ∈ ts, u t = 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have hn : 0 ≤ ∑ r, (u t r)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have htail : 0 ≤ (ts.map fun t => ∑ r, (u t r)^2).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    constructor
    · intro hz
      simp only [List.map_cons,List.sum_cons] at hz
      have hzero : (∑ r, (u t r)^2) = 0 := by omega
      have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg (u t r))).mp hzero
      have ht : u t = 0 := funext (fun r =>
        (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp (hp r (Finset.mem_univ _)))
      have hz' : (ts.map fun t => ∑ r, (u t r)^2).sum = 0 := by omega
      intro x hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ht
      · exact ih.mp hz' _ hv
    · intro h
      have hz := ih.mpr (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have ht := h t List.mem_cons_self
      simp [ht,hz]

theorem Trace.energy_iff {X : Machine J} {p : ℕ} (C : Trace X p)
    (O : ℕ → Matrix κ J ℤ) (n : ℕ) (hn : n < p) :
    energy (C.cov n) (O (n+1)) = 0 ↔
      ∀ t : FiniteRootedTree, (t.order : ℕ) = n+1 → O (n+1) *ᵥ feature X t = 0 := by
  rw [C.correct n hn,covTrees,energy_covList,sum_coords_zero]
  simp only [mem_treesOfOrderSucc]


section Semantics

variable {K : Type*} [CommRing K] [Algebra ℚ K] {s : ℕ}
abbrev StagePair (s : ℕ) (K : Type*) := (Fin s → K) × K

/-- Integer-coordinate model of an integral multiplication basis.
The extra coordinate is the homogeneous scalar (embedded in K);
the output is decoded by the independent coefficient coordinates. -/
structure Model (X : Machine J) (M : Matrix (Fin s) (Fin s) K)
    (w : Fin s → K) (d e : ℤ) where
  read : (J → ℤ) →+ StagePair s K
  value : (κ → ℤ) →+ K
  value_injective : Function.Injective value
  output : ℕ → Matrix κ J ℤ
  map_leaf : read X.leaf = (1,1)
  map_mul : ∀ v z, read (featureMul X v z) = read v * read z
  map_branch : ∀ k v, read (X.branch k *ᵥ v) =
    ((k : K) • (M *ᵥ (read v).1), (d : K) * (read v).2)
  map_output : ∀ n v, value (output n *ᵥ v) =
    (n : K) * (w ⬝ᵥ (read v).1) - (e : K) * (read v).2

omit [Fintype κ] [Algebra ℚ K] in
theorem Model.read_feature {X : Machine J} {M : Matrix (Fin s) (Fin s) K}
    {w : Fin s → K} {d e : ℤ} (P : Model (κ := κ) X M w d e) (t : FiniteRootedTree) :
    P.read (feature X t) =
      (((treeScale t : K) * (t.forestFactorial : K)) • Φ t M,
       (treeScale t : K) * (d : K)^((t.order : ℕ)-1)) := by
  induction t with
  | leaf =>
    rw [feature,P.map_leaf]
    simp [treeScale,forestFactorial,Φ,order]
  | butcherProduct t u ht hu =>
    rw [feature,map_zsmul,P.map_mul,P.map_branch,ht,hu]
    apply Prod.ext
    · rw [Prod.smul_fst]
      funext i
      simp only [Prod.fst_mul,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,
        Matrix.mulVec_smul,treeScale,Nat.cast_mul,forestFactorial,PNat.mul_coe,Φ,
        zsmul_eq_mul,Int.cast_natCast]
      ring
    · have h₁ := t.order.pos
      have h₂ := u.order.pos
      have hdegree : ((t ◂ u).order : ℕ)-1 =
          ((t.order : ℕ)-1) + (1 + ((u.order : ℕ)-1)) := by
        simp only [order,PNat.add_coe]
        omega
      rw [Prod.smul_snd]
      simp only [Prod.snd_mul,zsmul_eq_mul,treeScale,Nat.cast_mul,
        Int.cast_natCast,hdegree,pow_add,pow_one]
      ring

omit [Fintype κ] [Algebra ℚ K] in
theorem Model.read_residual {X : Machine J} {M : Matrix (Fin s) (Fin s) K}
    {w : Fin s → K} {d e : ℤ} (P : Model (κ := κ) X M w d e)
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (hA : M = (d : K) • A) (hb : w = (e : K) • b) (t : FiniteRootedTree) :
    P.value (P.output t.order *ᵥ feature X t) =
      ((treeScale t : K) * ((e : K) * (d : K)^((t.order : ℕ)-1))) *
        ((t.factorial : K) * (b ⬝ᵥ Φ t A) - 1) := by
  rw [P.map_output,P.read_feature,hA,hb,Φ_matrix_smul]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,factorial,PNat.mul_coe,Nat.cast_mul]
  ring

omit [Fintype κ] in
theorem Model.output_zero_iff {X : Machine J} {M : Matrix (Fin s) (Fin s) K}
    {w : Fin s → K} {d e : ℤ} (P : Model (κ := κ) X M w d e)
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (hA : M = (d : K) • A) (hb : w = (e : K) • b)
    (hd : IsUnit (d : K)) (he : IsUnit (e : K)) (t : FiniteRootedTree) :
    P.output t.order *ᵥ feature X t = 0 ↔
      (t.factorial : K) * (b ⬝ᵥ Φ t A) = 1 := by
  have hq : IsUnit (treeScale t : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (treeScale_pos t)))
  have hs : IsUnit (treeScale t : K) := by
    simpa only [map_natCast] using hq.map (algebraMap ℚ K)
  have huv := hs.mul (he.mul (hd.pow ((t.order : ℕ)-1)))
  rw [← P.value_injective.eq_iff,map_zero,P.read_residual hA hb]
  exact
    ⟨fun h => sub_eq_zero.mp (huv.mul_left_cancel (by simpa only [mul_zero] using h)),
     fun h => by rw [h,sub_self,mul_zero]⟩

/-- Coordinate energy certifies the same reviewed order predicate,
and its nonzero value certifies failure. The proof is independent of
order or positivity on the coefficient algebra itself. -/
theorem Trace.hasOrder_iff {X : Machine J} {M : Matrix (Fin s) (Fin s) K}
    {w : Fin s → K} {d e : ℤ} {p : ℕ} (C : Trace X p) (P : Model (κ := κ) X M w d e)
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (hA : M = (d : K) • A) (hb : w = (e : K) • b)
    (hd : IsUnit (d : K)) (he : IsUnit (e : K)) :
    HasOrder p A b ↔ ∀ n < p, energy (C.cov n) (P.output (n+1)) = 0 := by
  constructor
  · intro ho n hn
    apply (C.energy_iff P.output n hn).mpr
    intro t ht
    rw [← ht]
    exact (P.output_zero_iff hA hb hd he t).mpr (ho t (by omega))
  · intro hz t ht
    have hpos := t.order.pos
    have hn : (t.order : ℕ)-1 < p := by omega
    have hg : (t.order : ℕ) = ((t.order : ℕ)-1)+1 := by omega
    apply (P.output_zero_iff hA hb hd he t).mp
    have hp := (C.energy_iff P.output _ hn).mp (hz _ hn) t hg
    rwa [← hg] at hp

end Semantics

end RKResearch.Certified.CoordinateRootedTreeGram

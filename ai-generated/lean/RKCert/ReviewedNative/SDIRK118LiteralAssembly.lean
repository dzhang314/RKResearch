module

public import RKCert.ReviewedNative.SDIRK118InstantiationAdapters
public import RKCert.ReviewedNative.DiagonalTwin
public import Mathlib.LinearAlgebra.Matrix.Notation

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.Graded (mat diag diag_apply mergeCoefficient)
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.PaidDefectBridge
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (Chart PolyBound Tableau wDot)
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation
open scoped Matrix BigOperators

variable {K : Type*} [Field K]

abbrev Vec (n : ℕ) (K : Type*) := Fin n → K

def rows {m n : ℕ} (F : Fin m → Vec n K →ₗ[K] K) : Vec n K →ₗ[K] Vec m K where
  toFun v i := F i v
  map_add' v w := by
    funext i
    exact map_add (F i) v w
  map_smul' a v := by
    funext i
    exact map_smul (F i) a v

def pull {m n : ℕ} (s : Fin m → Fin n) : Vec n K →ₗ[K] Vec m K :=
  rows (fun i => coordinate (s i))

def delta {n : ℕ} (j : Fin n) : Vec n K := fun i => if i=j then 1 else 0

def matrixOf {m n : ℕ} (F : Vec n K →ₗ[K] Vec m K) : Matrix (Fin m) (Fin n) K :=
  fun i j => F (delta j) i

/-- A literal row operator is emitted as its scalars on the coordinate units. -/
theorem matrixOf_mulVec {m n : ℕ} (F : Vec n K →ₗ[K] Vec m K) (v : Vec n K) :
    matrixOf F *ᵥ v=F v := by
  have hv : (∑ j : Fin n, v j • delta j)=v := by
    funext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,delta]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ h
      simp [Ne.symm h]
    · simp
  funext i
  calc
    (matrixOf F *ᵥ v) i = (F (∑ j : Fin n, v j • delta j)) i := by
      change (∑ j : Fin n, F (delta j) i*v j)=_
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    _=F v i := by rw [hv]

theorem mulVec_delta {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    (M *ᵥ delta j) i=M i j := by
  change (∑ k : Fin n, M i k*(if k=j then 1 else 0))=_
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

def site : Fin 8 → Fin 6 := ![1,5,4,0,3,2,1,0]
def oldIx : Fin 4 → Fin 8 := ![7,6,5,4]

def splitMass (W : Vec 6 K) : Vec 8 K :=
  ![W 1/2,W 5,W 4,W 0/2,W 3,W 2,W 1/2,W 0/2]

def C : Vec 8 K →ₗ[K] Vec 6 K :=
  rows ![(1/2 : K) • (coordinate 3+coordinate 7),
    (1/2 : K) • (coordinate 0+coordinate 6),coordinate 5,coordinate 4,coordinate 2,coordinate 1]

def S (γ a b c : K) : Vec 6 K →ₗ[K] Vec 6 K :=
  rows ![γ • coordinate 0,γ • coordinate 1,γ • coordinate 2,γ • coordinate 3,
    γ • coordinate 4+a • coordinate 0,γ • coordinate 5+b • coordinate 0+c • coordinate 4]

def oldProject (proj : Vec 4 K →ₗ[K] Polynomial K) : Vec 8 K →ₗ[K] Polynomial K :=
  proj.comp (pull oldIx)

def targetRows (Ey : Polynomial K →ₗ[K] Vec 6 K)
    (I : Polynomial K →ₗ[K] Polynomial K) (proj : Vec 4 K →ₗ[K] Polynomial K)
    (γ a b c : K) : Vec 8 K →ₗ[K] Vec 6 K :=
  Ey.comp (I.comp (oldProject proj)) +
    (S γ a b c).comp (C-Ey.comp (oldProject proj))

def revRows (R : Matrix (Fin 4) (Fin 4) K) (U : Vec 8 K →ₗ[K] Vec 6 K) :
    Vec 8 K →ₗ[K] Vec 8 K :=
  let O := (mat R).comp (pull oldIx)
  rows ![(2 : K) • ((coordinate 1).comp U)-(coordinate 1).comp O,
    (coordinate 5).comp U,(coordinate 4).comp U,
    (2 : K) • ((coordinate 0).comp U)-(coordinate 0).comp O,
    (coordinate 3).comp O,(coordinate 2).comp O,(coordinate 1).comp O,(coordinate 0).comp O]

def revMatrix (R : Matrix (Fin 4) (Fin 4) K) (U : Vec 8 K →ₗ[K] Vec 6 K) :
    Matrix (Fin 8) (Fin 8) K := matrixOf (revRows R U)

theorem rev_restrict (R : Matrix (Fin 4) (Fin 4) K) (U : Vec 8 K →ₗ[K] Vec 6 K)
    (v : Vec 8 K) :
    (revMatrix R U *ᵥ v) ∘ oldIx = R *ᵥ (v ∘ oldIx) := by
  rw [revMatrix,matrixOf_mulVec]
  funext i
  fin_cases i <;> rfl

theorem oldIx_val (k : Fin 4) : (oldIx k).val=7-k.val := by
  fin_cases k <;> decide

theorem oldIx_injective : Function.Injective oldIx := by
  intro i j h
  have e := congrArg Fin.val h
  rw [oldIx_val,oldIx_val] at e
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  omega

theorem old_delta_new (j : Fin 8) (hj : j.val<4) :
    (delta j : Vec 8 K) ∘ oldIx = 0 := by
  funext i
  have hi : oldIx i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    rw [oldIx_val] at hv
    have hs := i.isLt
    omega
  simp only [Function.comp_apply,delta,if_neg hi,Pi.zero_apply]

theorem reverse_old_block (R : Matrix (Fin 4) (Fin 4) K)
    (U : Vec 8 K →ₗ[K] Vec 6 K) (i j : Fin 4) :
    revMatrix R U (oldIx i) (oldIx j)=R i j := by
  have hd : (delta (oldIx j) : Vec 8 K) ∘ oldIx=delta j := by
    funext k
    simp only [Function.comp_apply,delta,oldIx_injective.eq_iff]
  have h := congrArg (fun z : Vec 4 K => z i) (rev_restrict R U (delta (oldIx j)))
  simpa only [Function.comp_apply,hd,mulVec_delta] using h

theorem reverse_old_new (R : Matrix (Fin 4) (Fin 4) K)
    (U : Vec 8 K →ₗ[K] Vec 6 K) (i : Fin 4) (j : Fin 8) (hj : j.val<4) :
    revMatrix R U (oldIx i) j=0 := by
  have h := congrArg (fun z : Vec 4 K => z i) (rev_restrict R U (delta j))
  rw [old_delta_new j hj] at h
  change (revMatrix R U *ᵥ delta j) (oldIx i)=(mat R 0) i at h
  simpa only [mulVec_delta,map_zero,Pi.zero_apply] using h

def newIx (i : Fin 4) : Fin 8 := ⟨i.val,by omega⟩

def newBlock (γ a b c : K) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => (if i=j then γ else 0)+
    (if i=1 then (if j=2 then c else if j=3 then b/2 else 0)
      else if i=2 ∧ j=3 then a/2 else 0)

/-- All new-column contributions are the site contrasts. Primitive and
evaluation rows depend only on old columns, so they vanish in this table. -/
theorem reverse_new_block [CharZero K]
    (R : Matrix (Fin 4) (Fin 4) K) (Ey : Polynomial K →ₗ[K] Vec 6 K)
    (I : Polynomial K →ₗ[K] Polynomial K) (proj : Vec 4 K →ₗ[K] Polynomial K)
    (γ a b c : K) (i j : Fin 4) :
    revMatrix R (targetRows Ey I proj γ a b c) (newIx i) (newIx j)=newBlock γ a b c i j := by
  have u (k : Fin 8) (hk : k.val < 4) :
      targetRows Ey I proj γ a b c (delta k) = S γ a b c (C (delta k)) := by
    change Ey (I (proj (pull oldIx (delta k)))) +
      S γ a b c (C (delta k) - Ey (proj (pull oldIx (delta k)))) = _
    have hz : pull oldIx (delta k : Vec 8 K) = 0 := old_delta_new k hk
    simp only [hz, map_zero, sub_zero, zero_add]
  have o (k : Fin 8) (hk : k.val < 4) : R *ᵥ pull oldIx (delta k) = 0 := by
    have hz : pull oldIx (delta k : Vec 8 K) = 0 := old_delta_new k hk
    rw [hz, Matrix.mulVec_zero]
  change revRows R (targetRows Ey I proj γ a b c) (delta (newIx j)) (newIx i) = _
  fin_cases i <;> fin_cases j <;>
    simp [revRows, rows, coordinate, C, S, delta, newIx, newBlock,
      u 0 (by decide), u 1 (by decide), u 2 (by decide), u 3 (by decide),
      o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide)] <;> try ring

theorem split_indices (i : Fin 8) :
    (∃ j : Fin 4,i=newIx j) ∨ (∃ j : Fin 4,i=oldIx j) := by
  by_cases h : i.val<4
  · exact Or.inl ⟨⟨i.val,h⟩,Fin.ext rfl⟩
  · have hi := i.isLt
    let j : Fin 4 := ⟨7-i.val,by omega⟩
    refine Or.inr ⟨j,Fin.ext ?_⟩
    rw [oldIx_val]
    change i.val=7-(7-i.val)
    omega

theorem reverse_upper_diag [CharZero K]
    (R : Matrix (Fin 4) (Fin 4) K) (Ey : Polynomial K →ₗ[K] Vec 6 K)
    (I : Polynomial K →ₗ[K] Polynomial K) (proj : Vec 4 K →ₗ[K] Polynomial K)
    (γ a b c : K) (hR : R.IsLowerTriangular) (hD : ∀ i,R i i=γ) :
    let L := revMatrix R (targetRows Ey I proj γ a b c)
    (∀ i j, j < i → L i j=0) ∧ ∀ i,L i i=γ := by
  dsimp
  constructor
  · intro i j hij
    rcases split_indices i with ⟨u,rfl⟩ | ⟨u,rfl⟩ <;>
      rcases split_indices j with ⟨v,rfl⟩ | ⟨v,rfl⟩
    · rw [reverse_new_block]
      have hv : v<u := hij
      fin_cases u <;> fin_cases v <;> simp [newBlock] at hv ⊢
    · change (oldIx v).val<u.val at hij
      rw [oldIx_val] at hij
      have hu := u.isLt
      have hv := v.isLt
      omega
    · exact reverse_old_new R _ u (newIx v) v.isLt
    · rw [reverse_old_block]
      apply hR
      change (oldIx v).val<(oldIx u).val at hij
      rw [oldIx_val,oldIx_val] at hij
      have hu := u.isLt
      have hv := v.isLt
      change u.val<v.val
      omega
  · intro i
    rcases split_indices i with ⟨u,rfl⟩ | ⟨u,rfl⟩
    · rw [reverse_new_block]
      fin_cases u <;> simp [newBlock]
    · rw [reverse_old_block,hD]

/-- The aggregate is a full operator identity, with only the two genuine
old singleton rows proved by anchor transport. The other four are literal. -/
theorem aggregate_target [CharZero K] (R : Matrix (Fin 4) (Fin 4) K)
    (Ey : Polynomial K →ₗ[K] Vec 6 K)
    (I : Polynomial K →ₗ[K] Polynomial K) (proj : Vec 4 K →ₗ[K] Polynomial K)
    (γ a b c : K)
    (hE2 : ∀ v : Vec 4 K, Ey (proj v) 2=v 2)
    (hE3 : ∀ v : Vec 4 K, Ey (proj v) 3=v 3)
    (hI2 : ∀ v : Vec 4 K, Ey (I (proj v)) 2=(R *ᵥ v) 2)
    (hI3 : ∀ v : Vec 4 K, Ey (I (proj v)) 3=(R *ᵥ v) 3)
    (v : Vec 8 K) :
    C (revMatrix R (targetRows Ey I proj γ a b c) *ᵥ v)=targetRows Ey I proj γ a b c v := by
  rw [revMatrix,matrixOf_mulVec]
  let U := targetRows Ey I proj γ a b c
  let O := (mat R (v ∘ oldIx))
  funext i
  fin_cases i
  · change (1/2 : K)*((2*U v 0-O 0)+O 0)=U v 0
    ring
  · change (1/2 : K)*((2*U v 1-O 1)+O 1)=U v 1
    ring
  · change O 2=Ey (I (proj (v ∘ oldIx))) 2+
      γ*(v 5-Ey (proj (v ∘ oldIx)) 2)
    rw [hI2,hE2]
    change O 2=O 2+γ*(v 5-v 5)
    simp
  · change O 3=Ey (I (proj (v ∘ oldIx))) 3+
      γ*(v 4-Ey (proj (v ∘ oldIx)) 3)
    rw [hI3,hE3]
    change O 3=O 3+γ*(v 4-v 4)
    simp
  · rfl
  · rfl

def suffix (W : Vec 6 K) (L : Matrix (Fin 8) (Fin 8) K) : Matrix (Fin 8) (Fin 8) K :=
  fun i j => (splitMass W j/splitMass W i)*L j i

theorem balance_exact (W : Vec 6 K) (L : Matrix (Fin 8) (Fin 8) K)
    (hw : ∀ i, splitMass W i ≠ 0) (i j : Fin 8) :
    splitMass W i*suffix W L i j=splitMass W j*L j i := by
  unfold suffix
  field_simp [hw i] <;> ring

def xEval (Ex : Polynomial K →ₗ[K] Vec 6 K) : Polynomial K →ₗ[K] Vec 8 K :=
  (pull site).comp Ex

def crossOperator (T : Matrix (Fin 8) (Fin 8) K)
    (Ex : Polynomial K →ₗ[K] Vec 6 K) (I : Polynomial K →ₗ[K] Polynomial K)
    (Projf : Vec 4 K →ₗ[K] Polynomial K) : Vec 4 K →ₗ[K] Vec 8 K :=
  ((xEval Ex).comp I-(mat T).comp (xEval Ex)).comp Projf

def blocks (G : Matrix (Fin 4) (Fin 4) K) (D : Matrix (Fin 8) (Fin 4) K)
    (T : Matrix (Fin 8) (Fin 8) K) : Tableau K
  | .inl i,.inl j => G i j
  | .inl _,.inr _ => 0
  | .inr i,.inl j => D i j
  | .inr i,.inr j => T i j

theorem split_nonzero [CharZero K] (W : Vec 6 K) (h : ∀ i, W i ≠ 0) :
    ∀ i, splitMass W i ≠ 0 := by
  intro i
  fin_cases i <;> simp [splitMass,h,div_ne_zero]

theorem cluster_dot [CharZero K] (W a : Vec 6 K) (v : Vec 8 K) :
    wDot (splitMass W) v (a ∘ site) = wDot W (C v) a := by
  simp [wDot,splitMass,site,C,rows,coordinate,Fin.sum_univ_succ,Function.comp_apply]
  <;> ring

theorem C_one [CharZero K] : C (1 : Vec 8 K)=1 := by
  funext i
  fin_cases i <;> norm_num [C,rows,coordinate]

theorem cluster_clock [CharZero K] (x : Vec 6 K) (v : Vec 8 K) :
    C (diag (x ∘ site) v) = x * C v := by
  funext i
  fin_cases i <;> simp [C,rows,coordinate,site,diag_apply,Function.comp_apply] <;> ring

theorem site_quadrature_split [CharZero K] {p : ℕ} (W x : Vec 6 K)
    (h : HasQuadratureOrder p W x) :
    HasQuadratureOrder p (splitMass W) (x ∘ site) := by
  intro n hn
  have e := cluster_dot W (x^n) (1 : Vec 8 K)
  rw [C_one] at e
  have e' : splitMass W ⬝ᵥ ((x ∘ site)^n) = W ⬝ᵥ (x^n) := by
    simpa only [wDot,dotProduct,Pi.one_apply,mul_one,Pi.pow_apply,Function.comp_apply] using e
  rw [e']
  exact h n hn

theorem strict_entries [CharZero K] (W u e : Vec 6 K) (γ a b c : K) :
    wDot W u (S γ a b c e-γ • e) =
      W 4*u 4*a*e 0+W 5*u 5*b*e 0+W 5*u 5*c*e 4 := by
  simp [wDot,S,rows,coordinate,Fin.sum_univ_succ,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  <;> ring

/-- Input of exact scalar/forward/reverse data, not a 12-stage matrix.
The proper literals are the objects emitted below. -/
structure Geometry (K : Type*) [Field K] where
  G : Matrix (Fin 4) (Fin 4) K
  R : Matrix (Fin 4) (Fin 4) K
  W : Vec 6 K
  γ : K
  Ex : Polynomial K →ₗ[K] Vec 6 K
  Ey : Polynomial K →ₗ[K] Vec 6 K
  I : Polynomial K →ₗ[K] Polynomial K
  Projf : Vec 4 K →ₗ[K] Polynomial K
  Projr : Vec 4 K →ₗ[K] Polynomial K
  HF : Fin 2 → Polynomial K
  KR : Fin 2 → Polynomial K

def ideal (t : FiniteRootedTree) : Polynomial K :=
  (forestNat t : K)⁻¹ • Polynomial.X ^ treeGrade t

namespace Geometry

variable (g : Geometry K)

def pairing (H J : Polynomial K) : K :=
  wDot g.W (g.Ex H) (g.Ey (g.I J)-g.γ • g.Ey J)

def t40 : K := g.pairing (g.HF 0) (g.KR 0)/g.W 4
def t50 : K := g.pairing (g.HF 1) (g.KR 0)/g.W 5
def t54 : K := g.pairing (g.HF 1) (g.KR 1)/g.W 5
def U : Vec 8 K →ₗ[K] Vec 6 K := targetRows g.Ey g.I g.Projr g.γ g.t40 g.t50 g.t54
def L : Matrix (Fin 8) (Fin 8) K := revMatrix g.R g.U
def T : Matrix (Fin 8) (Fin 8) K := suffix g.W g.L
def D : Matrix (Fin 8) (Fin 4) K := matrixOf (crossOperator g.T g.Ex g.I g.Projf)
def A : Tableau K := blocks g.G g.D g.T
def w : Vec 8 K := splitMass g.W
def ξ : Vec 8 K := (g.Ex Polynomial.X) ∘ site
def b : Fin 4 ⊕ Fin 8 → K := Sum.elim (0 : Vec 4 K) g.w

def F (t : FiniteRootedTree) : Polynomial K := ideal t-g.Projf (Φ t g.G)

def chart : Chart K where
  mass := g.W
  site := site
  C := C
  L := g.L
  I := g.I
  Ex := g.Ex
  Ey := g.Ey
  projectOld := oldProject g.Projr
  S := S g.γ g.t40 g.t50 g.t54
  F := g.F
  gamma := g.γ
  s40 := g.t40
  s50 := g.t50
  s54 := g.t54

theorem prefix_exact (t : FiniteRootedTree) : Φ t g.A ∘ Sum.inl=Φ t g.G :=
  phi_comp_of_mulVec g.A g.G Sum.inl
    (mulVec_inl_of_upperRight_zero g.A g.G (fun _ _ => rfl) (fun _ _ => rfl)) t

theorem exact_cross (v : Vec 4 K) :
    crossBlock g.A *ᵥ v =
      g.chart.liftSites (g.Ex (g.I (g.Projf v))) -
        mat (suffixBlock g.A) (g.chart.liftSites (g.Ex (g.Projf v))) :=
  matrixOf_mulVec (crossOperator g.T g.Ex g.I g.Projf) v

theorem exact_graft
    (hD : ∀ t, g.chart.liftSites (g.Ex (ideal t))=idealDerivative g.ξ t)
    (hI : ∀ t, g.chart.liftSites (g.Ex (g.I (ideal t)))=idealPrimitive g.ξ t) :
    ∀ t, primitiveSeed g.A g.ξ t=g.chart.graftVector g.A (g.F t) := by
  refine g.chart.graft_of_cross g.A g.ξ g.Projf ideal ?_ hD hI g.exact_cross
  intro t
  change ideal t-g.Projf (Φ t g.G)=ideal t-g.Projf (Φ t g.A ∘ Sum.inl)
  rw [g.prefix_exact]

/-- The two reviewed scalar profile bindings from monomial evaluation and
the coefficient primitive. No two extra parameter identities are needed. -/
theorem ideal_bindings
    (evalPow : ∀ n : ℕ, g.Ex (Polynomial.X^n)=(g.Ex Polynomial.X)^n)
    (intPow : ∀ n : ℕ, g.I (Polynomial.X^n)=
      ((n+1 : ℕ) : K)⁻¹ • (Polynomial.X^(n+1))) :
    (∀ t, g.chart.liftSites (g.Ex (ideal t))=idealDerivative g.ξ t) ∧
    (∀ t, g.chart.liftSites (g.Ex (g.I (ideal t)))=idealPrimitive g.ξ t) := by
  constructor
  · intro t
    simp only [ideal,map_smul,evalPow,idealDerivative] <;> rfl
  · intro t
    have pos : 0 < treeSize t := t.order.pos
    have sizeEq : treeGrade t+1=treeSize t := by
      change treeSize t-1+1=treeSize t
      omega
    have facEq : factorialNat t=treeSize t*forestNat t := by
      simp only [factorialNat,treeSize,forestNat,FiniteRootedTree.factorial,PNat.mul_coe]
    simp only [ideal,map_smul,intPow,evalPow,idealPrimitive,sizeEq,facEq,Nat.cast_mul,mul_inv_rev]
    rw [←mul_smul]
    rfl

/-- The operator fields are produced, not passed as a Chart.Laws witness.
The low/budget fields and the unrelated degree-seven scalar flux come
from the earlier small core proofs. -/
theorem make_laws [CharZero K]
    (hW : ∀ i, g.W i ≠ 0)
    (hE2 : ∀ v : Vec 4 K, g.Ey (g.Projr v) 2=v 2)
    (hE3 : ∀ v : Vec 4 K, g.Ey (g.Projr v) 3=v 3)
    (hI2 : ∀ v : Vec 4 K, g.Ey (g.I (g.Projr v)) 2=(g.R *ᵥ v) 2)
    (hI3 : ∀ v : Vec 4 K, g.Ey (g.I (g.Projr v)) 3=(g.R *ᵥ v) 3)
    (he1 : g.Ey 1=1)
    (heC : ∀ Q, g.Ey ((1-Polynomial.X)*Q)=(g.Ex Polynomial.X)*g.Ey Q)
    (hD : ∀ t, g.chart.liftSites (g.Ex (ideal t))=idealDerivative g.ξ t)
    (hI : ∀ t, g.chart.liftSites (g.Ex (g.I (ideal t)))=idealPrimitive g.ξ t)
    (hOld : ∀ U : List Letter, U.length≤2 → g.chart.revDefect g.ξ U=0)
    (hLow : ∀ t, treeSize t≤3 → g.F t=0)
    (hSeed : ∀ t, PolyBound (treeGrade t) (g.F t))
    (hDeg : ∀ U, PolyBound U.length (g.chart.profile U))
    (hFlux : ∀ (H Q : Polynomial K) (n m : ℕ),
      PolyBound n H → PolyBound m Q → n+m+1≤7 →
      wDot g.W (g.Ex H) (g.Ey (g.I Q)) =
        wDot g.W (g.Ex (g.I H)) (g.Ey Q)) :
    g.chart.Laws g.A g.w g.ξ where
  balance := balance_exact g.W g.L (split_nonzero g.W hW)
  cluster := fun v a => cluster_dot g.W a v
  aggregate := aggregate_target g.R g.Ey g.I g.Projr g.γ g.t40 g.t50 g.t54 hE2 hE3 hI2 hI3
  init := by
    change C (1 : Vec 8 K)=g.Ey 1
    rw [C_one,he1]
  clock := by
    intro v Q hQ
    change C (diag ((g.Ex Polynomial.X) ∘ site) v)=g.Ey ((1-Polynomial.X)*Q)
    change C v=g.Ey Q at hQ
    rw [cluster_clock,hQ,heC]
  oldShort := hOld
  prefixLow := hLow
  graft := g.exact_graft hD hI
  seedDegree := hSeed
  profileDegree := hDeg
  green := hFlux

theorem tap_support [CharZero K] : g.chart.ExactSupport := by
  intro u e
  exact strict_entries g.W u e g.γ g.t40 g.t50 g.t54

/- Assemble the already proved kernel fields by the checked scalar/order
 bridge. There is no assumed paid short word or top expansion here. -/
theorem emitted_order [CharZero K]
    (hW : ∀ i, g.W i ≠ 0)
    (hQuad : HasQuadratureOrder 8 g.W (g.Ex Polynomial.X))
    (h : g.chart.Laws g.A g.w g.ξ)
    (hF : ∀ t, treeSize t=4 →
      g.F t=g.Ex (g.F t) 4 • g.HF 0+g.Ex (g.F t) 5 • g.HF 1)
    (hR : ∀ U : List Letter, U.length=3 →
      g.chart.revDefect g.ξ U=g.Ey (g.chart.revDefect g.ξ U) 0 • g.KR 0+
        g.Ey (g.chart.revDefect g.ξ U) 4 • g.KR 1)
    (Δ Dcal cal : K) (hΔ : Δ ≠ 0) (hDcal : Dcal ≠ 0)
    (hscale : cal=-(Δ*Dcal)*g.pairing (g.HF 0) (g.KR 1))
    (hzero : cal=0) : HasOrder 8 g.A g.b := by
  exact Chart.hasOrder_eight_of_chart_calibration h g.HF g.KR Δ Dcal cal
    (site_quadrature_split g.W (g.Ex Polynomial.X) hQuad) g.tap_support
    ⟨hF,hR⟩ rfl rfl rfl (hW 4) (hW 5) hΔ hDcal hscale hzero

end Geometry

theorem suffix_lower_diag (W : Vec 6 K) (L : Matrix (Fin 8) (Fin 8) K) (γ : K)
    (hw : ∀ i, splitMass W i ≠ 0)
    (hL : ∀ i j, j < i → L i j=0) (hγ : ∀ i, L i i=γ) :
    (suffix W L).IsLowerTriangular ∧ ∀ i, suffix W L i i=γ := by
  constructor
  · intro i j hij
    simp only [suffix,hL j i hij,mul_zero]
  · intro i
    rw [suffix,hγ,div_self (hw i),one_mul]

theorem first_row_of_lower (T : Matrix (Fin 8) (Fin 8) K) (γ : K)
    (hT : T.IsLowerTriangular) (h00 : T 0 0=γ) (v : Vec 8 K) :
    (T *ᵥ v) 0=γ*v 0 := by
  change (∑ j : Fin 8,T 0 j*v j)=γ*v 0
  rw [Finset.sum_eq_single (0 : Fin 8)]
  · rw [h00]
  · intro j _ hj
    have hv : j.val ≠ 0 := fun e => hj (Fin.ext e)
    have hp : (0 : Fin 8)<j := by change 0<j.val; omega
    have hz : T (0 : Fin 8) j = 0 := hT hp
    rw [hz, zero_mul]
  · simp

namespace Geometry

variable (g : Geometry K)

theorem suffix_shape [CharZero K]
    (hW : ∀ i,g.W i≠0) (hR : g.R.IsLowerTriangular) (hRdiag : ∀ i,g.R i i=g.γ) :
    g.T.IsLowerTriangular ∧ ∀ i,g.T i i=g.γ := by
  obtain ⟨hUL,hDL⟩ := reverse_upper_diag g.R g.Ey g.I g.Projr g.γ g.t40 g.t50 g.t54 hR hRdiag
  exact suffix_lower_diag g.W g.L g.γ (split_nonzero g.W hW) hUL hDL

/-- This is the shifted row on the entire 12-coordinate space, not a
statement just about two equal clock values. -/
theorem corrected_sum_rows
    (hT : g.T.IsLowerTriangular) (h00 : g.T 0 0=g.γ)
    (anchor : ∀ v : Vec 4 K,
      (g.G *ᵥ v) 2-g.γ*v 2 =
        g.Ex (g.I (g.Projf v)) 1-g.γ*g.Ex (g.Projf v) 1)
    (s : Fin 4 ⊕ Fin 8) :
    g.A (.inr 0) s-(if s=Sum.inr 0 then g.γ else 0)=
      g.A (.inl 2) s-(if s=Sum.inl 2 then g.γ else 0) := by
  cases s with
  | inl j =>
    have e := congrArg (fun z : Vec 8 K => z 0) (g.exact_cross (delta j))
    change (g.D *ᵥ delta j) 0 =
      g.Ex (g.I (g.Projf (delta j))) 1-
        (g.T *ᵥ xEval g.Ex (g.Projf (delta j))) 0 at e
    rw [mulVec_delta,first_row_of_lower g.T g.γ hT h00] at e
    change g.D 0 j =
      g.Ex (g.I (g.Projf (delta j))) 1-g.γ*g.Ex (g.Projf (delta j)) 1 at e
    rw [←anchor (delta j),mulVec_delta] at e
    by_cases hj : j=2
    · subst j
      simpa [A,blocks,delta] using e
    · simpa [A,blocks,delta,hj,Ne.symm hj] using e
  | inr j =>
    have e := first_row_of_lower g.T g.γ hT h00 (delta j)
    rw [mulVec_delta] at e
    by_cases hj : j=0
    · subst j
      simp [A,blocks,h00]
    · have z : g.T 0 j=0 := by simpa [delta,Ne.symm hj] using e
      simp [A,blocks,z,hj]

end Geometry

section Relabel

variable {J Kidx : Type*} [Fintype J] [Fintype Kidx]

/-- Reviewed order transported by a finite renaming. -/
theorem relabel_order {p : ℕ} (e : J ≃ Kidx)
    (A : Matrix J J K) (b : J → K) (h : HasOrder p A b) :
    HasOrder p (A.submatrix e.symm e.symm) (b ∘ e.symm) := by
  have mul : ∀ v : J → K, (A *ᵥ v) ∘ e.symm =
      A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) := by
    intro v
    funext i
    change (∑ j : J,A (e.symm i) j*v j) =
      ∑ j : Kidx,A (e.symm i) (e.symm j)*v (e.symm j)
    exact (e.symm.sum_comp (fun j : J => A (e.symm i) j*v j)).symm
  intro t ht
  have eφ := phi_comp_of_mulVec A (A.submatrix e.symm e.symm) e.symm mul t
  rw [←eφ]
  have dot : (b ∘ e.symm) ⬝ᵥ (Φ t A ∘ e.symm)= b ⬝ᵥ Φ t A := by
    change (∑ i : Kidx,b (e.symm i)*Φ t A (e.symm i))=∑ j : J,b j*Φ t A j
    exact e.symm.sum_comp (fun j : J => b j*Φ t A j)
  rw [dot]
  exact h t ht

end Relabel

namespace Geometry

variable (g : Geometry K)

/-- The canonical block relabeling is supplied with its two elementary
index formulas. This statement does not assume any 12-stage identities. -/
theorem finish_fin11
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    (eL : ∀ i : Fin 4, (e (.inl i)).val=i.val)
    (eR : ∀ i : Fin 8, (e (.inr i)).val=4+i.val)
    (hγ : g.γ ≠ 0)
    (hGL : g.G.IsLowerTriangular) (hGD : ∀ i, g.G i i=g.γ)
    (hTL : g.T.IsLowerTriangular) (hTD : ∀ i, g.T i i=g.γ)
    (anchor : ∀ v : Vec 4 K,
      (g.G *ᵥ v) 2-g.γ*v 2 =
        g.Ex (g.I (g.Projf v)) 1-g.γ*g.Ex (g.Projf v) 1)
    (h8 : HasOrder 8 g.A g.b) :
    let A12 := g.A.submatrix e.symm e.symm
    let b12 := g.b ∘ e.symm
    let B := contractMatrix (4 : Fin 12) (2 : Fin 11) A12
    let b := mergeCoefficient (4 : Fin 12) (2 : Fin 11) b12
    B.IsLowerTriangular ∧ (∀ i,B i i=g.γ) ∧ g.γ ≠ 0 ∧ HasOrder 8 B b := by
  let A12 := g.A.submatrix e.symm e.symm
  let b12 := g.b ∘ e.symm
  have order12 : HasOrder 8 A12 b12 := relabel_order e g.A g.b h8
  have zeros (i j : Fin 4 ⊕ Fin 8) (h : e i<e j) : g.A i j=0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        apply hGL
        change (e (.inl i)).val<(e (.inl j)).val at h
        change i.val < j.val
        simpa only [eL] using h
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        have hj := j.isLt
        change (e (.inr i)).val<(e (.inl j)).val at h
        rw [eR,eL] at h
        omega
      | inr j =>
        apply hTL
        change (e (.inr i)).val<(e (.inr j)).val at h
        rw [eR,eR] at h
        change i.val<j.val
        omega
  have lower12 : A12.IsLowerTriangular := by
    intro i j hij
    exact zeros (e.symm i) (e.symm j) (by simpa using hij)
  have diag12 (i) : A12 i i=g.γ := by
    change g.A (e.symm i) (e.symm i)=g.γ
    cases e.symm i with
    | inl j => exact hGD j
    | inr j => exact hTD j
  have e2 : e (.inl (2 : Fin 4))=(2 : Fin 12) := Fin.ext (eL 2)
  have e4 : e (.inr (0 : Fin 8))=(4 : Fin 12) := Fin.ext (eR 0)
  have i2 : e.symm (2 : Fin 12)=Sum.inl (2 : Fin 4) := by rw [←e2,e.symm_apply_apply]
  have i4 : e.symm (4 : Fin 12)=Sum.inr (0 : Fin 8) := by rw [←e4,e.symm_apply_apply]
  have ri (i j : Fin 12) (s : Fin 4 ⊕ Fin 8) (hs : e.symm i=s) :
      j=i ↔ e.symm j=s := by
    constructor
    · rintro rfl
      exact hs
    · intro h
      exact e.symm.injective (h.trans hs.symm)
  have twins : RKResearch.Certified.DiagonalTwin.DiagonalTwins
      (4 : Fin 12) (2 : Fin 11) g.γ A12 := by
    intro j
    have hj : (4 : Fin 12).succAbove (2 : Fin 11)=(2 : Fin 12) := by decide
    simpa only [hj,A12,Matrix.submatrix_apply,i2,i4,
      ri 4 j _ i4,ri 2 j _ i2] using g.corrected_sum_rows hTL (hTD 0) anchor (e.symm j)
  have chron : (4 : Fin 12).succAbove (2 : Fin 11)<(4 : Fin 12) := by decide
  exact RKResearch.Certified.DiagonalTwin.contract_strict_sdirk
    (n := 11) (p := 8) (j := (4 : Fin 12)) (r := (2 : Fin 11))
    chron lower12 diag12 hγ twins order12

end Geometry

end RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly

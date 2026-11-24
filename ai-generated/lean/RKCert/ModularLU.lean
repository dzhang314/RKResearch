module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
@[expose] public section
namespace RKCert.LU
open Matrix
universe u
variable {n:ℕ} {R:Type u} [CommRing R]

/-- Original-row lookup after a finite list of genuine physical row swaps. -/
def permute : List (Fin n×Fin n)→Fin n→Fin n
  | []=>id
  | (i,j)::w=>fun k=>permute w (Equiv.swap i j k)
def sign (R:Type*) [CommRing R] : List (Fin n×Fin n)→R
  | []=>1
  | (i,j)::w=>if i=j then sign R w else -sign R w

theorem swap_sign_sq (w:List (Fin n×Fin n)):sign R w*sign R w=1:=by
  induction w with
  | nil=>simp [sign]
  | cons q w ih=>rcases q with ⟨i,j⟩;by_cases eqn:i=j <;> simp [sign,eqn,ih]

theorem det_permuted (M:Matrix (Fin n) (Fin n) R) (w:List (Fin n×Fin n)):
    (M.submatrix (permute w) id).det=sign R w*M.det:=by
  induction w with
  | nil=>simp [permute,sign]
  | cons q w ih=>
    rcases q with ⟨i,j⟩
    change ((M.submatrix (permute w) id).submatrix (Equiv.swap i j) id).det=_
    rw [Matrix.det_permute,ih]
    by_cases e:i=j
    · simp [e,sign]
    · simp [Equiv.Perm.sign_swap e,sign,e]

/-- PLU certificates work over any commutative ring, including singular
U. The computation does not invert a pivot: only the producer does so. -/
theorem det_of_lu (M L U:Matrix (Fin n) (Fin n) R) (w:List (Fin n×Fin n))
    (eqn:M.submatrix (permute w) id=L*U)
    (lt:L.IsLowerTriangular) (ut:U.IsUpperTriangular) (ones:∀i,L i i=1) :
    M.det=sign R w*∏i,U i i:=by
  have h:sign R w*M.det=∏i,U i i:=by
    rw [←det_permuted,eqn,Matrix.det_mul,Matrix.det_of_isLowerTriangular _ lt,
      Matrix.det_of_isUpperTriangular ut];simp [ones]
  calc
    M.det=(sign R w*sign R w)*M.det:=by rw [swap_sign_sq,one_mul]
    _=sign R w*∏i,U i i:=by rw [mul_assoc,h]

def base:ℕ:=1024
def digit (a k:ℕ):ℕ:=(a/base^k)%base
def get (xs:Array ℕ) (i:ℕ):ℕ:=xs[i]?.getD 0
def rowMatrix (p n:ℕ)(rows:Array ℕ):Matrix (Fin n) (Fin n) (ZMod p):=
  fun i j=>(digit (get rows i.val) j.val:ℕ)
def colMatrix (p n:ℕ)(cols:Array ℕ):Matrix (Fin n) (Fin n) (ZMod p):=
  fun i j=>(digit (get cols j.val) i.val:ℕ)

def dot : ℕ→ℕ→ℕ→ℕ
  | 0,_,_=>0
  | k+1,a,b=>a%base*(b%base)+dot k (a/base) (b/base)

theorem digit_div (x k:ℕ):digit (x/base) k=digit x (k+1):=by
  simp only [digit,Nat.div_div_eq_div_mul,pow_succ, Nat.mul_comm base]

theorem dot_eq (n a b:ℕ):dot n a b=∑k∈Finset.range n,digit a k*digit b k:=by
  induction n generalizing a b with
  | zero=>simp [dot]
  | succ n ih=>
    rw [dot,ih,Finset.sum_range_succ']
    simp only [digit_div]
    have zero (x:ℕ):digit x 0=x%base:=by simp [digit]
    rw [zero,zero];omega

theorem digit_zero_of_bound {x i j:ℕ} (bound:x<base^(i+1)) (bigger:i<j):digit x j=0:=by
  have top:x<base^j:=bound.trans_le (Nat.pow_le_pow_right (by decide:0<base) (by omega))
  simp [digit,Nat.div_eq_of_lt top]

/-- Each input integer is one row (or one column), little-endian base 1024.
A single modular reduction after an entire integer dot product suffices. -/
theorem det_dense (p:ℕ) (M L U:Array ℕ) (w:List (Fin n×Fin n)) (v:ZMod p)
    (lower:∀i:Fin n,get L i.val<base^(i.val+1) ∧ digit (get L i.val) i.val=1)
    (upper:∀j:Fin n,get U j.val<base^(j.val+1))
    (mul:∀i j:Fin n,(digit (get M (permute w i).val) j.val:ZMod p)=
      (dot n (get L i.val) (get U j.val):ZMod p))
    (value:sign (ZMod p) w*(∏i:Fin n,(digit (get U i.val) i.val:ZMod p))=v):
    (rowMatrix p n M).det=v:=by
  rw [←value];apply det_of_lu (rowMatrix p n M) (rowMatrix p n L) (colMatrix p n U) w
  · ext i j
    change (digit (get M (permute w i).val) j.val:ZMod p)=_
    rw [mul,dot_eq,Nat.cast_sum,Matrix.mul_apply]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl;intro k _;simp only [Nat.cast_mul,rowMatrix,colMatrix]
  · intro i j less;change i < j at less
    change (digit (get L i.val) j.val:ZMod p)=0
    rw [digit_zero_of_bound (lower i).1 less,Nat.cast_zero]
  · intro i j less;change j < i at less
    change (digit (get U j.val) i.val:ZMod p)=0
    rw [digit_zero_of_bound (upper j) less,Nat.cast_zero]
  · intro i;change (digit (get L i.val) i.val:ZMod p)=1
    rw [(lower i).2,Nat.cast_one]
end RKCert.LU

module
public import RKCert.ModularLU
@[expose] public section
namespace RKCert.LU
def wide:ℕ:=2^32
def lane (B a k:ℕ):ℕ:=(a/B^k)%B
def pack (B n:ℕ)(f:ℕ→ℕ):ℕ:=∑k∈Finset.range n,f k*B^k

theorem pack_succ (B n:ℕ)(f:ℕ→ℕ):pack B (n+1) f=f 0+B*pack B n (fun k=>f (k+1)):=by
  rw [pack,Finset.sum_range_succ',pack,Finset.mul_sum]
  simp only [pow_zero,mul_one,pow_succ]
  rw [Nat.add_comm (f 0)];congr 1
  apply Finset.sum_congr rfl;intro i _;ring
theorem lane_div (B x k:ℕ):lane B (x/B) k=lane B x (k+1):=by
  simp only [lane,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm B]

theorem lane_pack (B:ℕ)(pos:0<B)(n:ℕ)(f:ℕ→ℕ)(bound:∀k<n,f k<B) {j:ℕ}(pay:j<n):
    lane B (pack B n f) j=f j:=by
  induction n generalizing j f with
  | zero=>omega
  | succ n ih=>
    rw [pack_succ]
    have h0:=bound 0 (by omega)
    cases j with
    | zero=>simp [lane,Nat.mod_eq_of_lt h0]
    | succ j=>
      rw [←lane_div,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt h0,zero_add]
      apply ih (fun k=>f (k+1)) (fun k hk=>bound (k+1) (by omega)) (by omega)

def recode (A B p:ℕ):ℕ→ℕ→ℕ
  | 0,_=>0
  | n+1,x=>x%A%p+B*recode A B p n (x/A)

theorem recode_pack (A B p n x:ℕ):recode A B p n x=pack B n (fun k=>lane A x k%p):=by
  induction n generalizing x with
  | zero=>simp [recode,pack]
  | succ n ih=>rw [recode,pack_succ,ih];simp only [lane_div];simp [lane]
/-- Scatter base-1024 matrix entries to independent 32-bit lanes. -/
def widen (n x:ℕ):ℕ:=recode base wide base n x
theorem widen_pack (n x:ℕ):widen n x=pack wide n (fun j=>digit x j):=by
  rw [widen,recode_pack];congr 1;funext j;exact Nat.mod_mod .. 

/-- One packed multi-precision row combination. Each inner coefficient is
ordinary exact natural arithmetic; its no-carry proof occurs once for every
matrix dimension, not inside the concrete numeric computation. -/
def combine (l:ℕ)(w:Array ℕ):ℕ→ℕ
  | 0=>0
  | n+1=>combine l w n+digit l n*get w n

theorem combine_sum (l:ℕ)(w:Array ℕ)(n:ℕ):combine l w n=∑k∈Finset.range n,digit l k*get w k:=by
  induction n with
  | zero=>simp [combine]
  | succ n ih=>rw [combine,ih,Finset.sum_range_succ]

def dotAt (l:ℕ)(U:Array ℕ)(n j:ℕ):ℕ:=∑k∈Finset.range n,digit l k*digit (get U k) j

theorem combine_pack (l:ℕ)(w U:Array ℕ)(n:ℕ)(input:∀i:Fin n,get w i.val=widen n (get U i.val)):
    combine l w n=pack wide n (dotAt l U n):=by
  rw [combine_sum]
  calc
    _=∑k∈Finset.range n,∑j∈Finset.range n,digit l k*digit (get U k) j*wide^j:=by
      apply Finset.sum_congr rfl;intro k hk
      rw [input ⟨k,Finset.mem_range.mp hk⟩,widen_pack,pack,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro j _;ring
    _=pack wide n (dotAt l U n):=by
      rw [Finset.sum_comm,pack];apply Finset.sum_congr rfl;intro j _
      simp only [dotAt,Finset.sum_mul]
theorem bound_dotAt (l:ℕ)(U:Array ℕ)(n j:ℕ):dotAt l U n j≤n*((base-1)*(base-1)):=by
  have small(x k:ℕ):digit x k≤base-1:=by
    have h:=Nat.mod_lt (x/base^k) (by decide:0<base)
    change x/base^k%base≤base-1;omega
  apply (Finset.sum_le_sum (s:=Finset.range n) (fun k _=>Nat.mul_le_mul (small l k) (small (get U k) j))).trans
  simp
theorem reduced_row_digit (p n l:ℕ)(U w:Array ℕ)(j:Fin n)
    (small:0<p ∧ p≤base)(room:n*((base-1)*(base-1))<wide)
    (input:∀i:Fin n,get w i.val=widen n (get U i.val)):
    digit (recode wide base p n (combine l w n)) j.val=dotAt l U n j.val%p:=by
  change lane base _ _=_
  rw [recode_pack,lane_pack base (by decide) n _ (fun k _=>(Nat.mod_lt _ small.1).trans_le small.2) j.isLt,
    combine_pack _ _ _ _ input,lane_pack wide (by decide) n _ (fun k _=>(bound_dotAt l U n k).trans_lt room) j.isLt]
end RKCert.LU

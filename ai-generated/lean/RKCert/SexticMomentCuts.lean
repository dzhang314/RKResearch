module
public import RKCert.DirkQuinticFixed10
public import RKCert.DirkTrace
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.List.FinRange
public import Mathlib.RingTheory.Polynomial.ScaleRoots
@[expose] public section
namespace RKCert.Sextic
open Polynomial RKCert.FixedFactor RKCert.Paired RKCert.Endpoint
/-- The deweighted primitive rows clear denominators before specializing.
Factoring the common endpoint power makes the scalar predicate meaningful
even at residue zero, with no inversion in the coefficient ring. -/
def row {R:Type*} [CommRing R] (a:ℕ→R) (u:R) (k:ℕ) : R :=
  ∑ i:Fin 6, (2520/(k+i.val+1):ℕ)*a i.val*u^i.val

def minor {R:Type*} [CommRing R] (a:ℕ→R) (u:R):R :=
  row a u 1*row a u 3-(row a u 2)^2

def old {R:Type*} (v:Fin 6→R):List R := List.ofFn (fun i:Fin 5=>v i.castSucc)

def tuple {R:Type*} [CommRing R] (v:Fin 6→R):R := minor (coeffs (old v)) (v (Fin.last 5))

noncomputable def universal : MvPolynomial (Fin 6) ℤ := tuple MvPolynomial.X

theorem map_coeffs {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (l:List R) (i:ℕ):
    f (coeffs l i)=coeffs (l.map f) i := by
  induction l generalizing i with
  | nil => by_cases h:i=0 <;> simp [FixedFactor.coeffs,h]
  | cons x l ih => cases i <;> simp [FixedFactor.coeffs,ih]

theorem map_tuple {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (v:Fin 6→R):
    f (tuple v)=tuple (f ∘ v) := by
  have h:old (f ∘ v)=(old v).map f:=List.ofFn_comp' _ _
  simp [tuple,minor,row,h,map_coeffs]

theorem eval_universal {R:Type*} [CommRing R] (v:Fin 6→R) : zEval universal v=tuple v := by
  let f:=MvPolynomial.eval₂Hom (Int.castRingHom R) v
  change f (tuple MvPolynomial.X)=_
  rw [map_tuple];congr 1;funext i;simp [f]

theorem sorted_product {K:Type*} [Field K] {l t:List K} (p:l.Perm t) :
    linearProduct id l=linearProduct id t := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [linearProduct,ih]
  | swap a b l => simp only [linearProduct];ring
  | trans p q h g => exact h.trans g

theorem scale_product {K:Type*} [Field K] (c:K) (l:List K) :
    linearProduct id (l.map (c*·))=(linearProduct id l).scaleRoots c := by
  induction l with
  | nil=>simp [linearProduct]
  | cons x l ih=>
    simp only [List.map_cons,linearProduct,id_eq,mul_scaleRoots_of_noZeroDivisors,X_sub_C_scaleRoots,ih]
    rw [mul_comm x c]

theorem row_scale {K:Type*} [Field K] (P:K[X]) (c u:K) (k:ℕ) :
    row (P.scaleRoots c).coeff (c*u) k=c^P.natDegree*row P.coeff u k := by
  rw [row,row,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_scaleRoots,mul_pow]
  by_cases hi:i.val≤P.natDegree
  · have h:c^(P.natDegree-i.val)*c^i.val=c^P.natDegree:=by rw [←pow_add,Nat.sub_add_cancel hi]
    conv_rhs=>rw [←h]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < i.val)]
    ring

theorem tuple_scale {K:Type*} [Field K] (v:Fin 6→K) (c:K) :
    tuple (fun i=>c*v i)=c^10*tuple v := by
  have h:old (fun i=>c*v i)=(old v).map (c*·):=List.ofFn_comp' _ _
  have d:(linearProduct id (old v)).natDegree=5:=by rw [degree_product];simp [old]
  have cf (l:List K):FixedFactor.coeffs l=(linearProduct id l).coeff:=funext fun i=>(coeff_product l i).symm
  simp only [tuple,h,cf,scale_product,minor,row_scale,d]
  ring

theorem row_primitive {K:Type*} [Field K] [CharZero K] (P:K[X]) (d:P.natDegree≤5)
    (u:K) {k:ℕ} (lo:1≤k) (hi:k≤3) :
    (2520:K)*(primitive (X^k*P)).eval u=u^(k+1)*row P.coeff u k := by
  rw [←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul _ _ _ d,row,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have ix:=i.isLt
  have hn:0<k+i.val+1:=by omega
  have hh:k+i.val+1≤9:=by omega
  have dvd : k+i.val+1∣2520 :=by
    generalize k+i.val+1=n at hn hh ⊢
    interval_cases n <;> decide
  have clear:((2520/(k+i.val+1):ℕ):K)=2520/((k+i.val+1:ℕ):K) :=by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))).mpr
    exact_mod_cast Nat.div_mul_cancel dvd
  rw [clear,show k+i.val+1=k+1+i.val by omega,pow_add]
  ring

end RKCert.Sextic

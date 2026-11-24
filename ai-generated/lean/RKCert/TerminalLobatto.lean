module
public import RKCert.TerminalCardinal
public import RKCert.StagePrimitives
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- Signed on odd degrees to use the convention L_m(1)=1, since Mathlib
defines the shifted Legendre polynomial with P_m(0)=1. -/
def lobatto (m : ℕ) : Polynomial K :=
  C ((-1:K)^m) * (X * ((shiftedLegendre m).derivative.map (Int.castRingHom K)))

def lobattoCoeff (m j : ℕ) : K :=
  (-1:K)^m * ((j:K) * (((shiftedLegendre m).coeff j : ℤ):K))

omit [CharZero K] in
theorem lobatto_coeff (m j : ℕ) : (lobatto (K:=K) m).coeff j = lobattoCoeff m j := by
  cases j with
  | zero => rw [lobatto,coeff_C_mul,coeff_X_mul_zero]; simp [lobattoCoeff]
  | succ j =>
    rw [lobatto,coeff_C_mul,coeff_X_mul,coeff_map,coeff_derivative]
    simp [lobattoCoeff, mul_comm]

omit [CharZero K] in
theorem lobatto_degree {m:ℕ} (hm:0<m) : (lobatto (K:=K) m).natDegree≤m := by
  apply (natDegree_C_mul_le ..).trans
  apply (natDegree_mul_le ..).trans
  have hd := natDegree_map_le (f:=Int.castRingHom K) (p:=(shiftedLegendre m).derivative)
  rw [natDegree_derivative,natDegree_shiftedLegendre] at hd
  rw [natDegree_X]
  omega

omit [CharZero K] in
theorem lobatto_coeff_zero (m:ℕ) : lobattoCoeff (K:=K) m 0=0 := by simp [lobattoCoeff]

omit [CharZero K] in
/-- A finite supported moment certificate is enough to identify the *actual*
cardinal, output weight, and clean nonterminal clocks. -/
theorem lobatto_tableau (ho : HasTreeOrderAtLeast A b p) {m:ℕ} (hm : 2*m≤p) (hm' : 1≤m)
    (o t:Fin s) (h0 : nodes A o=0) (h1 : nodes A t=1)
    (clean0 : ∀f∈zeroSpace A m, f o=0) (clean1 : ∀f∈zeroSpace A m, f t=0)
    (hcard : Pi.single t (1:K)∈treeSpace A m)
    (moment : ∀k:Fin m, (∑ j:Fin (m+1), lobattoCoeff (K:=K) m j.val/((k.val+j.val+1:ℕ):K))=1)
    (atOne : (∑ j:Fin (m+1), lobattoCoeff (K:=K) m j.val)=((m*(m+1):ℕ):K)) :
    Pi.single t (1:K)-(b t) • evalNodes A (lobatto m)∈zeroSpace A m ∧
    b t*((m*(m+1):ℕ):K)=1 ∧
    ∀ i:Fin s, i≠t → (∀f∈zeroSpace A m,f i=0) → (lobatto m).eval (nodes A i)=0 := by
  have ⟨hid,hw⟩ := identify_cardinal ho hm hm' o t h0 h1 clean0 clean1 hcard
    (fun j => lobattoCoeff m j.val) (lobatto_coeff_zero m) moment
  have eqn : evalNodes A (lobatto m)=polyEval A m (fun j => lobattoCoeff m j.val) := by
    rw [evalNodes_eq_polyEval A _ (lobatto_degree (by omega))]
    simp only [lobatto_coeff]
  refine ⟨eqn ▸ hid,atOne ▸ hw,?_⟩
  intro i hit hc
  have hi := clean_grid t hid hw hit hc
  rw [← polyEval_node,← eqn] at hi
  exact hi

set_option maxHeartbeats 3000000 in
/-- Fixed-family scalar certificates needed by the four strongest even-order
DIRK reductions. Only Mathlib's native integer Legendre coefficients and
finite characteristic-zero field arithmetic are evaluated. -/
theorem lobatto_fixed {m:ℕ} (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10) :
    (∀ k:Fin m, (∑ j:Fin (m+1), lobattoCoeff (K:=K) m j.val/((k.val+j.val+1:ℕ):K))=1) ∧
    (∑ j:Fin (m+1), lobattoCoeff (K:=K) m j.val)=((m*(m+1):ℕ):K) := by
  rcases hm with rfl|rfl|rfl|rfl <;> constructor
  all_goals first
  | intro k; fin_cases k <;> norm_num [Fin.sum_univ_succ,lobattoCoeff,Polynomial.coeff_shiftedLegendre,Nat.choose]
  | norm_num [Fin.sum_univ_succ,lobattoCoeff,Polynomial.coeff_shiftedLegendre,Nat.choose]

end
end RKCert.Paired.Terminal

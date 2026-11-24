module
public import RKCert.FiveDebutTwoCuts
@[expose] public section
namespace RKCert.FiveDebut
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

/-- The three vanishing moments on four distinct nonzero physical clocks
force a single common barycentric amplitude scale. Subtract pairs of
monic cardinal numerators to stay within the exact two-degree budget. -/
theorem four_atoms_normalized {z w : Fin 4→K} (inj : Function.Injective z)
    (nz:∀i,z i≠0) (nw:∀i,w i≠0)
    (paid:∀ k:Fin 3,sumPower z (fun i=>z i^2/w i) k.val=0) :
    ∃ scale : K, scale≠0 ∧ ∀ i, w i=scale*z i^2*(Lagrange.nodal Finset.univ z).derivative.eval (z i) := by
  classical
  let a:=fun i : Fin 4=>z i^2/w i
  have s0:sumPower z a 0=0:=paid 0
  have s1:sumPower z a 1=0:=paid 1
  have s2:sumPower z a 2=0:=paid 2
  have small (P : K[X]) (dg:P.degree<(3:WithBot ℕ)) : (∑i,a i*P.eval (z i))=0 := by
    by_cases pt:P=0
    · simp [pt]
    have dn:P.natDegree<3 := (natDegree_lt_iff_degree_lt pt).mpr dg
    have ep (i):P.eval (z i)=P.coeff 0+P.coeff 1*z i+P.coeff 2*z i^2 := by
      rw [eval_eq_sum_range' (n:=3) dn,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero];simp
    calc
      _ = sumPower z a 0*P.coeff 0+sumPower z a 1*P.coeff 1+sumPower z a 2*P.coeff 2 := by
        simp only [sumPower,Finset.sum_mul,←Finset.sum_add_distrib,ep]
        apply Finset.sum_congr rfl;intro i _;ring
      _ = 0 := by rw [s0,s1,s2];ring
  let N (i:Fin 4) := Lagrange.nodal (Finset.univ.erase i) z
  have dN (i:Fin 4) : (N i).degree=3:=by simp [N]
  have mN (i:Fin 4) : (N i).Monic := Lagrange.nodal_monic
  have raw (i:Fin 4) : (∑k,a k*(N i).eval (z k))=a i*denomin z i := by
    rw [Finset.sum_eq_single i]
    · change _* (Lagrange.nodal _ z).eval (z i)=_
      rw [Lagrange.eval_nodal];rfl
    · intro k _ ki
      have van:(N i).eval (z k)=0:=Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨ki,Finset.mem_univ _⟩)
      rw [van,mul_zero]
    · simp
  have equal (i:Fin 4):a i*denomin z i = a 0*denomin z 0 := by
    have d:=degree_sub_lt_left ((dN i).trans (dN 0).symm) (mN i).ne_zero ((mN i).trans (mN 0).symm)
    have zero:=small (N i-N 0) (d.trans_le (dN i).le)
    simp only [eval_sub,mul_sub,Finset.sum_sub_distrib,raw,sub_eq_zero] at zero
    exact zero
  let v:=a 0*denomin z 0
  have vn:v≠0:=mul_ne_zero (div_ne_zero (pow_ne_zero _ (nz 0)) (nw 0)) (denom_ne_zero inj 0)
  refine ⟨v⁻¹,inv_ne_zero vn,fun i=>?_⟩
  rw [nodal_derivative]
  apply mul_left_cancel₀ vn
  rw [show v*(v⁻¹*z i^2*denomin z i)=z i^2*denomin z i by field_simp]
  rw [show v=a i*denomin z i from (equal i).symm]
  dsimp [a];field_simp [nw i]

end
end RKCert.FiveDebut

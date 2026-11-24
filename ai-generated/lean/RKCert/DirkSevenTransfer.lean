module
public import RKCert.DirkSevenPrime135
public import RKCert.DirkSevenPrime898
@[expose] public section
namespace RKCert.SevenPort
open Polynomial RKCert.FixedFactor
set_option maxRecDepth 5000
noncomputable section
def quadratic:ℤ[X]:=intHorner [150,-24,1]
def roots1009:List E:=[135,898]
theorem quadratic_degree:quadratic.natDegree=2:=by
  apply le_antisymm (degree_horner_le _ _ (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner [150,-24,1]).coeff 2≠0
  rw [coeff_horner];decide
theorem quadratic_monic:quadratic.Monic:=by rw [Monic,leadingCoeff,quadratic_degree,quadratic,coeff_horner];decide
theorem quadratic_split:quadratic.map (Int.castRingHom E)=linearProduct id roots1009:=by
  apply z_grid_split _ _ (by decide);intro i hi
  change i≤2 at hi;interval_cases i <;> decide +kernel
/-- Only one fixed integral algebraic parameter is specialized. The arbitrary
physical pivot and the arbitrary small factor are eliminated in the source
field, not mapped to a finite field. -/
theorem exceptional_resultant {K:Type*} [Field K] [CharZero K] (t:K)(root:t^2-24*t+150=0):res t≠0:=by
  have rt:(quadratic.map (Int.castRingHom K)).eval t=0:=by
    simp [quadratic,intHorner]
    linear_combination root
  have cert:=split_prime_root_tuple 1009 quadratic quadratic_monic roots1009 quadratic_split
    (fun z h=>quadratic_split ▸ simple_product_of_nodup roots1009 (by decide) h)
    witness (fun (_ _:Fin 1)=>False)
    (fun z non _=>by
      have inside:=non 0
      change z 0∈([135,898]:List E) at inside
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
      rw [eval_witness]
      rcases inside with one|two
      · rw [one];exact Branch135.good
      · rw [two];exact Branch898.good)
    (fun _:Fin 1=>t) (fun _=>rt) (fun _ _ no=>no.elim)
  simpa only [eval_witness] using cert
theorem no_common_minors {K:Type*} [Field K] [CharZero K] (t u:K)(root:t^2-24*t+150=0):
    ¬(d5 t u 0=0 ∧ d5 t u 1=0):=by
  rintro ⟨z₀,z₁⟩;apply exceptional_resultant t root
  exact padded_resultant_zero _ _ u (degree_minor _ _) (degree_minor _ _)
    ((eval_minor _ _ _).trans z₀) ((eval_minor _ _ _).trans z₁)
end
end RKCert.SevenPort

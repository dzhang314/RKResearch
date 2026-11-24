module

public import RKCert.CompanionRawNorm

@[expose] public section

/-! # Actual paid factor moments force the symbolic norm to vanish

The proof works on the quotient by the actual factor, so repeated roots
and repeated copies of an endpoint factor are retained. -/
namespace RKCert.Compound
open Polynomial Module Set Set.powersetCard RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem gramBlock_toMatrix {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V] (B : Basis I K V) (T S U : V→ₗ[K]V) :
    LinearMap.toMatrix (B.prod B) (B.prod B) (gramBlock T S U)=
      Matrix.fromBlocks (LinearMap.toMatrix B B T) (LinearMap.toMatrix B B S)
        (LinearMap.toMatrix B B S) (LinearMap.toMatrix B B U) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply,Basis.prod_apply,gramBlock_apply]

def normalizedFactorOperator (q : K[X]) (k M j w : ℕ) (u : K) :
    (⋀[K]^k (AdjoinRoot q)) →ₗ[K] (⋀[K]^k (AdjoinRoot q)) :=
  ((M:K)/u^(j+1)) • factorWeightedOperator q k u j w

theorem normalized_eigenline (F G : K[X]) (F0 : F≠0) (GM : G.Monic) (M w : ℕ) (u : K) :
    ∃ z : ⋀[K]^G.natDegree (AdjoinRoot (F*G)),z≠0 ∧
      ∀ j,normalizedFactorOperator (F*G) G.natDegree M j w u z=
        (((M:K)/u^(j+1))*paidMoment ((1-X)^w*G) u j) • z := by
  obtain ⟨z,nz,eigen⟩ := factor_weighted_eigenline F G F0 GM
  exact ⟨z,nz,fun j => by
    rw [normalizedFactorOperator,LinearMap.smul_apply,eigen,smul_smul]⟩

private theorem scaled_gram_zero (M j : ℕ) {u a b c : K}
    (h : a*c-b^2=0) :
    (((M:K)/u^(j+1))*a)*(((M:K)/u^(j+2+1))*c)-
      (((M:K)/u^(j+1+1))*b)^2=0 := by
  have eq : (u^(j+1):K)*u^(j+2+1)=(u^(j+1+1))^2 := by
    rw [←pow_add,←pow_mul]
    congr 1
    omega
  have scale : ((M:K)/u^(j+1))*((M:K)/u^(j+2+1))=(((M:K)/u^(j+1+1)))^2 := by
    rw [div_mul_div_comm,div_pow,eq,pow_two (M:K)]
  calc
   _ = (((M:K)/u^(j+1))*((M:K)/u^(j+2+1)))*(a*c)-
      (((M:K)/u^(j+1+1)))^2*b^2 := by ring
   _ = (((M:K)/u^(j+1+1)))^2*(a*c-b^2) := by rw [scale]; ring
   _ = 0 := by rw [h,mul_zero]

theorem rawMomentNorm_zero_of_factor (q : K[X]) (Q : q.Monic) (G : K[X])
    (g : G.Monic) (dvd : G∣q) (b : Fin (q.natDegree+1)→K)
    (below : ∀ i : Fin q.natDegree,b i.castSucc=b (Fin.last q.natDegree)*q.coeff i.val)
    (M j w : ℕ) (u : K) (un : u≠0)
    (den : ∀ i : Fin (G.natDegree+w+1),j+i.val+1∣M)
    (zero : paidMoment ((1-X)^w*G) u j=0) :
    rawMomentNorm G.natDegree M j w u b=0 := by
  obtain ⟨F,e⟩ := dvd
  rw [mul_comm] at e
  subst q
  have F0 : F≠0 := fun z=>Q.ne_zero (by rw [z,zero_mul])
  let : Module.Finite K (AdjoinRoot (F*G)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' Q).basis
  let B : Basis (powersetCard (Fin (F*G).natDegree) G.natDegree) K
      (⋀[K]^G.natDegree (AdjoinRoot (F*G))) :=
    (AdjoinRoot.powerBasis' Q).basis.exteriorPower G.natDegree
  let T := normalizedFactorOperator (F*G) G.natDegree M j w u
  let s (i : powersetCard (Fin (F*G).natDegree) G.natDegree) : K :=
    if hasLast i then b (Fin.last (F*G).natDegree) else 1
  obtain ⟨z,nz,eigen⟩ := normalized_eigenline F G F0 g M w u
  have det : LinearMap.det T=0 := by
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro h
    apply nz
    have cz : z∈LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      change normalizedFactorOperator (F*G) G.natDegree M j w u z=0
      rw [eigen j,zero,mul_zero,zero_smul]
    rwa [h,Submodule.mem_bot] at cz
  have eq : rawMomentMatrix (k:=G.natDegree) M j w u b =
      Matrix.of (fun i t => s t * LinearMap.toMatrix B B T i t) := by
    ext i t
    exact normalized_raw_entry (F*G) Q b below M j G.natDegree w u un i t den
  rw [rawMomentNorm,eq,Matrix.det_mul_row s (LinearMap.toMatrix B B T),
    LinearMap.det_toMatrix,det,mul_zero]

theorem rawGramNorm_zero_of_factor (q : K[X]) (Q : q.Monic) (G : K[X])
    (g : G.Monic) (dvd : G∣q) (b : Fin (q.natDegree+1)→K)
    (below : ∀ i : Fin q.natDegree,b i.castSucc=b (Fin.last q.natDegree)*q.coeff i.val)
    (M j w : ℕ) (u : K) (un : u≠0)
    (den : ∀ k≤2,∀ i : Fin (G.natDegree+w+1),j+k+i.val+1∣M)
    (zero : paidMoment ((1-X)^w*G) u j*paidMoment ((1-X)^w*G) u (j+2)-
      (paidMoment ((1-X)^w*G) u (j+1))^2=0) :
    rawGramNorm G.natDegree M j w u b=0 := by
  obtain ⟨F,e⟩ := dvd
  rw [mul_comm] at e
  subst q
  have F0 : F≠0 := fun z=>Q.ne_zero (by rw [z,zero_mul])
  let : Module.Finite K (AdjoinRoot (F*G)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' Q).basis
  let B : Basis (powersetCard (Fin (F*G).natDegree) G.natDegree) K
      (⋀[K]^G.natDegree (AdjoinRoot (F*G))) :=
    (AdjoinRoot.powerBasis' Q).basis.exteriorPower G.natDegree
  let T k := normalizedFactorOperator (F*G) G.natDegree M (j+k) w u
  let L := gramBlock (T 0) (T 1) (T 2)
  let s (i : powersetCard (Fin (F*G).natDegree) G.natDegree) : K :=
    if hasLast i then b (Fin.last (F*G).natDegree) else 1
  obtain ⟨z,nz,eigen⟩ := normalized_eigenline F G F0 g M w u
  have det : LinearMap.det L=0 := gramBlock_det_zero_of_line _ _ _ nz
    (eigen j) (eigen (j+1)) (eigen (j+2)) (scaled_gram_zero M j zero)
  have eq : rawGramMatrix (k:=G.natDegree) M j w u b =
      Matrix.of (fun i t => Sum.elim s s t * LinearMap.toMatrix (B.prod B) (B.prod B) L i t) := by
    ext i t
    change _=Sum.elim s s t*LinearMap.toMatrix (B.prod B) (B.prod B)
      (gramBlock (T 0) (T 1) (T 2)) i t
    rw [gramBlock_toMatrix]
    cases i <;> cases t
    · exact normalized_raw_entry (F*G) Q b below M j G.natDegree w u un _ _ (den 0 (by decide))
    · exact normalized_raw_entry (F*G) Q b below M (j+1) G.natDegree w u un _ _ (den 1 (by decide))
    · exact normalized_raw_entry (F*G) Q b below M (j+1) G.natDegree w u un _ _ (den 1 (by decide))
    · exact normalized_raw_entry (F*G) Q b below M (j+2) G.natDegree w u un _ _ (den 2 (by decide))
  rw [rawGramNorm,eq,Matrix.det_mul_row (Sum.elim s s) (LinearMap.toMatrix (B.prod B) (B.prod B) L),
    LinearMap.det_toMatrix,det,mul_zero]

end
end RKCert.Compound

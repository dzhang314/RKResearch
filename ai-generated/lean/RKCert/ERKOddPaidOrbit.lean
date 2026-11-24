module
public import RKCert.ERKOddClockMassTools
public import RKCert.ERKOddFourModes

@[expose] public section
/-! # Actual cutoff advances in the localized rank-two reverse band -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ v:Vec K 26}{U:Submodule K (Vec K 26)}
noncomputable section

theorem LocalLinearBand.moments_thirteen (B:LocalLinearBand A b 2 U τ)
    (P:K[X])(d:P.natDegree≤13):(∑i,τ i*P.eval (mirror A i))=0:=by
  have e:=mem_annih.mp B.paid _ (mirror_eval_in_tree (A:=A) P d)
  simpa only [row_apply] using e

theorem LocalLinearBand.low_orbitBand_paid (B:LocalLinearBand A b 2 U τ):
    orbitBand (mirror A) τ 7≤annih (treeSpace A 7):=by
  classical
  let : DecidableEq K:=Classical.decEq K
  rintro _ ⟨u,rfl⟩
  let P:K[X]:=ofFn 7 u
  have d:P.natDegree<7:=ofFn_natDegree_lt (by decide) _
  rw [LinearMap.comp_apply]
  change weightedEval (mirror A) τ P∈annih (treeSpace A 7)
  exact B.head_reflect_paid 7 P (by omega)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem peel_top (P:K[X]){q:ℕ}(d:P.natDegree≤q+1):
    ∃R:K[X],R.natDegree≤q∧P=R+C (P.coeff (q+1))*X^(q+1):=by
  refine ⟨P-C (P.coeff (q+1))*X^(q+1),?_,by ring⟩
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j dj
  rw [coeff_sub,C_mul_X_pow_eq_monomial,coeff_monomial]
  by_cases e:j=q+1
  · subst j;simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega:P.natDegree<j)]
    simp [e]

private theorem peel_at (P:K[X])(a:K){q:ℕ}(d:P.natDegree≤q+1):
    ∃R:K[X],R.natDegree≤q∧P-C (P.eval a)=(X-C a)*R:=by
  obtain ⟨R,e⟩:=X_sub_C_dvd_sub_C_eval (p:=P) (a:=a)
  refine ⟨R,?_,e⟩
  by_cases z:R=0
  · simp [z]
  have n:=natDegree_sub_le P (C (P.eval a))
  rw [e,natDegree_mul (X_sub_C_ne_zero _) z,natDegree_X_sub_C,natDegree_C] at n
  omega

theorem LocalLinearBand.polynomial_moments_fourteen (B:LocalLinearBand A b 2 U τ)
    (adv:weightedEval (mirror A) τ (X^7)∈annih (treeSpace A 7))
    (P:K[X])(d:P.natDegree≤14):(∑i,τ i*P.eval (mirror A i))=0:=by
  obtain ⟨R,dR,eq⟩:=peel_top P (q:=13) d
  have w:=mem_annih.mp adv _ (mirror_eval_in_tree (A:=A) ((X:K[X])^7)
    ((natDegree_X_pow _).le))
  simp only [row_apply,weightedEval_apply,eval_pow,eval_X] at w
  have q:(∑ i:Fin 26,τ i*(mirror A i)^14)=0:=by
    convert w using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  conv_lhs=>rw [eq]
  simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X,mul_add,Finset.sum_add_distrib]
  rw [B.moments_thirteen R dR,zero_add]
  calc
    _=P.coeff 14*(∑i:Fin 26,τ i*(mirror A i)^14):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=0:=by rw [q,mul_zero]

theorem LocalLinearBand.polynomial_orbit_at_eight (B:LocalLinearBand A b 2 U τ)
    (adv:weightedEval (mirror A) τ (X^7)∈annih (treeSpace A 7))
    (eight:(orbitSites (mirror A) τ).card=8):
    nodalOrbit (mirror A) τ≤annih (treeSpace A 7):=by
  classical
  let : DecidableEq K:=Classical.decEq K
  have e:orbitBand (mirror A) τ 8=nodalOrbit (mirror A) τ:=by
    apply Submodule.eq_of_le_of_finrank_le (orbitBand_le _ _ _)
    rw [nodalOrbit_rank,eight,orbitBand_rank _ _ _ eight.ge]
  rw [←e]
  rintro _ ⟨u,rfl⟩
  let P:K[X]:=ofFn 8 u
  have d:P.natDegree<8:=ofFn_natDegree_lt (by decide) _
  obtain ⟨R,dR,q⟩:=peel_top P (q:=6) (by omega)
  have F:weightedEval (mirror A) τ (C (P.coeff 7)*X^7)∈annih (treeSpace A 7):=by
    rw [←smul_eq_C_mul,map_smul]
    exact (annih _).smul_mem _ adv
  rw [LinearMap.comp_apply]
  change weightedEval (mirror A) τ P∈annih (treeSpace A 7)
  rw [q,map_add]
  exact (annih _).add_mem (B.head_reflect_paid 7 R (by omega)) (by
    exact F)

def rationalHead (y d:Vec K 26)(a:K):Vec K 26:=fun i=>d i/(y i-a)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem TrueRationalAdvance.head_sites {a:K}(D:TrueRationalAdvance A τ a):
    orbitSites (mirror A) (rationalHead (mirror A) τ a)=orbitSites (mirror A) τ:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  have e:activeRows (rationalHead (mirror A) τ a)=activeRows τ:=by
    ext i
    rw [mem_activeRows,mem_activeRows]
    exact same_active_div_clock (mirror A) τ a D.omitted i
  change (activeRows (rationalHead (mirror A) τ a)).image _=(activeRows τ).image _
  rw [e]

theorem TrueRationalAdvance.head_orthogonal {a:K}(_D:TrueRationalAdvance A τ a)
    (B:LocalLinearBand A b 2 U τ):
    rationalHead (mirror A) τ a∈annih U:=by
  let y:=mirror A
  have h:=joint_selector_mem (diag_annih_invariant B.clock) (diag_annih_invariant B.clock)
    B.orthogonal (fun p _=>(p-a)⁻¹)
  have e:rationalHead y τ a=(fun i=>(y i-a)⁻¹*τ i):=by
    ext i
    simp only [rationalHead,div_eq_mul_inv,mul_comm]
  rw [e]
  exact h

private theorem rational_weighted_decomposition {a:K}
    (D:TrueRationalAdvance A τ a)(P R:K[X])
    (eq:P-C (P.eval a)=(X-C a)*R):
    weightedEval (mirror A) (rationalHead (mirror A) τ a) P =
      P.eval a•rationalHead (mirror A) τ a+weightedEval (mirror A) τ R:=by
  ext i
  have e:=congrArg (eval (mirror A i)) eq
  simp only [eval_sub,eval_C,eval_mul,eval_X] at e
  simp only [weightedEval_apply,rationalHead,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  by_cases cut:mirror A i=a
  · rw [D.omitted i cut,zero_div,mul_zero,mul_zero,mul_zero,add_zero]
  field_simp [sub_ne_zero.mpr cut]
  linear_combination τ i*e

theorem TrueRationalAdvance.moments_fourteen {a:K}(D:TrueRationalAdvance A τ a)
    (B:LocalLinearBand A b 2 U τ)
    (P:K[X])(d:P.natDegree≤14):
    (∑i,rationalHead (mirror A) τ a i*P.eval (mirror A i))=0:=by
  let y:=mirror A
  let v:=rationalHead y τ a
  obtain ⟨R,dR,eq⟩:=peel_at P a (q:=13) d
  have v0:(∑i,rationalHead (mirror A) τ a i)=0:=by
    change (∑i,τ i/(mirror A i-a))=0
    have e:=mem_annih.mp D.paid (1:Vec K 26) (stageWeight_mem_space A .leaf (by decide))
    simpa only [row_apply,Pi.one_apply,mul_one] using e
  have q:=rational_weighted_decomposition D _ _ eq
  have e:(∑i,v i*P.eval (y i))=∑i,weightedEval y v P i:=by
    simp only [weightedEval_apply,mul_comm]
  rw [e,q]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum,
    v0,mul_zero,zero_add]
  simpa only [weightedEval_apply,mul_comm] using B.moments_thirteen R dR

theorem TrueRationalAdvance.orbit_at_eight {a:K}(D:TrueRationalAdvance A τ a)
    (B:LocalLinearBand A b 2 U τ)
    (eight:(orbitSites (mirror A) τ).card=8):
    nodalOrbit (mirror A) (rationalHead (mirror A) τ a)≤annih (treeSpace A 7):=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  let v:=rationalHead y τ a
  have count:(orbitSites y v).card=8:=by rw [show orbitSites y v=orbitSites y τ from D.head_sites];exact eight
  have eq:orbitBand y v 8=nodalOrbit y v:=by
    apply Submodule.eq_of_le_of_finrank_le (orbitBand_le _ _ _)
    rw [nodalOrbit_rank,count,orbitBand_rank _ _ _ count.ge]
  change nodalOrbit y v≤_
  rw [←eq]
  rintro _ ⟨u,rfl⟩
  let P:K[X]:=ofFn 8 u
  have d:P.natDegree<8:=ofFn_natDegree_lt (by decide) _
  obtain ⟨R,dR,h⟩:=peel_at P a (q:=6) (by omega)
  rw [LinearMap.comp_apply]
  change weightedEval (mirror A) (rationalHead (mirror A) τ a) P∈annih (treeSpace A 7)
  rw [rational_weighted_decomposition D _ _ h]
  exact (annih _).add_mem ((annih _).smul_mem _ D.paid) (B.head_reflect_paid 7 R (by omega))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem TrueRationalAdvance.transfer_zero_mass {a:K}(D:TrueRationalAdvance A τ a)
    (zero:∀z∈orbitSites (mirror A) (rationalHead (mirror A) τ a),
      clockMass (mirror A) (rationalHead (mirror A) τ a) z=0):
    ∀z∈headSites (mirror A) τ,clockMass (mirror A) τ z=0:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  intro z hz
  let y:=mirror A
  let v:=rationalHead y τ a
  have z0:clockMass y v z=0:=zero z (D.head_sites.symm ▸ hz)
  have e:clockMass y τ z=(z-a)*clockMass y v z:=by
    rw [clockMass_apply,clockMass_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have p:y i=z:=(Finset.mem_filter.mp hi).2
    by_cases n:z=a
    · have h:=D.omitted i (p.trans n)
      simp [n,h]
    change τ i=(z-a)*(τ i/(y i-a))
    rw [p]
    field_simp [sub_ne_zero.mpr n]
  rw [e,z0,mul_zero]

theorem LocalLinearBand.no_paid_large_orbit (B:LocalLinearBand A b 2 U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (rich:7≤finrank K (zeroSpace A 6))
    (n:8≤(orbitSites (mirror A) v).card)(orth:v∈annih U)
    (pay:nodalOrbit (mirror A) v≤annih (treeSpace A 7)):False:=by
  let y:=mirror A
  let V:=nodalOrbit y v
  have vo:V≤annih U:=by
    change nodalOrbit y v≤_
    rw [nodalOrbit_eq_weightedEval]
    rintro _ ⟨P,rfl⟩
    exact weightedEval_orthogonal B.clock orth P
  have inter:U⊓V=⊥:=by
    apply le_bot_iff.mp
    rintro w ⟨u,h⟩
    exact dot_orthogonal_inter_zero u (vo h)
  have d:=Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [inter,finrank_bot,add_zero,B.dimension,show finrank K V=(orbitSites y v).card from nodalOrbit_rank _ _] at d
  have inv:((U⊔V:Submodule K (Vec K 26)).map (diag y))≤U⊔V:=by
    rw [Submodule.map_sup]
    refine sup_le (B.clock.trans le_sup_left) (le_trans ?_ le_sup_right)
    rintro _ ⟨w,hw,rfl⟩
    exact mulByBlock_mem y (nodalOrbit_mask y v) (fun a=>a) hw
  have cap:=odd17_invariant_reverse_eight_cap ha ho S rich (U⊔V)
    (sup_le ((B.base_annih ho).trans (annih_antitone_paired (treeSpace_mono A (by decide:7≤16-2)))) pay) inv
  change 8≤(orbitSites y v).card at n
  omega
end
end RKCert.Paired.ReverseHull

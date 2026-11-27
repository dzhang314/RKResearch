module

public import RKCert.ReviewedNative.SDIRKOrderEightSingletonZero
public import RKCert.ReviewedNative.NonsingularDefectDescent
public import RKCert.ReviewedNative.GradedProducts
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual ten-stage order-eight saturation with one quadratic zero

The quadratic column below is twice the usual quadratic stage residual.
No zero-weight or repeated-clock restrictions and no ordering are used.
-/

namespace RKResearch.Certified.Graded.OrderEightSingletonZero

open FiniteRootedTree Module
open scoped BigOperators Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- Only the forward Volterra ranks needed for the two scalar packets. -/
private theorem census (ho : HasOrder 8 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ j, A j j ≠ 0) :
    finrank K (treeSpace A 0)=1 ∧ finrank K (treeSpace A 2)=4 ∧
    finrank K (treeSpace A 3)=6 ∧ finrank K (treeSpace A 4)=8 ∧
    finrank K (treeSpace A 5)=9 := by
  have top (j : ℕ) : finrank K (treeSpace A j) ≤ 10 := by
    simpa only [Module.finrank_fin_fun,Fintype.card_fin] using (Submodule.finrank_le (treeSpace A j))
  have lower (j : ℕ) (h : j+1≤8) := parityCensus_le_finrank ho ha hn j h
  have h02 := nonsingular_rank_step ho ha hn 0 2 (by decide) (by decide)
  have h24 := nonsingular_rank_step ho ha hn 2 3 (by decide) (by decide)
  have h46 := nonsingular_rank_step ho ha hn 4 1 (by decide) (by decide)
  have h35 := nonsingular_rank_step ho ha hn 3 2 (by decide) (by decide)
  have h57 := nonsingular_rank_step ho ha hn 5 0 (by decide) (by decide)
  change 2+1+finrank K (treeSpace A 0) ≤ finrank K (treeSpace A 2) at h02
  change 3+1+finrank K (treeSpace A 2) ≤ finrank K (treeSpace A 4) at h24
  change 1+1+finrank K (treeSpace A 4) ≤ finrank K (treeSpace A 6) at h46
  change 2+1+finrank K (treeSpace A 3) ≤ finrank K (treeSpace A 5) at h35
  change 0+1+finrank K (treeSpace A 5) ≤ finrank K (treeSpace A 7) at h57
  have t6 := top 6
  have t7 := top 7
  have lo0 : 1 ≤ finrank K (treeSpace A 0) := lower 0 (by decide)
  have lo2 : 4 ≤ finrank K (treeSpace A 2) := lower 2 (by decide)
  have lo3 : 6 ≤ finrank K (treeSpace A 3) := lower 3 (by decide)
  have lo4 : 8 ≤ finrank K (treeSpace A 4) := lower 4 (by decide)
  have lo5 : 9 ≤ finrank K (treeSpace A 5) := lower 5 (by decide)
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

private theorem volterra_one : volterra A 1 = -monomialStageDefect A 1 := by
  have hc : diag (nodes A) 1 = nodes A := by ext j; simp
  have ha : mat A 1 = nodes A := rfl
  simp only [volterra,LinearMap.sub_apply,LinearMap.comp_apply,ha,hc]
  ext j
  change nodes A j * nodes A j - mat A (nodes A) j - mat A (nodes A) j =
    -(((1+1:ℕ):K)*mat A (fun l => nodes A l^1) j-(nodes A j)^(1+1))
  norm_num
  ring

private theorem low_defect_read (i : Fin 10) (hg : monomialStageDefect A 1 i = 0)
    (pkt : ExactVolterraPacket A 0 2)
    (r0 : finrank K (treeSpace A 0)=1)
    {v : Fin 10 → K} (hv : v ∈ zeroSpace A 2) : v i = 0 := by
  let L := Submodule.span K {(1 : Fin 10 → K)}
  have rankL : finrank K L=1 := finrank_span_singleton one_ne_zero
  have h1 : (1 : Fin 10 → K) ∈ treeSpace A 0 := by
    simpa only [Φ] using Φ_mem_treeSpace A .leaf (j:=0) (by decide)
  have leL : L ≤ treeSpace A 0 := Submodule.span_le.mpr (by simpa using h1)
  have eq : L = treeSpace A 0 :=
    Submodule.eq_of_le_of_finrank_eq leL (rankL.trans r0.symm)
  rw [pkt.defect,←eq] at hv
  obtain ⟨x,hx,rfl⟩ := hv
  obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul,volterra_one]
  simp [hg]

private theorem range_does_not_surpass_defects (ho : HasOrder 8 A b) (j : ℕ) (hj : j+1≤8) :
    (treeSpace A j).map (diag (monomialStageDefect A 1)) ≤ zeroSpace A (j+2) := by
  rintro _ ⟨v,hv,rfl⟩
  change monomialStageDefect A 1 * v ∈ zeroSpace A (j+2)
  rw [Nat.add_comm j]
  exact zeroSpace_mul_treeSpace ho hj (monomialStageDefect_mem A 1) hv

private theorem image_finrank_of_restricted_inj (U : Submodule K (Fin 10 → K))
    (L : (Fin 10 → K) →ₗ[K] (Fin 10 → K))
    (h : Function.Injective (L.comp U.subtype)) :
    finrank K (U.map L)=finrank K U := by
  have eq : U.map L=(L.comp U.subtype).range := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨⟨v,hv⟩,rfl⟩
    · rintro ⟨v,rfl⟩
      exact ⟨v,v.property,rfl⟩
  rw [eq,LinearMap.finrank_range_of_inj h]

private theorem defect_rank (j q : ℕ)
    (ha : A.IsLowerTriangular) (hn : ∀ k, A k k ≠ 0)
    (pkt : ExactVolterraPacket A j q) :
    finrank K (zeroSpace A (j+2))=finrank K (treeSpace A j) := by
  rw [pkt.defect]
  apply image_finrank_of_restricted_inj
  exact (volterra_injective ha hn).comp Subtype.val_injective

private theorem support_of_zero_mul (i : Fin 10)
    (hne : ∀ j, j≠i → monomialStageDefect A 1 j ≠ 0)
    {v : Fin 10 → K} (hv : diag (monomialStageDefect A 1) v=0) :
    ∀ j, j≠i → v j=0 := by
  intro j hj
  have h := congrFun hv j
  rw [diag_apply,Pi.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left (hne j hj)

private def pad (r : Fin 3 → K) : Fin 4 → K := ![r 0,r 1,r 2,0]

private theorem pad_coeffEval (r : Fin 3 → K) : coeffEval A 3 (pad r)=coeffEval A 2 r := by
  ext j
  simp only [coeffEval_apply,normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp [Fin.sum_univ_succ,pad]

variable [CharZero K]

private theorem rank4_clean (ho : HasOrder 8 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ j, A j j≠0) (i : Fin 10)
    (hzero : monomialStageDefect A 1 i=0)
    (hne : ∀ j, j≠i → monomialStageDefect A 1 j≠0)
    (p02 : ExactVolterraPacket A 0 2) (p24 : ExactVolterraPacket A 2 3)
    (r0 : finrank K (treeSpace A 0)=1) :
    ∀ v ∈ zeroSpace A 4, v i=0 := by
  let G := diag (monomialStageDefect A 1)
  let E := treeSpace A 2
  have inj : Function.Injective (G.comp E.subtype) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have supp := support_of_zero_mul i hne (show G (v : Fin 10 → K)=0 from hv)
    obtain ⟨x,⟨r,rfl⟩,d,hd,e⟩ := Submodule.mem_sup.mp
      (show (v : Fin 10 → K) ∈ (coeffEval A 2).range⊔zeroSpace A 2 from
        (treeSpace_coeff_sup ho (q:=2) (by decide)) ▸ v.property)
    have e3 : coeffEval A 3 (pad r) + d = (v : Fin 10 → K) := by
      rw [pad_coeffEval,e]
    have shape := shape_of_supported_packet ho i (pad r) d (zeroSpace_mono A (by decide : 2≤3) hd)
      (fun j hj => by rw [e3]; exact supp j hj)
    have zero : pad r=0 := by
      ext j
      simp [shape.1 j,show pad r 3=0 from rfl]
    apply Subtype.ext
    ext j
    by_cases hj : j=i
    · subst j
      rw [←e3,zero,map_zero,zero_add,low_defect_read i hzero p02 r0 hd]
      rfl
    · exact supp j hj
  have inclusion : E.map G ≤ zeroSpace A 4 := range_does_not_surpass_defects ho 2 (by decide)
  have eq : E.map G = zeroSpace A 4 := Submodule.eq_of_le_of_finrank_eq inclusion
    ((image_finrank_of_restricted_inj E G inj).trans (defect_rank 2 3 ha hn p24).symm)
  intro v hv
  rw [←eq] at hv
  obtain ⟨u,_,rfl⟩ := hv
  exact show G u i=0 by simp [G,hzero]

private def L3coeff (K : Type*) [Field K] : Fin 4 → K := ![-1/20,3/5,-3/2,1]
private def L4coeff (K : Type*) [Field K] : Fin 5 → K := ![1/70,-2/7,9/7,-2,1]

private theorem L3_paid (ho : HasOrder 8 A b) (k : Fin 3) :
    probe A b k.val (coeffEval A 3 (L3coeff K))=0 := by
  have hk := k.isLt
  rw [probe_coeffEval ho (by omega)]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,L3coeff]

private theorem L4_paid (ho : HasOrder 8 A b) (k : Fin 3) :
    probe A b k.val (coeffEval A 4 (L4coeff K))=0 := by
  have hk := k.isLt
  rw [probe_coeffEval ho (by omega)]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,L4coeff]

private theorem two_legendre_not_both_zero (i : Fin 10) :
    ¬ (coeffEval A 3 (L3coeff K) i=0 ∧ coeffEval A 4 (L4coeff K) i=0) := by
  rintro ⟨e,f⟩
  simp only [coeffEval_apply,normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at e f
  norm_num [Fin.sum_univ_succ,L3coeff,L4coeff] at e f
  set x := nodes A i
  have h : (1 : K)=0 := by
    linear_combination (2800*x^3-4200*x^2+(5200/3)*x-500/3)*e +
      (-2800*x^2+2800*x-1540/3)*f
  exact one_ne_zero h

omit [CharZero K] in
private theorem belong_defect5_of_three_probes (ho : HasOrder 8 A b)
    (pkt : ExactVolterraPacket A 3 2) {v : Fin 10 → K}
    (hv : v∈treeSpace A 5) (obs : ∀ k : Fin 3, probe A b k.val v=0) :
    v∈zeroSpace A 5 := by
  rw [pkt.split] at hv
  obtain ⟨_,⟨r,rfl⟩,d,hd,rfl⟩ := Submodule.mem_sup.mp hv
  have hdf : d∈zeroSpace A 5 := pkt.defect.symm ▸ hd
  have hr := paid_coeffEval_eq_zero ho (q:=2) (by decide) r (fun k => by
    have z : probe A b k.val d=0 := probe_zeroSpace ho
      (by have := k.isLt; omega) hdf
    simpa only [map_add,z,add_zero] using obs k)
  simpa [hr] using hdf

private theorem support_packet (ho : HasOrder 8 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ j, A j j≠0) (i : Fin 10)
    (hzero : monomialStageDefect A 1 i=0)
    (hne : ∀ j, j≠i → monomialStageDefect A 1 j≠0)
    (pkt : ExactVolterraPacket A 3 2) :
    ∃ r d, d∈zeroSpace A 3 ∧ (∀ j, j≠i → (coeffEval A 3 r+d) j=0) ∧
      (coeffEval A 3 r+d) i≠0 := by
  let G := diag (monomialStageDefect A 1)
  let E := treeSpace A 3
  have l3 := belong_defect5_of_three_probes ho pkt
    (treeSpace_mono A (by decide : 3≤5) (coeffEval_mem_treeSpace A 3 (L3coeff K)))
    (L3_paid ho)
  have l4 := belong_defect5_of_three_probes ho pkt
    (treeSpace_mono A (by decide : 4≤5) (coeffEval_mem_treeSpace A 4 (L4coeff K)))
    (L4_paid ho)
  have noninj : ¬ Function.Injective (G.comp E.subtype) := by
    intro hinj
    have inclusion : E.map G ≤ zeroSpace A 5 := range_does_not_surpass_defects ho 3 (by decide)
    have eq : E.map G = zeroSpace A 5 := Submodule.eq_of_le_of_finrank_eq inclusion
      ((image_finrank_of_restricted_inj E G hinj).trans (defect_rank 3 2 ha hn pkt).symm)
    have allzero (x : Fin 10 → K) (hx : x∈zeroSpace A 5) : x i=0 := by
      rw [←eq] at hx
      obtain ⟨u,_,rfl⟩ := hx
      exact show G u i=0 by simp [G,hzero]
    exact two_legendre_not_both_zero i ⟨allzero _ l3,allzero _ l4⟩
  have ex : ∃ v : E, (G.comp E.subtype) v=0 ∧ v≠0 := by
    by_contra! h
    exact noninj ((injective_iff_map_eq_zero _).mpr h)
  obtain ⟨v,hG,hv⟩ := ex
  have supp := support_of_zero_mul i hne (show G (v : Fin 10 → K)=0 from hG)
  have vi : (v : Fin 10 → K) i ≠0 := by
    intro h
    apply hv
    apply Subtype.ext
    ext j
    by_cases hj : j=i
    · subst j; exact h
    · exact supp j hj
  obtain ⟨_,⟨r,rfl⟩,d,hd,e⟩ := Submodule.mem_sup.mp
    (show (v : Fin 10 → K)∈(coeffEval A 3).range⊔zeroSpace A 3 from
      (treeSpace_coeff_sup ho (q:=3) (by decide)) ▸ v.property)
  exact ⟨r,d,hd,(fun j hj => by rw [e]; exact supp j hj),by rwa [e]⟩

/-- Every actual ten-stage nonsingular DIRK tableau of order eight
with precisely one zero quadratic residual has a Gauss clock there.
Its physical diagonal is half the associated weight. No common-diagonal
hypothesis is needed for this local assertion. -/
theorem order_eight_singleton_zero_stage_pin (ho : HasOrder 8 A b)
    (ha : A.IsLowerTriangular) (hn : ∀ j, A j j≠0) (i : Fin 10)
    (hzero : monomialStageDefect A 1 i=0)
    (hne : ∀ j, j≠i → monomialStageDefect A 1 j≠0) :
    legendreFour (nodes A i)=0 ∧ A i i=halfMass (nodes A i) ∧
    b i=2*A i i ∧ (144*A i i-18)^2=30 := by
  obtain ⟨r0,r2,r3,r4,r5⟩ := census ho ha hn
  have p02 : ExactVolterraPacket A 0 2 := exact_volterra_packet ho ha hn
    (by decide) (by decide) (by change finrank K (treeSpace A 2) = 2+1+finrank K (treeSpace A 0); omega)
  have p24 : ExactVolterraPacket A 2 3 := exact_volterra_packet ho ha hn
    (by decide) (by decide) (by change finrank K (treeSpace A 4) = 3+1+finrank K (treeSpace A 2); omega)
  have p35 : ExactVolterraPacket A 3 2 := exact_volterra_packet ho ha hn
    (by decide) (by decide) (by change finrank K (treeSpace A 5) = 2+1+finrank K (treeSpace A 3); omega)
  obtain ⟨r,d,hd,hs,hv⟩ := support_packet ho ha hn i hzero hne p35
  exact stage_pin_from_supported_packet ho i r d hd
    (rank4_clean ho ha hn i hzero hne p02 p24 r0) hs hv

/-- A ten-stage rational nonsingular order-eight tableau has either
no quadratic zero or at least two of them. -/
theorem no_singleton_zero_rational {A : Matrix (Fin 10) (Fin 10) ℚ} {b : Fin 10 → ℚ}
    (ho : HasOrder 8 A b) (ha : A.IsLowerTriangular) (hn : ∀ j, A j j ≠ 0)
    (i : Fin 10) (hzero : monomialStageDefect A 1 i=0)
    (hne : ∀ j, j≠i → monomialStageDefect A 1 j≠0) : False := by
  have square : IsSquare (30 : ℚ) := ⟨144*A i i-18,
    by simpa only [pow_two] using
      (order_eight_singleton_zero_stage_pin ho ha hn i hzero hne).2.2.2.symm⟩
  have integral : IsSquare (30 : ℕ) := Rat.isSquare_natCast_iff.mp square
  obtain ⟨r,hr⟩ := integral
  by_cases small : r≤5
  · have h := Nat.mul_le_mul small small
    omega
  · have h₆ : 6≤r := by omega
    have h := Nat.mul_le_mul h₆ h₆
    omega

omit [CharZero K] in
/-- An eleven-stage nonsingular order-eight witness cannot in fact
have order nine. This supplies exactness for the archived upper. -/
theorem no_order_nine_fin11 {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}
    (ha : A.IsLowerTriangular) (hn : ∀ j, A j j ≠ 0) : ¬HasOrder 9 A b := by
  intro ho
  have h : 13≤11 := nonsingular_stageFloor_field ho ha hn (by decide)
  omega

end RKResearch.Certified.Graded.OrderEightSingletonZero

module

public import RKCert.ReviewedNative.ERK8CharElevenHighHull
public import RKCert.ReviewedNative.ERK8PaidPhysicalBridge

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Leading-coefficient transfer between two paid four-node hulls
A single degree-two fitted defect relates the original off hull to the
clean terminal hull. No root splitting of that defect is required. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch LobattoEight ERK8CharEleven OneOff ERKTaggedHorizon FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape (CleanTerminalProfile lastPhysical)
open scoped Classical BigOperators Matrix

variable {K : Type*} [Field K]

noncomputable def nodalCofactor (S : Finset K) (x : K) : K := (nodalHull (S.erase x)).eval x

noncomputable def nodalMeasure (P : K[X]) (S : Finset K) (G : K[X]) : K :=
  ∑ x∈S, (G.eval x/P.eval x)/nodalCofactor S x

theorem nodalMeasure_add (P : K[X]) (S : Finset K) (G H : K[X]) :
    nodalMeasure P S (G+H)=nodalMeasure P S G+nodalMeasure P S H := by
  rw [nodalMeasure,nodalMeasure,nodalMeasure,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => by simp only [eval_add,add_div])

theorem nodalMeasure_sub (P : K[X]) (S : Finset K) (G H : K[X]) :
    nodalMeasure P S (G-H)=nodalMeasure P S G-nodalMeasure P S H := by
  rw [nodalMeasure,nodalMeasure,nodalMeasure,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun x _ => by simp only [eval_sub,sub_div])

theorem nodalMeasure_Cmul (P : K[X]) (S : Finset K) (a : K) (G : K[X]) :
    nodalMeasure P S (C a*G)=a*nodalMeasure P S G := by
  rw [nodalMeasure,nodalMeasure,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by simp only [eval_mul,eval_C,mul_div_assoc])

theorem nodalCofactor_ne_of_mem {S : Finset K} {x : K} (_hx : x∈S) : nodalCofactor S x≠0 := by
  simp only [nodalCofactor,nodalHull,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_ne_zero_iff]
  intro y hy
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm

theorem nodalHull_dvd_of_evals_zero {S : Finset K} {P : K[X]} (on : ∀ x∈S,P.eval x=0) :
    nodalHull S ∣ P := by
  unfold nodalHull
  apply Finset.prod_dvd_of_coprime
  · intro x _ y _ ne
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit
  · intro x hx
    exact dvd_iff_isRoot.mpr (on x hx)

theorem coprime_nodalHull_of_eval_ne {S : Finset K} {P : K[X]} (on : ∀ x∈S,P.eval x≠0) :
    IsCoprime P (nodalHull S) := by
  unfold nodalHull
  apply IsCoprime.prod_right
  intro x hx
  obtain ⟨U,hU⟩ := dvd_iff_isRoot.mpr (show (P-C (P.eval x)).eval x=0 by simp)
  let a := P.eval x
  have inv : (C a⁻¹ : K[X])*C a=1 := by rw [←map_mul,inv_mul_cancel₀ (on x hx),map_one]
  refine ⟨C a⁻¹,-C a⁻¹*U,?_⟩
  change C a⁻¹*P+(-C a⁻¹*U)*(X-C x)=1
  change P-C a=(X-C x)*U at hU
  linear_combination C a⁻¹*hU+inv

noncomputable def nodalDivide (P : K[X]) (S : Finset K) (G : K[X]) : K[X] :=
  Lagrange.interpolate S id (fun x=>G.eval x/P.eval x)

theorem nodalDivide_degree (P : K[X]) (S : Finset K) (G : K[X]) {n : ℕ} (cn : S.card=n+1) :
    (nodalDivide P S G).natDegree≤n := by
  by_cases z : nodalDivide P S G=0
  · simp [z]
  have d := (natDegree_lt_iff_degree_lt z).mpr (Lagrange.degree_interpolate_lt
    (fun x=>G.eval x/P.eval x) (Set.injOn_id _) (s:=S))
  change _ < S.card at d
  omega

theorem nodalDivide_eval (P : K[X]) (S : Finset K) (G : K[X]) {x : K} (hx : x∈S) :
    (nodalDivide P S G).eval x=G.eval x/P.eval x :=
  Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hx

theorem nodalMeasure_top (P : K[X]) (S : Finset K) (G : K[X]) {n : ℕ} (cn : S.card=n+1) :
    nodalMeasure P S G=(nodalDivide P S G).coeff n := by
  have h := coeff_last_barycentric S (nodalDivide P S G)
    ((nodalDivide_degree P S G cn).trans_lt (by omega))
  rw [cn,Nat.add_sub_cancel] at h
  rw [h,nodalMeasure]
  apply Finset.sum_congr rfl
  intro x hx
  rw [nodalDivide_eval P S G hx]
  rfl

theorem nodalMeasure_erase (P : K[X]) {S : Finset K} {e : K} (en : e∉S) (G : K[X]) :
    nodalMeasure P S G=nodalMeasure P (insert e S) ((X-C e)*G) := by
  have cf (x : K) (hx : x∈S) : nodalCofactor (insert e S) x=(x-e)*nodalCofactor S x := by
    have ne : x≠e := fun u=>en (u ▸ hx)
    have cuts : (insert e S).erase x=insert e (S.erase x) := by
      ext y
      by_cases ye : y=e
      · simp [ye,ne.symm]
      · simp only [Finset.mem_erase,Finset.mem_insert,ye,false_or]
    rw [nodalCofactor,cuts]
    have eq : nodalHull (insert e (S.erase x))=(X-C e)*nodalHull (S.erase x) :=
      Finset.prod_insert (fun m=>en (Finset.mem_of_mem_erase m))
    rw [eq,eval_mul,eval_sub,eval_X,eval_C]
    rfl
  simp only [nodalMeasure,Finset.sum_insert en,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,
    zero_div,zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [cf x hx,mul_div_assoc,mul_div_mul_left _ _ (sub_ne_zero.mpr (fun (u : x=e)=>en (u ▸ hx)))]

theorem nodalMeasure_erase_pow (P : K[X]) {S : Finset K} {e : K} (en : e∉S) (r : ℕ) :
    nodalMeasure P S (X^r)=
      nodalMeasure P (insert e S) (X^(r+1))-e*nodalMeasure P (insert e S) (X^r) := by
  rw [nodalMeasure_erase P en]
  rw [sub_mul,pow_succ',nodalMeasure_sub,nodalMeasure_Cmul]

theorem measure_quotient_four {P G : K[X]} (p2 : P.natDegree=2) (Gd : G.natDegree≤4)
    {S : Finset K} (Sc : S.card=4) (n : ∀ x∈S,P.eval x≠0) :
    ∃ V : K[X], V.natDegree≤1 ∧
      P*nodalDivide P S G-G=nodalHull S*V ∧
      V.coeff 1=P.coeff 2*nodalMeasure P S G := by
  let U := nodalDivide P S G
  let D := nodalHull S
  have ud : U.natDegree≤3 := nodalDivide_degree P S G Sc
  have Pd := natDegree_mul_le_of_le p2.le ud
  have hd : (P*U-G).natDegree≤5 := natDegree_sub_le_of_le Pd (Gd.trans (by decide : 4≤5))
  obtain ⟨V,ve⟩ := nodalHull_dvd_of_evals_zero (S:=S) (P:=P*U-G) (by
    intro x hx
    simp only [U,eval_sub,eval_mul,nodalDivide_eval P S G hx,mul_div_cancel₀ _ (n x hx),sub_self])
  change P*U-G=D*V at ve
  have Vd : V.natDegree≤1 := by
    by_cases z : V=0
    · simp [z]
    have d := natDegree_mul (monic_nodalHull S).ne_zero z
    rw [←show D=nodalHull S from rfl,←ve,show D.natDegree=4 from (natDegree_nodalHull _).trans Sc] at d
    omega
  have ce := congrArg (fun q : K[X]=>q.coeff 5) ve
  simp only [coeff_sub,coeff_eq_zero_of_natDegree_lt (Gd.trans_lt (by decide : 4<5)),
    sub_zero,show (5:ℕ)=2+3 by decide,coeff_mul_add_eq_of_natDegree_le p2.le ud] at ce
  have vtop : (D*V).coeff 5 = D.coeff 4*V.coeff 1 :=
    coeff_mul_add_eq_of_natDegree_le ((natDegree_nodalHull S).trans Sc).le Vd
  rw [vtop,show D.coeff 4=1 by
    have e := (monic_nodalHull S).coeff_natDegree
    rwa [natDegree_nodalHull,Sc] at e,one_mul] at ce
  exact ⟨V,Vd,ve,by rw [nodalMeasure_top P S G Sc]; exact ce.symm⟩

theorem nodalMeasure_transfer_four {P G R : K[X]} (p2 : P.natDegree=2) (Gd : G.natDegree≤4)
    {S T : Finset K} (Sc : S.card=4) (Tc : T.card=4)
    (sn : ∀ x∈S,P.eval x≠0) (tn : ∀ x∈T,P.eval x≠0) {sig : K}
    (terminal : nodalHull T+P*R=C sig*nodalHull S) :
    nodalMeasure P S G=sig*nodalMeasure P T G := by
  obtain ⟨VS,VSd,hs,cs⟩ := measure_quotient_four p2 Gd Sc sn
  obtain ⟨VT,VTd,ht,ct⟩ := measure_quotient_four p2 Gd Tc tn
  have mult : nodalHull S*(VS-C sig*VT)=
      P*(nodalDivide P S G-nodalDivide P T G-R*VT) := by
    linear_combination -hs+ht+VT*terminal
  have dvd : P∣VS-C sig*VT :=
    (coprime_nodalHull_of_eval_ne sn).dvd_of_dvd_mul_left ⟨_,mult⟩
  have v : VS-C sig*VT=0 := by
    by_contra h
    have d := natDegree_le_of_dvd dvd h
    have m : (VS-C sig*VT).natDegree≤1 := natDegree_sub_le_of_le VSd
      ((natDegree_C_mul_le _ _).trans VTd)
    omega
  have c := congrArg (fun r : K[X]=>r.coeff 1) (sub_eq_zero.mp v)
  rw [coeff_C_mul,cs,ct] at c
  have pn : P≠0 := by intro z; simp [z] at p2
  have c2 : P.coeff 2≠0 := by
    rw [←p2,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr pn
  apply mul_left_cancel₀ c2
  linear_combination c

variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P R : K[X]} {dup k : Fin 10}

/-- Actual terminal hull identity. The scale is earned and never zero
when the fitted defect is quadratic and nonzero at the four clean sites. -/
theorem actual_terminal_hull_transfer (M : Placement A b P dup k)
    {S : Finset K} (Sc : S.card=4) (n : ∀ x∈S,P.eval x≠0) (p2 : P.natDegree=2)
    (T : CleanTerminalProfile A (nodalHull S) R) :
    ∃ sig : K, sig≠0 ∧ nodalHull S+P*R=C sig*nodalHull (offKnots A) := by
  let F := nodalHull S+P*R
  have sd : (nodalHull S).natDegree=4 := (natDegree_nodalHull _).trans Sc
  have fd : F.natDegree≤4 := natDegree_add_le_of_degree_le sd.le
    (natDegree_mul_le_of_le p2.le T.degR)
  have r (x : K) (hx : x∈offKnots A) : F.eval x=0 := by
    obtain ⟨j,gj,hj⟩ := mem_offKnots.mp hx
    have ne : j≠lastPhysical := fun e=>gj (e.symm ▸ M.rankData.cleanNine)
    have h := congrFun T.profile j
    simp only [Pi.add_apply,evalNodes_apply,diag_apply,Pi.smul_apply,Pi.single_eq_of_ne ne,
      smul_zero] at h
    rw [←hj]
    simpa only [F,eval_add,eval_mul,M.rankData.fit j gj] using h
  obtain ⟨sig,hs⟩ := polynomial_hull_of_test_zeros (offKnots A) F (by rw [M.rankData.offCard]; exact fd) r
  refine ⟨sig,?_,hs⟩
  intro sg
  have z : F=0 := by simp [hs,sg]
  have dvd : P ∣ nodalHull S := ⟨-R,by dsimp only [F] at z; linear_combination z⟩
  have u := (coprime_nodalHull_of_eval_ne n).dvd_of_dvd_mul_left
    (show P ∣ nodalHull S*1 by simpa using dvd)
  have deg := natDegree_le_of_dvd u (one_ne_zero : (1:K[X])≠0)
  simp [p2] at deg

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.nodalMeasure_transfer_four
#print axioms RKResearch.Certified.Graded.FourOffNewton.actual_terminal_hull_transfer

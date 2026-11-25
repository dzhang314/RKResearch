module

public import RKCert.ERK8OneOffActions

@[expose] public section

/-! The paid grade-four terminal, not the p9 grade-five terminal.
The physical last coordinate and all four row probes come from p8. -/
namespace RKResearch.Certified.Graded.OneOff.Eight

open RKResearch Polynomial Module Reverse
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- Actual E4 terminal polynomial. The second coefficient is linear
in the clock because F4 is span(g,h,c h), not all of F5. -/
theorem terminalProfile (ho : HasOrder 8 A b) (mid : ERKEvenHorizon A b 4)
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) (R : PhysicalPrefix A a d) :
    ∃ ρ : K, (lobattoCubic : K[X]).eval (2*d)=0 ∧
      ∀ r : Fin 10, r<Fin.last 9 → g A r=0 →
        14*nodes A r*(lobattoCubic : K[X]).eval (nodes A r) +
          scaled A a r*(ρ*(nodes A r-2*d))=0 := by
  let τ : Fin 10 := Fin.last 9
  let T : Fin 10 → K := coordinate τ
  have ct : nodes A τ=1 := (lastClock mid).1
  have tm : T∈treeSpace A 4 := (lastClock mid).2
  have gt : g A τ=0 :=
    terminalDefectZero ho mid (zeroSpace_mono A (by decide : 2≤3) (mDef_mem A 1))
  have ht : h A τ=0 := terminalDefectZero ho mid (h_in_grade_three A)
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have f0 : nodes A (0:Fin 10)=0 ∧ g A (0:Fin 10)=0 ∧ h A (0:Fin 10)=0 := by
    simpa [chartNode,chartDefect,chartH] using R.first.features 0
  have f3 : nodes A (3:Fin 10)=2*d ∧ g A (3:Fin 10)=0 ∧ h A (3:Fin 10)=a*d^2 := by
    simpa [chartNode,chartDefect,chartH] using R.first.features 3
  have diff : h A (4:Fin 10)≠h A (3:Fin 10) := by rw [f3.2.2]; exact R.fifth.2.2
  rw [treeSpace_coeff_sup ho (q:=4) (by decide)] at tm
  obtain ⟨_,⟨p,rfl⟩,F,Fm,eq⟩ := Submodule.mem_sup.mp tm
  let P := ofFn 5 p
  have pd : P.natDegree≤4 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have sumEq : evalNodes A P+F=T := by
    change evalNodes A (ofFn 5 p)+F=T
    rwa [evalNodes_ofFn A 4]
  have FE : ∃ β δ γ : K, F=(β • g A+δ • h A)+γ • diag (nodes A) (h A) := by
    have fm := Fm
    rw [D.span_four,D.base.span_three] at fm
    obtain ⟨u,um,w,wm,hEq⟩ := Submodule.mem_sup.mp fm
    obtain ⟨β,δ,rfl⟩ := Submodule.mem_span_pair.mp um
    obtain ⟨γ,rfl⟩ := Submodule.mem_span_singleton.mp wm
    exact ⟨β,δ,γ,hEq.symm⟩
  obtain ⟨β,δ,γ,fe⟩ := FE
  have val (r : Fin 10) : T r=P.eval (nodes A r)+β*g A r+h A r*(δ+γ*nodes A r) := by
    rw [←sumEq,fe]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,evalNodes_apply]
    ring
  have early0 (r : Fin 10) (rr : r<τ) : T r=0 := by
    have ne : r≠τ := ne_of_lt rr
    simp [T,coordinate,ne]
  have p0 : P.eval 0=0 := by
    have e := (val (0:Fin 10)).symm
    simpa only [f0.1,f0.2.1,f0.2.2,mul_zero,zero_mul,add_zero,
      early0 _ (by decide : (0:Fin 10)<τ)] using e
  have p1 : P.eval 1=1 := by
    have e := (val τ).symm
    simpa only [ct,gt,ht,mul_zero,zero_mul,add_zero,T,coordinate,Pi.single_eq_same] using e
  have e3 : (0:K)+h A (3:Fin 10)*0=P.eval (2*d)+h A (3:Fin 10)*(δ+γ*(2*d)) := by
    simpa only [f3.1,f3.2.1,mul_zero,add_zero,early0 _ (by decide : (3:Fin 10)<τ)] using val 3
  have e4 : (0:K)+h A (4:Fin 10)*0=P.eval (2*d)+h A (4:Fin 10)*(δ+γ*(2*d)) := by
    simpa only [R.fifth.1,R.fifth.2.1,mul_zero,add_zero,early0 _ (by decide : (4:Fin 10)<τ)] using val 4
  obtain ⟨pD,qD⟩ := common_clock_affine_parameters diff e3 e4
  have probes (k : Fin 4) : probe A b k.val (evalNodes A P)=b τ := by
    have e := congrArg (probe A b k.val) sumEq
    rw [map_add,probe_zeroSpace ho (by have hk := k.isLt; omega) Fm,add_zero] at e
    rw [e]
    change row _ (coordinate τ)=b τ
    rw [row_coordinate,ct,one_pow,mul_one]
  have pEq := terminalPolynomial ho pd p0 p1 (b τ) probes
  have pVal (x : K) : P.eval x=14*x*(lobattoCubic : K[X]).eval x := by
    rw [pEq,eval_mul,eval_mul,eval_X,eval_C]
    ring
  have lD : (lobattoCubic : K[X]).eval (2*d)=0 := by
    rw [pVal] at pD
    exact (mul_eq_zero.mp pD).resolve_left (mul_ne_zero (by norm_num)
      (mul_ne_zero (by norm_num) dn))
  refine ⟨a*γ,lD,fun r rr gr=>?_⟩
  have e := val r
  rw [early0 r rr,gr,mul_zero,add_zero,pVal] at e
  have line : δ+γ*nodes A r=γ*(nodes A r-2*d) := by linear_combination qD
  rw [line] at e
  rw [scaled_eval]
  calc
    _ = 14*nodes A r*(lobattoCubic : K[X]).eval (nodes A r)+h A r*(γ*(nodes A r-2*d)) := by
      field_simp [an] <;> ring
    _ = 0 := e.symm

end RKResearch.Certified.Graded.OneOff.Eight

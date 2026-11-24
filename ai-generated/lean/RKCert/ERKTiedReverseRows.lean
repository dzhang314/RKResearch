module
public import RKCert.ReverseTwoNodeCausality
public import RKCert.OrderTwelveReverseRows

@[expose] public section
/-! # Reuse of the causal two-node system for compressed tableaux
The compressed shadow need only attain order eight. None of the scalar
tests assumes a nonzero weight at every stage, simple clocks, positivity,
an ordered field, or a localized first adjoint.
-/
namespace RKCert.Paired
open RKCert.ReverseTwoNode RKCert.Paired.OrderTwelve RKCert.Paired.Clock
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}
set_option maxHeartbeats 2000000

/-- Last active pivot, with any number of trailing zero-output stages. -/
theorem tied_second_nonzero_at_pivot (ha:StrictLower A) {i:Fin s}
    (later:∀ j,i<j→b j=0) (live:reverseResidual A b 0 i≠0) :
    reverseResidual A b 1 i≠0 := by
  have za (k:ℕ) : transMat A (powerWeight (mirror A) b k) i=0 := by
    apply causal_transpose ha i
    intro j hj
    have h : i<j := Fin.rev_lt_rev.mp hj
    simp [powerWeight,later j h]
  have F0 : reverseResidual A b 0 i= -(mirror A i*b i) := by
    rw [reverseResidual_eq _ _ _ (by norm_num),reflWeight_power,reflWeight_power,Pi.sub_apply,za 0]
    simp [powerWeight]
  have F1 : reverseResidual A b 1 i= -((2:K)⁻¹*((mirror A i)^2*b i)) := by
    rw [reverseResidual_eq _ _ _ (by norm_num),reflWeight_power,reflWeight_power,Pi.sub_apply,za 1]
    norm_num [powerWeight]
  have nz:=mul_ne_zero_iff.mp (fun he:mirror A i*b i=0=>live (by rw [F0,he,neg_zero]))
  rw [F1]
  exact neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero (by norm_num))
    (mul_ne_zero (pow_ne_zero _ nz.1) nz.2))

/-- A tied adjoint profile has exactly the previously checked two-node
chronology after using `h=Yb` and `g=(α/2)d`. -/
theorem tied_adjoint_profile_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:8≤p)
    (second:∃ α:K,α≠0∧∀i,reverseResidual A b 1 i=α*reverseResidual A b 0 i)
    (third:∃ β:K,∀i,reverseResidual A b 2 i=β*reverseResidual A b 0 i)
    (fourth:∃ q l:K,∀i,reverseResidual A b 3 i=(q+l*mirror A i)*reverseResidual A b 0 i)
    (advance:∃ k e:K,∀i,transMat A (reverseResidual A b 0) i=(k+e*mirror A i)*reverseResidual A b 0 i)
    (shifted:∃ m f r:K,∀i,transMat A (diag (mirror A) (reverseResidual A b 0)) i=
      (m+f*mirror A i+r*(mirror A i)^2)*reverseResidual A b 0 i) : False := by
  classical
  obtain ⟨α,αn,e2⟩:=second
  obtain ⟨β,e3⟩:=third
  obtain ⟨q,l,e4⟩:=fourth
  obtain ⟨k,e,eN⟩:=advance
  obtain ⟨m,f,r,eY⟩:=shifted
  let N:=transMat A
  let y:=mirror A
  let d:=reverseResidual A b 0
  let h:=powerWeight y b 1
  let g:=(α/2) • d
  have gv (i:Fin s) : g i=(α/2)*d i := rfl
  have hv (i:Fin s) : h i=y i*b i := by simp [h,powerWeight]
  have dg (i:Fin s) : d i=(2/α)*g i := by
    rw [gv];field_simp
  have powers (k:ℕ) : powerWeight y h k=powerWeight y b (k+1) := by
    ext i
    simp only [powerWeight,hv,pow_succ]
    ring
  have raw (k:ℕ) (i:Fin s) : N (powerWeight y b k) i=
      y i^(k+1)*b i/((k+1:ℕ):K)+reverseResidual A b k i := by
    have h := congrFun (reverseResidual_eq A b k (by exact_mod_cast Nat.succ_ne_zero k)) i
    rw [reflWeight_power,reflWeight_power] at h
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,powerWeight] at h
    simp only [N,y]
    rw [h,div_eq_mul_inv]
    ring
  have rows : TwoNodeRows N y h g := by
    refine ⟨?_,⟨β*(2/α),?_⟩,⟨q*(2/α),l*(2/α),?_⟩,⟨k,e,?_⟩,⟨m,f,r,?_⟩⟩
    · intro i
      change N (powerWeight y b 1) i=y i*h i/2+2*g i
      rw [raw 1,hv,gv,e2]
      change y i^2*b i/((2:ℕ):K)+α*d i=y i*(y i*b i)/2+2*(α/2*d i)
      norm_num
      ring
    · intro i
      rw [powers,raw 2,hv,e3]
      change y i^3*b i/((3:ℕ):K)+β*d i=y i^2*(y i*b i)/3+(β*(2/α))*g i
      rw [dg i]
      norm_num
      ring
    · intro i
      rw [powers,raw 3,hv,e4]
      change y i^4*b i/((4:ℕ):K)+(q+l*y i)*d i=
        y i^3*(y i*b i)/4+(q*(2/α)+l*(2/α)*y i)*g i
      rw [dg i]
      norm_num
      ring
    · intro i
      rw [show g=(α/2) • d from rfl,map_smul,Pi.smul_apply,smul_eq_mul]
      change (α/2)*transMat A (reverseResidual A b 0) i=(k+e*y i)*((α/2)*d i)
      rw [eN i]
      change (α/2)*((k+e*y i)*d i)=_
      ring
    · intro i
      rw [show g=(α/2) • d from rfl,map_smul,map_smul,Pi.smul_apply,smul_eq_mul]
      change (α/2)*transMat A (diag (mirror A) (reverseResidual A b 0)) i=
        (m+f*y i+r*(y i)^2)*((α/2)*d i)
      rw [eY i]
      change (α/2)*((m+f*y i+r*(y i)^2)*d i)=_
      ring
  apply two_node_confinement Fin.revPerm N (causal_transpose ha) y h g rows
  · intro i e
    rw [hv,e,zero_mul]
  · intro t u
    let T : Finset K := {0,t,u}
    have card : T.card≤3 := calc
      T.card ≤ ({t,u}:Finset K).card+1 := Finset.card_insert_le ..
      _ ≤ (({u}:Finset K).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) _
      _ = 3 := by simp
    obtain ⟨i,bi,hi⟩:=reflected_active_avoid ho T (by omega)
    have hh : y i≠0∧y i≠t∧y i≠u := by
      change y i∉({0,t,u}:Finset K) at hi
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
    exact ⟨i,by rw [hv];exact mul_ne_zero hh.1 bi,hh.2.1,hh.2.2⟩

end RKCert.Paired


module

public import RKCert.ReviewedNative.OptionalTerminalMark

@[expose] public section

/-! # Actual charged probes on a marked physical tableau

Subtract adjacent probes precisely when the last physical coordinate
was paid. The resulting linear maps move with the actual diagonal
clock and have a native Cauchy kernel, without polynomial tables. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Polynomial
open scoped Matrix
noncomputable section
variable {K : Type*} [Field K] {s p q j : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

def chargedProbe (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1)→K)
    (k : ℕ) : (Fin (s+1)→K) →ₗ[K] K := by
  classical
  exact if firstSeed A b=0 then probe A b k-probe A b (k+1) else probe A b k

private theorem probe_clock (k : ℕ) (u : Fin (s+1)→K) :
    probe A b k (diag (nodes A) u)=probe A b (k+1) u := by
  simp only [probe,row_apply,dotProduct,diag_apply,pow_succ,mul_assoc]

theorem chargedProbe_clock (k : ℕ) (u : Fin (s+1)→K) :
    chargedProbe A b k (diag (nodes A) u)=chargedProbe A b (k+1) u := by
  by_cases z : firstSeed A b=0
  · simp only [chargedProbe,z,ite_true,LinearMap.sub_apply,probe_clock]
  · simp only [chargedProbe,z,ite_false,probe_clock]

theorem chargedProbe_paid (ha : ∀ i l,i ≤ l → A i l=0) (ho : HasOrder A b p)
    (L : LastActive b (Fin.last s)) (k : ℕ) {u : Fin (s+1)→K}
    (h : u∈markedDefectSpace A b j) (pay : k+j+1+terminalDebit A b≤p) :
    chargedProbe A b k u=0 := by
  by_cases z : firstSeed A b=0
  · have e := paid_probe_marked_defect ha ho L h k (by omega)
    have f := paid_probe_marked_defect ha ho L h (k+1)
      (by simp [terminalDebit,z] at pay; omega)
    simp only [chargedProbe,z,ite_true,LinearMap.sub_apply,e,f,sub_self]
  · have h0 : u∈zeroSpace A j := by
      simpa only [markedDefectSpace,terminalMark,ite_eq_right z,sup_bot_eq] using h
    have q : probe A b k u=0 := probe_zeroSpace ho (by omega) h0
    simpa only [chargedProbe,z,ite_false] using q

/-- q charged moments and the vanished origin force all q+1 polynomial
coefficients to vanish. The marked credit is a single constant Cauchy row. -/
theorem charged_coeff_separated (ho : HasOrder A b p) (pay : 2*q+1≤p)
    (a : Fin (q+1)→K) (h0 : a 0=0)
    (tests : ∀ i<q,chargedProbe A b i (coeffEval A q a)=0) : a=0 := by
  have form (i : ℕ) (hi : i≤q) :
      probe A b i (coeffEval A q a) = ∑ j : Fin q,a j.succ/((i+j.val+2:ℕ):K) := by
    rw [probe_coeffEval ho (by omega),Fin.sum_univ_succ,h0,zero_div,zero_add]
    simp only [Fin.val_succ,Nat.add_assoc]
  have rest : ∀ k : Fin q,a k.succ=0 := by
    by_cases z : firstSeed A b=0
    · have eq (i : ℕ) (hi : i≤q) : probe A b i (coeffEval A q a)=probe A b 0 (coeffEval A q a) := by
        induction i with
        | zero => rfl
        | succ i ih =>
          have h := tests i (by omega)
          simp only [chargedProbe,z,ite_true,LinearMap.sub_apply,sub_eq_zero] at h
          exact h.symm.trans (ih (by omega))
      have e (i : Fin (q+1)) :
          (∑ j : Fin q,a j.succ/((i.val+j.val+2:ℕ):K))=probe A b 0 (coeffEval A q a) := by
        rw [←form i.val (by have := i.isLt; omega)]
        exact eq i.val (by have := i.isLt; omega)
      exact congrFun (paid_constant_cauchy ho pay _ _ e).1
    · apply moments_detect ho (d:=2) (by decide) (by omega) (fun i j=>by omega)
      intro i
      have e := tests i.val i.isLt
      simp only [chargedProbe,z,ite_false,form _ i.isLt.le] at e
      exact e
  ext k
  exact Fin.cases h0 rest k

theorem charged_polynomial_separated (ho : HasOrder A b p) (pay : 2*q+1≤p)
    (P : K[X]) (pd : P.natDegree≤q) (h0 : P.coeff 0=0)
    (tests : ∀ i<q,chargedProbe A b i (evalNodes A P)=0) : P=0 := by
  rw [evalNodes_eq_coeffEval A P pd] at tests
  have z := charged_coeff_separated ho pay (fun k : Fin (q+1)=>P.coeff k.val) h0 tests
  ext i
  rw [coeff_zero]
  by_cases h : i≤q
  · exact congrFun z (⟨i,by omega⟩ : Fin (q+1))
  · exact coeff_eq_zero_of_natDegree_lt (pd.trans_lt (by omega))

/-- Propagate a finite consecutive probe window through an exact sequence
of clock shifts modulo a single mesh vector. -/
theorem extend_charged_probe_window (v : ℕ→Fin (s+1)→K) (g₀ : Fin (s+1)→K) (B n : ℕ)
    (base : ∀ i≤n,∀ k≤B,chargedProbe A b k (v i)=0)
    (step : ∀ i<n,∃ t : K,diag (nodes A) (v i)-v (i+1)=t • g₀)
    (mesh : ∀ k<B+n,chargedProbe A b k g₀=0) :
    ∀ k≤B+n,chargedProbe A b k (v 0)=0 := by
  induction n generalizing v with
  | zero => intro k hk; exact base 0 le_rfl k (by omega)
  | succ n ih =>
    intro k hk
    by_cases h : k≤B
    · exact base 0 (by omega) k h
    have up := ih (fun i=>v (i+1)) (fun i hi k hk=>base _ (by omega) k hk)
      (fun i iH=>step _ (by omega)) (fun i im=>mesh _ (by omega)) (k-1) (by omega)
    obtain ⟨t,e⟩ := step 0 (by omega)
    have q := congrArg (fun u=>chargedProbe A b (k-1) u) e
    rw [map_sub,chargedProbe_clock,map_smul,mesh (k-1) (by omega),smul_zero,sub_eq_zero] at q
    rw [show k-1+1=k by omega] at q
    exact q.trans up

end
end RKResearch.Certified.Graded.Reverse

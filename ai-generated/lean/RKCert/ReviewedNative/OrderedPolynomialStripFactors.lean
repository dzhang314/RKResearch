module

public import RKCert.ReviewedNative.OrderedPolynomialSignStrips
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Complete signed strips with at most one root left over

The residual is exactly linear when the known roots are one short of the
degree. Endpoint signs and a positive product determine its outer direction;
Vieta fixes the correct coefficient expression for any rational box leaf.
-/
namespace RKCert.ReviewedNative.OrderedPolynomialSignStrips

open Polynomial
open scoped BigOperators

universe u
noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def withExtra {n : ℕ} (t : Fin n → K) (e : K) : Option (Fin n) → K
  | none => e
  | some i => t i

@[simp] theorem withExtra_none {n : ℕ} (t : Fin n → K) (e : K) : withExtra t e none = e := rfl

@[simp] theorem withExtra_some {n : ℕ} (t : Fin n → K) (e : K) (i : Fin n) :
    withExtra t e (some i) = t i := rfl

theorem withExtra_injective {n : ℕ} {t : Fin n → K} {e : K}
    (ht : Function.Injective t) (neq : ∀ i, e ≠ t i) :
    Function.Injective (withExtra t e) := by
  rintro (_ | i) (_ | j) h
  · rfl
  · exact (neq j h).elim
  · exact (neq i h.symm).elim
  · exact congrArg some (ht h)

theorem indexedHull_withExtra {n : ℕ} (t : Fin n → K) (e : K) :
    indexedHull (withExtra t e) Finset.univ = (X-C e)*indexedHull t Finset.univ := by
  simp only [indexedHull,Fintype.prod_option,withExtra_none,withExtra_some]

theorem scale_layout {ι : Type*} (t : ι → K) (I : Finset ι) (F P : K[X]) (c : K)
    (Fscale : F = C c*P) (Pfact : P = C P.leadingCoeff*indexedHull t I) :
    F = C F.leadingCoeff*indexedHull t I := by
  have hl : F.leadingCoeff=c*P.leadingCoeff := by
    rw [Fscale,leadingCoeff_mul,leadingCoeff_C]
  calc
    F = C c*P := Fscale
    _ = C c*(C P.leadingCoeff*indexedHull t I) :=
      congrArg (fun X : K[X] => C c*X) Pfact
    _ = C F.leadingCoeff*indexedHull t I := by rw [hl,C_mul,mul_assoc]

theorem exists_indexed_linear_residual {ι : Type*} {P : K[X]} {t : ι → K} {S : Finset ι}
    (degree : P.natDegree = S.card+1) (ht : Function.Injective t)
    (roots : ∀ i∈S, P.IsRoot (t i)) :
    ∃ e : K, P = C P.leadingCoeff*((X-C e)*indexedHull t S) := by
  obtain ⟨B,hB⟩ := indexedHull_dvd t S ht roots
  have pn : P ≠ 0 := by
    intro z
    rw [z,natDegree_zero] at degree
    omega
  have bn : B ≠ 0 := by
    intro z
    exact pn (by simp [hB,z])
  have db := natDegree_mul (indexedHull_monic t S).ne_zero bn
  have dB : B.natDegree=1 := by
    rw [←hB,indexedHull_degree,degree] at db
    omega
  have bc : B.coeff 1 ≠ 0 := by
    rw [← dB,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr bn
  let e := -(B.coeff 0)/B.coeff 1
  have be : B = C (B.coeff 1)*(X-C e) := by
    calc
      B = C (B.coeff 1)*X+C (B.coeff 0) := eq_X_add_C_of_natDegree_le_one dB.le
      _ = C (B.coeff 1)*(X-C e) := by
        have this : B.coeff 1*e = -B.coeff 0 := by
          dsimp only [e]
          rw [mul_comm,div_mul_cancel₀ _ bc]
        rw [mul_sub,← C_mul,this,C_neg,sub_neg_eq_add]
  have ff : P = C (B.coeff 1)*((X-C e)*indexedHull t S) := by
    calc
      P = indexedHull t S*B := hB
      _ = C (B.coeff 1)*((X-C e)*indexedHull t S) := by
        conv_lhs => rw [be]
        ring
  have fl : P.leadingCoeff = B.coeff 1 := by
    have f := congrArg Polynomial.leadingCoeff ff
    simpa only [leadingCoeff_mul,leadingCoeff_C,(monic_X_sub_C e).leadingCoeff,
      (indexedHull_monic t S).leadingCoeff,mul_one] using f
  exact ⟨e,by rw [fl]; exact ff⟩

theorem exists_one_extra_root {n : ℕ} {P : K[X]} {t : Fin n → K}
    (degree : P.natDegree = n+1) (ht : Function.Injective t)
    (roots : ∀ i, P.IsRoot (t i)) :
    ∃ e : K, P = C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ) :=
  exists_indexed_linear_residual (by simpa only [Finset.card_univ,Fintype.card_fin] using degree)
    ht (fun i _ => roots i)

theorem nextCoeff_of_indexed_layout {ι : Type*} {t : ι → K} {I : Finset ι}
    {P : K[X]} {m : ℕ} (size : I.card=m+1)
    (layout : P = C P.leadingCoeff*indexedHull t I) :
    P.coeff m = -P.leadingCoeff*(∑ i ∈ I,t i) := by
  have e : (indexedHull t I).coeff m = -∑ i ∈ I,t i := by
    have h := prod_X_sub_C_coeff_card_pred I t (by omega)
    simpa only [size,Nat.add_sub_cancel,indexedHull] using h
  calc
    P.coeff m = (C P.leadingCoeff*indexedHull t I).coeff m :=
      congrArg (fun p : K[X] => p.coeff m) layout
    _ = -P.leadingCoeff*(∑ i ∈ I,t i) := by rw [coeff_C_mul,e,mul_neg,neg_mul]

theorem vieta_indexed_outer {n : ℕ} {P : K[X]} {t : Fin n → K} {e : K}
    (degree : P.natDegree=n+1)
    (fact : P = C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ)) :
    P.coeff n = -P.coeff (n+1)*(e+∑ i : Fin n,t i) := by
  have size : (Finset.univ : Finset (Option (Fin n))).card=n+1 := by simp
  have f : P = C P.leadingCoeff*indexedHull (withExtra t e) Finset.univ := by
    rw [indexedHull_withExtra]
    exact fact
  have out := nextCoeff_of_indexed_layout size f
  have lead : P.leadingCoeff=P.coeff (n+1) := by rw [←degree,coeff_natDegree]
  rw [lead,Fintype.sum_option] at out
  simpa only [withExtra_none,withExtra_some] using out

theorem vieta_one_extra {P : K[X]} {t : Fin 7 → K} {e : K}
    (degree : P.natDegree=8)
    (fact : P = C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ))
    : P.coeff 7 = -P.coeff 8*(e+∑ i : Fin 7,t i) :=
  vieta_indexed_outer degree fact

/-- Exact evaluation of the linear residual times the known nodal factors. -/
theorem eval_extra_factor_at {n : ℕ} {P : K[X]} {t : Fin n → K} {e : K}
    (fact : P = C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ))
    (x : K) : P.eval x=P.leadingCoeff*((x-e)*∏ i : Fin n,(x-t i)) := by
  calc
    P.eval x = (C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ)).eval x :=
      congrArg (Polynomial.eval x) fact
    _ = _ := by simp only [eval_mul,eval_C,eval_sub,eval_X,indexedHull,eval_prod]

theorem extra_le_threshold_of_eval_nonpos_odd {n : ℕ} {P : K[X]} {t : Fin n → K} {e x : K}
    (odd : Odd n) (fact : P=C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ))
    (tpos : ∀ i,x<t i) (pl : 0<P.leadingCoeff) (sign : P.eval x≤0) : e≤x := by
  have hprod : 0<∏ i : Fin n,(t i-x) :=
    Finset.prod_pos (fun i _ => sub_pos.mpr (tpos i))
  have ev : (∏ i : Fin n,(x-t i)) = -(∏ i : Fin n,(t i-x)) := by
    have h (i : Fin n) : x-t i = -(t i-x) := by ring
    simp only [h,Finset.prod_neg,Finset.card_univ,Fintype.card_fin,odd.neg_one_pow,neg_one_mul]
  apply le_of_not_gt
  intro ep
  have bad : 0<P.eval x := by
    rw [eval_extra_factor_at fact x,ev]
    exact mul_pos pl (mul_pos_of_neg_of_neg (sub_neg.mpr ep) (neg_lt_zero.mpr hprod))
  exact (not_lt_of_ge sign) bad

theorem threshold_le_extra_of_eval_nonneg {n : ℕ} {P : K[X]} {t : Fin n → K} {e x : K}
    (fact : P=C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ))
    (tlt : ∀ i,t i<x) (pl : P.leadingCoeff<0) (sign : 0≤P.eval x) : x≤e := by
  have hprod : 0<∏ i : Fin n,(x-t i) :=
    Finset.prod_pos (fun i _ => sub_pos.mpr (tlt i))
  apply le_of_not_gt
  intro ep
  have bad : P.eval x<0 := by
    rw [eval_extra_factor_at fact x]
    exact mul_neg_of_neg_of_pos pl (mul_pos (sub_pos.mpr ep) hprod)
  exact (not_lt_of_ge sign) bad

theorem extra_le_zero_of_eval_zero {P : K[X]} {t : Fin 7 → K} {e : K}
    (fact : P=C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ))
    (tpos : ∀ i,0<t i) (pl : 0<P.leadingCoeff) (sign : P.eval 0≤0) : e≤0 :=
  extra_le_threshold_of_eval_nonpos_odd (show Odd (7:ℕ) from ⟨3,rfl⟩) fact tpos pl sign

theorem one_le_extra_of_eval_one {P : K[X]} {t : Fin 7 → K} {e : K}
    (fact : P=C P.leadingCoeff*((X-C e)*indexedHull t Finset.univ))
    (tlt : ∀ i,t i<1) (pl : P.leadingCoeff<0) (sign : 0≤P.eval 1) : 1≤e :=
  threshold_le_extra_of_eval_nonneg fact tlt pl sign

end
end RKCert.ReviewedNative.OrderedPolynomialSignStrips

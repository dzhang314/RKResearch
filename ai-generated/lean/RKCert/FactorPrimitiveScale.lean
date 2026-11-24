module
public import RKCert.IntegralFactorGate
public import RKCert.StagePrimitives
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Tactic.Ring

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial RKCert.Paired
variable {K : Type*} [Field K]

/-- Scaling all roots preserves a homogeneous moment equation. -/
theorem scale_moment (L D : ℕ) (c : K) (P : K[X]) (w : K) :
    moment L D (P.scaleRoots c) (c*w)=c^(P.natDegree+2)*moment L D P w := by
  simp only [moment,coeff_scaleRoots,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i≤P.natDegree
  · have e : c^(P.natDegree-i)*c^(i+2)=c^(P.natDegree+2) := by rw [←pow_add]; congr 1; omega
    rw [←e]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hi)]; ring

theorem moment_mul_C (L D : ℕ) (P : K[X]) (a w : K) :
    moment L D (P*C a) w=a*moment L D P w := by
  simp only [moment,coeff_mul_C,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro _ _; ring

variable [CharZero K]

omit [CharZero K] in
theorem weighted_primitive_sum (D : ℕ) (P : K[X]) (hd : P.natDegree≤D) (w : K) :
    (primitive (X*P)).eval w=∑i∈Finset.range (D+1), P.coeff i/((i+2:ℕ):K)*w^(i+2) := by
  conv_lhs => rw [P.as_sum_range' (D+1) (by omega),Finset.mul_sum,map_sum,eval_finsetSum]
  simp only [X_mul_monomial,primitive_monomial,eval_monomial,Nat.add_assoc]

theorem moment_eq_weighted_primitive (L D : ℕ) (hL : ∀i≤D,i+2∣L)
    (P : K[X]) (hd : P.natDegree≤D) (w : K) :
    moment L D P w=(L:K)*(primitive (X*P)).eval w := by
  rw [weighted_primitive_sum D P hd w,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have co : (L/(i+2):ℕ)*(i+2)=L := Nat.div_mul_cancel (hL i (by simpa using Finset.mem_range.mp hi))
  have cast : ((L/(i+2):ℕ):K)*((i+2:ℕ):K)=(L:K) := by exact_mod_cast co
  rw [←cast]
  have hn : ((i+2:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Apply an integral-divisor gate to a nonmonic native polynomial after a
known invertible change of root coordinates and leading-coefficient units. -/
theorem native_from_scaled (G : K[X]) (H : ℤ[X]) (c a : K) (hc:c≠0) (ha:a≠0)
    (hs : G.scaleRoots c=C a*((X*H).map (Int.castRingHom K)))
    (L D : ℕ) (pay : ∀i≤D,i+2∣L)
    (gate : ∀Q : K[X], ∀v, Q.Monic → Q∣(X*H).map (Int.castRingHom K) →
      Q.natDegree≤D → (H.map (Int.castRingHom K)).eval v=0 → moment L D Q v≠0)
    (P : K[X]) (w : K) (p0 : P≠0) (pf : P∣G) (hd : P.natDegree≤D) (hw:w≠0)
    (root : G.eval w=0) : (primitive (X*P)).eval w ≠0 := by
  intro bad
  let b:=P.leadingCoeff
  have hb : b≠0 := leadingCoeff_ne_zero.mpr p0
  let U:=P*C b⁻¹
  have hm : U.Monic := monic_mul_leadingCoeff_inv p0
  have ud : U∣G := by
    obtain ⟨Q,hQ⟩:=pf
    refine ⟨C b*Q,?_⟩
    change G=P*C b⁻¹*(C b*Q)
    rw [hQ,mul_assoc,←mul_assoc (C b⁻¹),←C_mul,inv_mul_cancel₀ hb,C_1,one_mul]
  let W:=U.scaleRoots c
  have Wd : W∣(X*H).map (Int.castRingHom K) := by
    have hh:=ud.scaleRoots (r:=c)
    rw [hs] at hh
    have unit : IsUnit (C a) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
    exact (unit.dvd_mul_left).mp hh
  have wr : (H.map (Int.castRingHom K)).eval (c*w)=0 := by
    have h:=(scaleRoots_eval_mul G w c).trans (by rw [root,mul_zero])
    rw [hs,eval_mul,eval_C,Polynomial.map_mul,map_X,eval_mul,eval_X] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ha)).resolve_left (mul_ne_zero hc hw)
  have uh : U.natDegree≤D := by
    change (P*C b⁻¹).natDegree≤D
    rw [natDegree_mul_C (inv_ne_zero hb)]; exact hd
  have wh : W.natDegree≤D := by simpa only [W,natDegree_scaleRoots] using uh
  apply gate W (c*w) ((monic_scaleRoots_iff c).mpr hm) Wd wh wr
  change moment L D (U.scaleRoots c) (c*w)=0
  rw [scale_moment,show U=P*C b⁻¹ from rfl,moment_mul_C,moment_eq_weighted_primitive L D pay P hd w,bad]
  ring

end RKCert.FixedFactor

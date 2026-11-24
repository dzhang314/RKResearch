module

public import RKCert.ERKOrderNinePencilScalar
public import RKCert.ERKLowLobatto

@[expose] public section

/-! # Six clean nodes of an order-nine tableau

No positivity of the Runge–Kutta weights or bound on the abscissas is
needed. The ordered-field assumption occurs only in the exact scalar
pencil obstruction.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- A canonical endpoint exclusion. Its classical equality test is fixed
so the same finset can be used over an unordered or an ordered field. -/
noncomputable abbrev endpointErase {a : Type*} (S : Finset a) (x : a) : Finset a :=
  @Finset.erase a (fun _ _ => Classical.propDecidable _) S x

omit [CharZero K] in
noncomputable def lobattoPencil (l : K) : K[X] :=
  monomial 0 (1/42-l/14) + monomial 1 (-1/3+9*l/14) +
    monomial 2 (4/3-3*l/2) + monomial 3 (l-2) + monomial 4 1

theorem lobattoPencil_scale (l u : K) :
    42*(lobattoPencil l).eval u=pencilScaled l u := by
  simp [lobattoPencil,pencilScaled]
  ring

set_option maxHeartbeats 850000 in
/-- The three exact beta moments distinguish the monic pencil; no roots
or moment weights are supplied independently of the physical tableau. -/
theorem beta_quartic_decoder (Q : K[X]) (hd : Q.natDegree ≤ 4)
    (h4 : Q.coeff 4=1)
    (hm : ∀ k : Fin 3,
      (∑ j : Fin 5, Q.coeff j.val / ((k.val+j.val+3:ℕ):K)) -
      (∑ j : Fin 5, Q.coeff j.val / ((k.val+j.val+2:ℕ):K))=0) :
    Q = lobattoPencil (Q.coeff 3+2) := by
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  norm_num [Fin.sum_univ_succ] at hm0 hm1 hm2
  have h0 : Q.coeff 0=1/42-(Q.coeff 3+2)/14 := by
    linear_combination -120*hm0 + 480*hm1 - 420*hm2 - (5/42)*h4
  have h1 : Q.coeff 1= -1/3+9*(Q.coeff 3+2)/14 := by
    linear_combination 480*hm0 - 2220*hm1 + 2100*hm2 + (20/21)*h4
  have h2 : Q.coeff 2=4/3-3*(Q.coeff 3+2)/2 := by
    linear_combination -420*hm0 + 2100*hm1 - 2100*hm2 - (5/3)*h4
  ext n
  by_cases hn : n≤4
  · interval_cases n <;> simp [lobattoPencil,coeff_monomial,h0,h1,h2,h4]
  · have hn0 : 0≠n := by omega
    have hn1 : 1≠n := by omega
    have hn2 : 2≠n := by omega
    have hn3 : 3≠n := by omega
    have hn4 : 4≠n := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree<n)]
    simp [lobattoPencil,coeff_monomial,coeff_C,Ne.symm hn0,hn1,hn2,hn3,hn4]

theorem order9_six_on_pencil {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=6) (h1 : (1:K)∈onNodes A)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    ∃ l : K, nodalHull (endpointErase (endpointErase (onNodes A) 1) 0)=lobattoPencil l := by
  let S := endpointErase (endpointErase (onNodes A) 1) 0
  let H := nodalHull S
  have h0 := zero_mem_onNodes ha
  have hc1 := Finset.card_erase_add_one h1
  have hc0 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨zero_ne_one,h0⟩ :
    (0:K)∈(onNodes A).erase 1)
  change S.card+1=((onNodes A).erase 1).card at hc0
  have hd : H.natDegree=4 := by
    change (nodalHull S).natDegree=4
    rw [natDegree_nodalHull]
    omega
  have hm4 : H.coeff 4=1 := hd ▸ (monic_nodalHull S).coeff_natDegree
  refine ⟨H.coeff 3+2,beta_quartic_decoder H hd.le hm4 (fun k => ?_)⟩
  apply beta_probe_coeff ho H hd.le (by have:=k.isLt; omega)
  change probe A b k.val (evalNodes A ((X^2-X)*nodalHull S))=0
  rw [←nodalHull_two_endpoint_factor (onNodes A) h0 h1]
  exact probes_zero_of_on_roots hoff _ (fun _ => nodalHull_eval_of_mem) k.val

omit [CharZero K] in
/-- Mathlib's linear-root divisibility and degree lemmas give the exact
quotient. No splitting or all-root factorisation hypothesis is needed. -/
theorem quartic_divisor_two_complement_roots {H P : K[X]} {h d : K}
    (dH : H.natDegree=4) (dP : P.natDegree=2) (div : P∣H)
    (hh : H.eval h=0) (hd : H.eval d=0) (hne : d≠h)
    (hhP : P.eval h≠0) (hdP : P.eval d≠0) :
    ∃ a : K, a≠0 ∧ H=(X-C h)*((X-C d)*(C a * P)) := by
  obtain ⟨R,eR⟩ := div
  have hn : H≠0 := by intro e; simp [e] at dH
  have hP0 : P≠0 := fun e => hhP (by simp [e])
  have hR : R≠0 := fun e => hn (by simp [eR,e])
  have dR := natDegree_mul hP0 hR
  rw [←eR,dH,dP] at dR
  have hhR : R.eval h=0 := by rw [eR,eval_mul] at hh; exact (mul_eq_zero.mp hh).resolve_left hhP
  have hdR : R.eval d=0 := by rw [eR,eval_mul] at hd; exact (mul_eq_zero.mp hd).resolve_left hdP
  obtain ⟨U,eU⟩ := dvd_iff_isRoot.mpr hhR
  have hdU : U.eval d=0 := by
    rw [eU,eval_mul,eval_sub,eval_X,eval_C] at hdR
    exact (mul_eq_zero.mp hdR).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨V,eV⟩ := dvd_iff_isRoot.mpr hdU
  have hV : V≠0 := fun e => hR (by simp [eU,eV,e])
  have hU : U≠0 := fun e => hR (by simp [eU,e])
  have dUV := natDegree_mul (X_sub_C_ne_zero d) hV
  have dRU := natDegree_mul (X_sub_C_ne_zero h) hU
  rw [←eV,natDegree_X_sub_C] at dUV
  rw [←eU,natDegree_X_sub_C] at dRU
  have eC := eq_C_of_natDegree_eq_zero (p:=V) (by omega)
  refine ⟨V.coeff 0,fun e => hV (by rw [eC,e,map_zero]),?_⟩
  rw [eR,eU,eV,eC]
  simp only [coeff_C_zero]
  ring

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
theorem lobattoPencil_complement_primitive_ne_zero {l h d a : K} {P : K[X]}
    (dP : P.natDegree≤2) (hh : h≠0) (hd : d≠h)
    (eqP : lobattoPencil l=(X-C h)*((X-C d)*(C a*P))) :
    (primitive (X*P)).eval h≠0 := by
  intro hz
  have hsH : (lobattoPencil l).eval h=0 := by rw [eqP]; simp
  have hsD : (lobattoPencil l).eval d=0 := by rw [eqP]; simp
  have hroot : pencilScaled l h=0 := by rw [←lobattoPencil_scale,hsH,mul_zero]
  have droot : pencilScaled l d=0 := by rw [←lobattoPencil_scale,hsD,mul_zero]
  apply six_node_pencil_quadratic_ne_zero hroot droot hd
  have h34 : P.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h44 : P.coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hc (n : ℕ) (hn : 2≤n) :
      (lobattoPencil l).coeff n =
        a*(P.coeff (n-2) - (h+d)*P.coeff (n-1) + h*d*P.coeff n) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : 2+k=k+1+1 := by omega
    rw [e,eqP,coeff_X_sub_C_mul,coeff_X_sub_C_mul,coeff_X_sub_C_mul]
    simp only [coeff_C_mul,show k+1+1-2=k by omega,show k+1+1-1=k+1 by omega]
    ring
  have c2 := hc 2 (by decide)
  have c3 := hc 3 (by decide)
  have c4 := hc 4 (by decide)
  norm_num [lobattoPencil,coeff_monomial,h34,h44] at c2 c3 c4
  rw [primitive_eval_X_quadratic P dP] at hz
  have hfact : h^2*(6*P.coeff 0+4*P.coeff 1*h+3*P.coeff 2*h^2)=0 := by
    linear_combination 12*hz
  have hprim := (mul_eq_zero.mp hfact).resolve_left (pow_ne_zero _ hh)
  unfold pencilK
  linear_combination a*hprim + 6*c2 + (10*h+6*d)*c3 +
    (13*h^2+10*h*d+6*d^2)*c4

end Ordered
end RKCert.Paired

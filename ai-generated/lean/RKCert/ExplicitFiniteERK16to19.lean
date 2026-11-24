module
public import RKCert.ERKFinitePencil
public import RKCert.ExplicitOrderTwelve

@[expose] public section

/-! # Sharpest certified finite ERK lower endpoints, characteristic zero -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 2500000

theorem fixed8_no_profile {P G:K[X]} {u v t:K} {W:K→K}
    (J:KnotPair P G 8 u v) (pd:P.natDegree≤4) (tn:t≠0)
    (g : ∀ x, G.eval x=t*x*W x)
    (gate : ∀ (c:Fin 5→K) (a u:K),a≠0→a≠1→twoTests c a 3→W u=0→W (a*u)=0→c=0) :
    P=0 := by
  let e : Fin 5→K := fun i=>P.coeff i.val
  have ep : ofFn 5 e=P:=ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  let a:=v/u
  have a0 : a≠0 := div_ne_zero J.v_ne J.u_ne
  have a1 : a≠1 := fun h=>J.different ((div_eq_one_iff_eq J.u_ne).mp h)
  have nv : a*u=v := div_mul_cancel₀ _ J.u_ne
  have ru : W u=0 := (mul_eq_zero.mp ((g u).symm.trans J.u_mesh)).resolve_left (mul_ne_zero tn J.u_ne)
  have rv : W v=0 := (mul_eq_zero.mp ((g v).symm.trans J.v_mesh)).resolve_left (mul_ne_zero tn J.v_ne)
  have hz := gate _ a u a0 a1 (EndpointPhysical.normalize J.u_ne (endpoint_tests_three J (by decide) e ep))
    ru (by rwa [nv])
  have z := (EndpointPhysical.rescale_eq_zero_iff e J.u_ne).mp hz
  rw [←ep,z,map_zero]

theorem q8_no_profile {s ε d a r:ℕ} {A:Fin (s+1)→Fin (s+1)→K}
    {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {P G:K[X]} {u v:K}
    (C:Chart A 8 ε d a r U w G) (Pr:Profile A 8 a U w G P) (J:KnotPair P G 8 u v) :
    P=0 := by
  by_cases h:a<8
  · exact cubic_no_profile (by decide) J (Pr.aliasDegree h)
  have a8:a=8 := by have := C.aLe;omega
  have gd:G.natDegree=9 := C.meshDegree.trans (by omega)
  have sc (t:K) (V:K[X]) (g:G=t•V) : t≠0 := by
    intro hz
    rw [g,hz,zero_smul,natDegree_zero] at gd
    omega
  cases C.mesh with
  | even8 t g =>
    apply fixed8_no_profile (W:=lobatto9) J Pr.degree (t:=t*(-72))
      (mul_ne_zero (sc _ _ g) (by norm_num)) _ lobatto9_quartic_gate
    intro x; rw [g,eval_smul,even7_eval,smul_eq_mul]; ring
  | full8 t g =>
    apply fixed8_no_profile (W:=rightWeight8) J Pr.degree (sc _ _ g) _ rightWeight8_quartic_gate
    intro x; rw [g,eval_smul,odd8_eval,smul_eq_mul]; ring
  | prefix8 t α g => exact prefix8_no_profile J Pr.degree gd Pr.factor t α g

/-- Repeat clocks and signed or zero weights are unrestricted. -/
theorem explicit_finite_floor_field {s q ε:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) : 3*q+2*ε≤s := by
  by_contra! hh
  cases s with
  | zero =>
    have h := explicit_order_le_stages ha ho
    omega
  | succ s =>
    have S := saturated ha ho (by omega) he (by omega)
    let d:=ε-finrank K (back A b 0)
    have M : Margin A b q ε d := margin ha ho (by omega) he S
    obtain ⟨a,r,U,w,G,C⟩ := actual_chart ha ho hq he S M
    obtain ⟨w',P,C,Pr⟩ := physical_profile ha ho hq he S M C
    obtain ⟨u,v,J⟩ := actual_two_knots ha (by omega) S M C Pr
    apply Pr.nonzero
    rcases hq with e|e
    · subst q
      exact q8_no_profile C Pr J
    · subst q
      exact q9_no_profile J Pr.degree

end RKCert.Paired.FiniteMidpoint

namespace RKCert
open Paired Paired.FiniteMidpoint

/-- Characteristic-zero ERK order 16 requires at least 24 stages. -/
theorem explicit_order16_ge24_field {K:Type*} [Field K] [CharZero K] {s:ℕ}
    {A:Fin s→Fin s→K} {b:Vec K s} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 16) :
    24≤s := explicit_finite_floor_field (q:=8) (ε:=0) ha ho (by decide) (by decide)

theorem explicit_order16_ge24_charZero {R:Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 16) :
    24≤s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO=>explicit_order16_ge24_field hA hO) ha ho

/-- Characteristic-zero ERK order 17 requires at least 26 stages. -/
theorem explicit_order17_ge26_field {K:Type*} [Field K] [CharZero K] {s:ℕ}
    {A:Fin s→Fin s→K} {b:Vec K s} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 17) :
    26≤s := explicit_finite_floor_field (q:=8) (ε:=1) ha ho (by decide) (by decide)

theorem explicit_order17_ge26_charZero {R:Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 17) :
    26≤s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO=>explicit_order17_ge26_field hA hO) ha ho

/-- Characteristic-zero ERK order 18 requires at least 27 stages. -/
theorem explicit_order18_ge27_field {K:Type*} [Field K] [CharZero K] {s:ℕ}
    {A:Fin s→Fin s→K} {b:Vec K s} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 18) :
    27≤s := explicit_finite_floor_field (q:=9) (ε:=0) ha ho (by decide) (by decide)

theorem explicit_order18_ge27_charZero {R:Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 18) :
    27≤s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO=>explicit_order18_ge27_field hA hO) ha ho

/-- Characteristic-zero ERK order 19 requires at least 29 stages. -/
theorem explicit_order19_ge29_field {K:Type*} [Field K] [CharZero K] {s:ℕ}
    {A:Fin s→Fin s→K} {b:Vec K s} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 19) :
    29≤s := explicit_finite_floor_field (q:=9) (ε:=1) ha ho (by decide) (by decide)

theorem explicit_order19_ge29_charZero {R:Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 19) :
    29≤s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO=>explicit_order19_ge29_field hA hO) ha ho

end RKCert


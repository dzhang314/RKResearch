module

public import RKCert.RadauGridLift
public import RKCert.Dirk15SignatureAlgebra

@[expose] public section

/-! # Fixed left Radau Gram nonvanishing over every characteristic-zero field
The archived modular certificate tests the actual homogeneous, cleared
primitive form. Distinctness comes from divided differences, not a
field-wide reduction or a numerical grid assumption on the RK array. -/
namespace RKCert.FixedPolynomial.Radau77569
open Polynomial RKCert.Paired RKCert.Paired.Signature
open scoped Classical

variable {R : Type*} [CommRing R]

def clearedMomentThree (j : ℕ) (u a b c : R) : R :=
  ((420/(j+4):ℕ):R)*u^(j+4) - ((420/(j+3):ℕ):R)*(a+b+c)*u^(j+3)
    + ((420/(j+2):ℕ):R)*(a*b+a*c+b*c)*u^(j+2) - ((420/(j+1):ℕ):R)*a*b*c*u^(j+1)

def clearedGram (u a b c : R) : R :=
  clearedMomentThree 1 u a b c*clearedMomentThree 3 u a b c-(clearedMomentThree 2 u a b c)^2

theorem clearedGram_swap12 (u a b c : R) : clearedGram u a b c=clearedGram u b a c := by
  unfold clearedGram clearedMomentThree
  ring

theorem clearedGram_swap23 (u a b c : R) : clearedGram u a b c=clearedGram u a c b := by
  unfold clearedGram clearedMomentThree
  ring

theorem clearedMomentThree_scale (L u a b c : R) (j : ℕ) (hj : 1≤j) (hJ : j≤3) :
    clearedMomentThree j (L*u) (L*a) (L*b) (L*c)=L^(j+4)*clearedMomentThree j u a b c := by
  rcases (show j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl <;>
    simp only [clearedMomentThree] <;> ring

theorem clearedGram_scale (L u a b c : R) :
    clearedGram (L*u) (L*a) (L*b) (L*c)=L^12*clearedGram u a b c := by
  unfold clearedGram
  rw [clearedMomentThree_scale _ _ _ _ _ 1 (by decide) (by decide),
    clearedMomentThree_scale _ _ _ _ _ 3 (by decide) (by decide),
    clearedMomentThree_scale _ _ _ _ _ 2 (by decide) (by decide)]
  ring

theorem map_clearedGram {S : Type*} [CommRing S] (φ : R→+*S) (u a b c : R) :
    φ (clearedGram u a b c)=clearedGram (φ u) (φ a) (φ b) (φ c) := by
  simp only [clearedGram,clearedMomentThree,map_add,map_sub,map_mul,map_pow,map_natCast]

theorem any_order_mod_gram (u : Fin 7) (a b c : Fin 8)
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ha : a≠u.succ) (hb : b≠u.succ) (hc : c≠u.succ) :
    clearedGram (leftRoots u) (leftGrid a) (leftGrid b) (leftGrid c)≠0 := by
  have order : (a<b ∧ b<c) ∨ (a<c ∧ c<b) ∨ (b<a ∧ a<c) ∨
      (b<c ∧ c<a) ∨ (c<a ∧ a<b) ∨ (c<b ∧ b<a) := by omega
  have check (x y z : Fin 8) (hxy : x<y) (hyz : y<z)
      (hx : x≠u.succ) (hy : y≠u.succ) (hz : z≠u.succ) :
      clearedGram (leftRoots u) (leftGrid x) (leftGrid y) (leftGrid z)≠0 :=
    left_three_gram u x y z hxy hyz hx hy hz
  rcases order with ⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩
  · exact check a b c h h' ha hb hc
  · rw [clearedGram_swap23]; exact check a c b h h' ha hc hb
  · rw [clearedGram_swap12]; exact check b a c h h' hb ha hc
  · rw [clearedGram_swap12,clearedGram_swap23]; exact check b c a h h' hb hc ha
  · rw [clearedGram_swap23,clearedGram_swap12]; exact check c a b h h' hc ha hb
  · rw [clearedGram_swap12,clearedGram_swap23,clearedGram_swap12]; exact check c b a h h' hc hb ha

variable {K : Type*} [Field K] [CharZero K]

noncomputable def cubicFactor (a b c : K) : K[X] := (X-C a)*(X-C b)*(X-C c)

theorem clearedMomentThree_eq (u a b c : K) (j : ℕ) (hj : 1≤j) (hJ : j≤3) :
    clearedMomentThree j u a b c=(420:K)*paidMoment (cubicFactor a b c) u j := by
  let v : Fin 4 → K := ![-a*b*c,a*b+a*c+b*c,-(a+b+c),1]
  have form : cubicFactor a b c=ofFn 4 v := by
    rw [cubicFactor,ofFn_eq_sum_monomial]
    simp [v,Fin.sum_univ_succ,←C_mul_X_pow_eq_monomial]
    ring
  have deg : (cubicFactor a b c).natDegree≤3 := by
    rw [form]
    have h := ofFn_natDegree_lt (by decide : 1≤4) v
    omega
  have cof (i : Fin 4) : (cubicFactor a b c).coeff i.val=v i := by
    rw [form,ofFn_coeff_eq_val_of_lt _ i.isLt]
  rw [paidMoment,primitive_eval_power_mul _ _ _ deg]
  simp only [cof]
  rcases (show j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl <;>
    norm_num [clearedMomentThree,v,Fin.sum_univ_succ] <;> ring

private noncomputable def gramExpr : MvPolynomial (Option (Fin 4)) ℤ :=
  clearedGram (MvPolynomial.X (some 0)) (MvPolynomial.X (some 1))
    (MvPolynomial.X (some 2)) (MvPolynomial.X (some 3))

private theorem gramExpr_eval {R : Type*} [CommRing R] (z : Option (Fin 4)→R) :
    gramExpr.eval₂ (Int.castRingHom R) z =
      clearedGram (z (some 0)) (z (some 1)) (z (some 2)) (z (some 3)) := by
  change MvPolynomial.eval₂Hom (Int.castRingHom R) z gramExpr=_
  rw [gramExpr,map_clearedGram]
  simp only [MvPolynomial.eval₂Hom_X']

/-- Any three distinct missing left-Radau ports other than a nonzero
pivot yield a nonzero determinant of the two adjacent primitive equations. -/
theorem left_three_primitive_gram_ne (u a b c : K) (hu : u≠0)
    (hA : Function.Injective (![u,a,b,c] : Fin 4→K))
    (hRoot : ∀ i : Fin 4, (![u,a,b,c] : Fin 4→K) i=0 ∨
      (RKCert.Paired.radauLeft7 : K[X]).eval ((![u,a,b,c] : Fin 4→K) i)=0) :
    paidMoment (cubicFactor a b c) u 1*paidMoment (cubicFactor a b c) u 3-
      (paidMoment (cubicFactor a b c) u 2)^2≠0 := by
  intro hm
  let z : Fin 4→K := ![u,a,b,c]
  obtain ⟨Lift⟩ := exists_grid_lift z hRoot
  let S := Lift.specialization
  have hG : clearedGram u a b c=0 := by
    unfold clearedGram
    rw [clearedMomentThree_eq _ _ _ _ 1 (by decide) (by decide),
      clearedMomentThree_eq _ _ _ _ 2 (by decide) (by decide),
      clearedMomentThree_eq _ _ _ _ 3 (by decide) (by decide)]
    calc
      _ = (420:K)^2*(paidMoment (cubicFactor a b c) u 1*paidMoment (cubicFactor a b c) u 3-
        (paidMoment (cubicFactor a b c) u 2)^2) := by ring
      _ = _ := by rw [hm,mul_zero]
  have source : gramExpr.eval₂ (Int.castRingHom K) (scaledInput z)=0 := by
    rw [gramExpr_eval]
    change clearedGram (((-51480:ℤ):K)*u) (((-51480:ℤ):K)*a)
      (((-51480:ℤ):K)*b) (((-51480:ℤ):K)*c)=0
    rw [clearedGram_scale,hG,mul_zero]
  have target := S.preserves gramExpr source
  rw [gramExpr_eval] at target
  change clearedGram (Lift.specialization.image (some 0))
    (Lift.specialization.image (some 1)) (Lift.specialization.image (some 2))
    (Lift.specialization.image (some 3))=0 at target
  simp only [Lift.decoded] at target
  rw [←map_clearedGram] at target
  have reduced : clearedGram (scaledRoot (Lift.index 0)) (scaledRoot (Lift.index 1))
      (scaledRoot (Lift.index 2)) (scaledRoot (Lift.index 3))=0 :=
    S.embed.injective (by simpa only [map_zero] using target)
  have actual : clearedGram (leftGrid (Lift.index 0)) (leftGrid (Lift.index 1))
      (leftGrid (Lift.index 2)) (leftGrid (Lift.index 3))=0 := by
    unfold scaledRoot at reduced
    rw [clearedGram_scale] at reduced
    exact (mul_eq_zero.mp reduced).resolve_left (pow_ne_zero _ leading_mod_ne)
  have hDistinct : Function.Injective Lift.index :=
    fun i j e => by_contra (fun h => Lift.distinct i j (fun ee => h (hA ee)) e)
  obtain ⟨i,hi⟩ := Fin.exists_succ_eq_of_ne_zero (Lift.nonorigin 0 hu)
  rw [←hi] at actual
  have hMod := any_order_mod_gram i (Lift.index 1) (Lift.index 2) (Lift.index 3)
    (fun h => (by decide : (1:Fin 4)≠2) (hDistinct h))
    (fun h => (by decide : (1:Fin 4)≠3) (hDistinct h))
    (fun h => (by decide : (2:Fin 4)≠3) (hDistinct h))
    (fun h => (by decide : (1:Fin 4)≠0) (hDistinct (h.trans hi)))
    (fun h => (by decide : (2:Fin 4)≠0) (hDistinct (h.trans hi)))
    (fun h => (by decide : (3:Fin 4)≠0) (hDistinct (h.trans hi)))
  exact hMod actual

end RKCert.FixedPolynomial.Radau77569

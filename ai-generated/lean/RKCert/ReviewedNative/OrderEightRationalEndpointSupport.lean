module

public import Mathlib.Data.Rat.Lemmas
public import RKResearch.OrderConditions
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section

/-! A rational order-eight rule cannot be carried by five given rational
sites if one of the sites is 0. This file checks the essential split-quartic
obstruction by reduction modulo seven. The rational moments obtained
by integrating the nodal polynomial are explicitly stated. -/

namespace RKResearch.Certified.OrderEightRationalEndpointSupport

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := ZMod 7
private def Ok (x : ℚ) : Prop := ¬ 7 ∣ x.den

private lemma ok_iff (x : ℚ) : Ok x ↔ (x.den : K) ≠ 0 := by
  unfold Ok
  exact (not_congr (ZMod.natCast_eq_zero_iff x.den 7)).symm

private lemma ok_add {a b : ℚ} (ha : Ok a) (hb : Ok b) : Ok (a+b) := by
  intro hc
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp
    (dvd_trans hc (Rat.add_den_dvd a b)) with h | h
  · exact ha h
  · exact hb h

private lemma ok_mul {a b : ℚ} (ha : Ok a) (hb : Ok b) : Ok (a*b) := by
  intro hc
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp
    (dvd_trans hc (Rat.mul_den_dvd a b)) with h | h
  · exact ha h
  · exact hb h

private lemma ok_neg {a : ℚ} (ha : Ok a) : Ok (-a) := by
  simpa only [Ok,Rat.neg_den] using ha

private def loc : Subring ℚ where
  carrier := {x | Ok x}
  zero_mem' := by change ¬ 7 ∣ (0:ℚ).den; decide
  one_mem' := by change ¬ 7 ∣ (1:ℚ).den; decide
  add_mem' := ok_add
  mul_mem' := ok_mul
  neg_mem' := ok_neg

private def red : loc →+* K where
  toFun x := (x.val : K)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := Rat.cast_add_of_ne_zero ((ok_iff _).mp a.prop) ((ok_iff _).mp b.prop)
  map_mul' a b := Rat.cast_mul_of_ne_zero ((ok_iff _).mp a.prop) ((ok_iff _).mp b.prop)

private lemma num_unit {x : ℚ} (hx : 7 ∣ x.den) : (x.num : K) ≠ 0 := by
  intro hz
  have hn : 7 ∣ x.num.natAbs := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 7).mp hz
    exact (Int.natCast_dvd_natCast.mp ((Int.dvd_natAbs).mpr h))
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 7) hn hx x.reduced

private lemma inv_reduces_zero {x : ℚ} (hx : 7 ∣ x.den) :
    Ok x⁻¹ ∧ (x⁻¹ : ℚ) = x⁻¹ ∧ ((x⁻¹ : ℚ) : K) = 0 := by
  have hn := num_unit hx
  have hnum : x.num ≠ 0 := fun h => hn (by simp [h])
  have hnot : ¬ 7 ∣ x.num.natAbs := by
    intro h
    apply hn
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 7).mpr
      ((Int.dvd_natAbs).mp (Int.natCast_dvd_natCast.mpr h))
  refine ⟨?_, rfl, ?_⟩
  · simp [Ok,Rat.den_inv,hnum,hnot]
  · rw [Rat.cast_inv_of_ne_zero hn, Rat.cast_def,
      (ZMod.natCast_eq_zero_iff _ _).mpr hx, div_zero, inv_zero]

private def P (r x : ℚ) : ℚ :=
  70*x^4-70*r*x^3+(120*r-150)*x^2+(100-60*r)*x+(8*r-15)

private def C (rN rD xN xD : ℤ) : ℤ :=
  70*rD*xN^4-70*rN*xN^3*xD+(120*rN-150*rD)*xN^2*xD^2
    +(100*rD-60*rN)*xN*xD^3+(8*rN-15*rD)*xD^4

private theorem clear {r x : ℚ} (h : P r x = 0) :
    C r.num (r.den : ℤ) x.num (x.den : ℤ) = 0 := by
  have hr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hx : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hc : (C r.num (r.den : ℤ) x.num (x.den : ℤ) : ℚ) =
      (r.den : ℚ) * (x.den : ℚ)^4 * P r x := by
    unfold C
    push_cast
    conv_rhs =>
      arg 2
      rw [← r.num_div_den, ← x.num_div_den]
      unfold P
    field_simp [hr, hx]
  rw [h, mul_zero] at hc
  exact_mod_cast hc

private theorem root_ok_of_ok {r x : ℚ} (hr : Ok r) (h : P r x = 0) : Ok x := by
  intro hdiv
  have hnorm := num_unit hdiv
  obtain ⟨n,hn⟩ := hdiv
  have h1 := clear h
  rw [hn, Nat.cast_mul, Nat.cast_ofNat] at h1
  let g : ℤ := -10*r.num*x.num^3*n +
    (120*r.num-150*r.den)*x.num^2*n^2 +
    7*(100*r.den-60*r.num)*x.num*n^3+
    49*(8*r.num-15*r.den)*n^4
  have h2 : (7:ℤ)*(10*(r.den:ℤ)*x.num^4+7*g)=0 := by
    unfold C at h1
    dsimp [g]
    linear_combination h1
  have h3 := (mul_eq_zero.mp h2).resolve_left (by decide)
  have h4 := congrArg (fun z : ℤ => (z:K)) h3
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_pow,Int.cast_zero] at h4
  have hz : (7:K)=0 := by decide
  rw [hz,zero_mul, add_zero] at h4
  exact mul_ne_zero (mul_ne_zero (by decide) ((ok_iff r).mp hr))
    (pow_ne_zero _ hnorm) h4

private theorem root_bad_of_bad {r x : ℚ} (hr : ¬Ok r) (h : P r x = 0) : ¬Ok x := by
  intro hx
  have hdiv : 7 ∣ r.den := Classical.not_not.mp (show ¬¬7 ∣ r.den from hr)
  have hrd : (r.den : K) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hnu := num_unit hdiv
  have he := congrArg (fun z : ℤ => (z:K)) (clear h)
  unfold C at he
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_pow,Int.cast_zero] at he
  have h70 : (70:K)=0 := by decide
  have h120 : (120:K)=1 := by decide
  have hm60 : (60:K)=-3 := by decide
  have h8 : (8:K)=1 := by decide
  rw [hrd,h70,h120,hm60,h8] at he
  have he' : (r.num:K) * (x.den:K)^2 *
      ((x.num:K)^2+3*(x.num:K)*(x.den:K)+(x.den:K)^2)=0 := by
    linear_combination he
  have hq : ∀ a b : K, b ≠ 0 → a^2+3*a*b+b^2 ≠ 0 := by decide +kernel
  have hden := (ok_iff x).mp hx
  exact mul_ne_zero (mul_ne_zero hnu (pow_ne_zero _ hden)) (hq _ _ hden) he'

def r1 (a b c d : ℚ) := a+b+c+d
def r2 (a b c d : ℚ) := a*b+a*c+a*d+b*c+b*d+c*d
def r3 (a b c d : ℚ) := -(a*b*c+a*b*d+a*c*d+b*c*d)
def r4 (a b c d : ℚ) := a*b*c*d

/-- The one-parameter quartic forced by three paid nodal moments
does not split into rational linear factors. -/
theorem no_split_moment_quartic (a b c d : ℚ)
    (hs : 7*r2 a b c d=12*r1 a b c d-15)
    (ht : 7*r3 a b c d=10-6*r1 a b c d)
    (hu : 70*r4 a b c d=8*r1 a b c d-15) : False := by
  let r := r1 a b c d
  let s := r2 a b c d
  let t := r3 a b c d
  let u := r4 a b c d
  have rid (x : ℚ) :
      P r x = 70*((x-a)*(x-b)*(x-c)*(x-d)) := by
    unfold P
    dsimp [r,r1] at *
    simp only [r2,r3,r4] at hs ht hu
    linear_combination -10*x^2*hs -10*x*ht - hu
  have ha : P r a=0 := by simp [rid]
  have hb : P r b=0 := by simp [rid]
  have hc : P r c=0 := by simp [rid]
  have hd : P r d=0 := by simp [rid]
  by_cases hr : Ok r
  · let aa : loc := ⟨a, root_ok_of_ok hr ha⟩
    let bb : loc := ⟨b, root_ok_of_ok hr hb⟩
    let cc : loc := ⟨c, root_ok_of_ok hr hc⟩
    let dd : loc := ⟨d, root_ok_of_ok hr hd⟩
    let rr : loc := ⟨r,hr⟩
    let ss := aa*bb+aa*cc+aa*dd+bb*cc+bb*dd+cc*dd
    let tt := -(aa*bb*cc+aa*bb*dd+aa*cc*dd+bb*cc*dd)
    have Hs : 7*ss=12*rr-15 := Subtype.ext hs
    have Ht : 7*tt=10-6*rr := Subtype.ext ht
    have hS := congrArg red Hs
    have hT := congrArg red Ht
    simp only [map_mul,map_sub,map_ofNat] at hS hT
    have hz : (7:K)=0 := by decide
    rw [hz,zero_mul] at hS hT
    have hbad : (5:K)=0 := by linear_combination -hS-2*hT
    exact (by decide : (5:K)≠0) hbad
  · have br := Classical.not_not.mp (show ¬¬7 ∣ r.den from hr)
    have ba := Classical.not_not.mp (show ¬¬7 ∣ a.den from root_bad_of_bad hr ha)
    have bb := Classical.not_not.mp (show ¬¬7 ∣ b.den from root_bad_of_bad hr hb)
    have bc := Classical.not_not.mp (show ¬¬7 ∣ c.den from root_bad_of_bad hr hc)
    have bd := Classical.not_not.mp (show ¬¬7 ∣ d.den from root_bad_of_bad hr hd)
    let rr : loc := ⟨r⁻¹,(inv_reduces_zero br).1⟩
    let aa : loc := ⟨a⁻¹,(inv_reduces_zero ba).1⟩
    let ab : loc := ⟨b⁻¹,(inv_reduces_zero bb).1⟩
    let ac : loc := ⟨c⁻¹,(inv_reduces_zero bc).1⟩
    let ad : loc := ⟨d⁻¹,(inv_reduces_zero bd).1⟩
    let v := aa*ab+aa*ac+aa*ad+ab*ac+ab*ad+ac*ad
    have nz (z : ℚ) (hz : 7 ∣ z.den) : z ≠ 0 := by
      rintro rfl
      exact (by decide : ¬ 7 ∣ (0:ℚ).den) hz
    let vQ := a⁻¹*b⁻¹+a⁻¹*c⁻¹+a⁻¹*d⁻¹+b⁻¹*c⁻¹+b⁻¹*d⁻¹+c⁻¹*d⁻¹
    have hs70 : 70*s=120*r-150 := by dsimp [s,r]; linear_combination 10*hs
    have hh : (8-15*rr)*v=120-150*rr := by
      apply Subtype.ext
      change (8-15*r⁻¹)*vQ = 120-150*r⁻¹
      have hmul : (8*r-15)*vQ = 120*r-150 := by
        rw [← show 70*u = 8*r-15 from hu, ← hs70]
        dsimp [u,s,r2,r4,vQ]
        field_simp [nz a ba,nz b bb,nz c bc,nz d bd]
        ring
      have he : r*r⁻¹=1 := mul_inv_cancel₀ (nz r br)
      linear_combination r⁻¹*hmul - (8*vQ-120)*he
    have h := congrArg red hh
    simp only [map_mul,map_sub,map_add,map_ofNat,v] at h
    have er : red rr=0 := (inv_reduces_zero br).2.2
    have ea : red aa=0 := (inv_reduces_zero ba).2.2
    have eb : red ab=0 := (inv_reduces_zero bb).2.2
    have ec : red ac=0 := (inv_reduces_zero bc).2.2
    have ed : red ad=0 := (inv_reduces_zero bd).2.2
    have hbad : (0:K)=120 := by simpa only [er,ea,eb,ec,ed,mul_zero,zero_mul,add_zero,sub_zero] using h
    exact (by decide : (0:K)≠120) hbad

/-- A polynomial split over the four nonzero-site candidates cannot
annihilate the three order-eight nodal moments once the fifth site is zero.
Repetitions of the four sites are harmless to the algebraic statement. -/
theorem no_five_site_nodal_moments (a b c d : ℚ)
    (h0 : 1/6-r1 a b c d/5+r2 a b c d/4+r3 a b c d/3+r4 a b c d/2=0)
    (h1 : 1/7-r1 a b c d/6+r2 a b c d/5+r3 a b c d/4+r4 a b c d/3=0)
    (h2 : 1/8-r1 a b c d/7+r2 a b c d/6+r3 a b c d/5+r4 a b c d/4=0) : False := by
  apply no_split_moment_quartic a b c d
  · linear_combination 1260*h0-5040*h1+4200*h2
  · linear_combination -1680*h0+6300*h1-5040*h2
  · linear_combination 5040*h0-16800*h1+12600*h2

open scoped Matrix

/-- Direct reviewed-quadrature consequence. Zero-weight stages may
lie anywhere. All nonzero weights must be at one of the five listed
sites (repetitions among the sites are allowed). -/
theorem no_order_eight_on_five_sites {ι : Type*} [Fintype ι]
    (b c : ι → ℚ) (a₁ a₂ a₃ a₄ : ℚ)
    (h : RKResearch.HasQuadratureOrder 8 b c)
    (hs : ∀ i, b i=0 ∨ c i=0 ∨ c i=a₁ ∨ c i=a₂ ∨ c i=a₃ ∨ c i=a₄) : False := by
  let r := r1 a₁ a₂ a₃ a₄
  let s := r2 a₁ a₂ a₃ a₄
  let t := r3 a₁ a₂ a₃ a₄
  let u := r4 a₁ a₂ a₃ a₄
  let m (k : Nat) := ∑ i, b i * (c i)^k
  have hmem (k : Nat) (hk : k<8) : m k=1/((k:ℚ)+1) := by
    have he : ((k:ℚ)+1)*m k=1 := by
      simpa only [m,dotProduct,Pi.pow_apply,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using h k hk
    have hp : (k:ℚ)+1 ≠ 0 := by positivity
    apply (eq_div_iff hp).mpr
    rw [mul_comm]
    exact he
  have hv (k:Nat) : m (k+5)-r*m (k+4)+s*m (k+3)+t*m (k+2)+u*m (k+1)=0 := by
    dsimp [m]
    simp only [Finset.mul_sum, ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have he : b i*c i^(k+5)-r*(b i*c i^(k+4))+s*(b i*c i^(k+3))+
        t*(b i*c i^(k+2))+u*(b i*c i^(k+1)) =
          b i*c i^(k+1)*((c i-a₁)*(c i-a₂)*(c i-a₃)*(c i-a₄)) := by
      simp only [pow_add]
      dsimp [r,s,t,u,r1,r2,r3,r4]
      ring
    rw [he]
    rcases hs i with hz|hz|hz|hz|hz|hz <;> simp [hz]
  apply no_five_site_nodal_moments a₁ a₂ a₃ a₄
  · have h0 := hv 0
    norm_num at h0
    rw [hmem 5 (by decide),hmem 4 (by decide),hmem 3 (by decide),
      hmem 2 (by decide),hmem 1 (by decide)] at h0
    norm_num [div_eq_mul_inv,r,s,t,u] at h0 ⊢
    exact h0
  · have h1 := hv 1
    norm_num at h1
    rw [hmem 6 (by decide),hmem 5 (by decide),hmem 4 (by decide),
      hmem 3 (by decide),hmem 2 (by decide)] at h1
    norm_num [div_eq_mul_inv,r,s,t,u] at h1 ⊢
    exact h1
  · have h2 := hv 2
    norm_num at h2
    rw [hmem 7 (by decide),hmem 6 (by decide),hmem 5 (by decide),
      hmem 4 (by decide),hmem 3 (by decide)] at h2
    norm_num [div_eq_mul_inv,r,s,t,u] at h2 ⊢
    exact h2

end RKResearch.Certified.OrderEightRationalEndpointSupport

#print axioms RKResearch.Certified.OrderEightRationalEndpointSupport.no_five_site_nodal_moments

#print axioms RKResearch.Certified.OrderEightRationalEndpointSupport.no_order_eight_on_five_sites

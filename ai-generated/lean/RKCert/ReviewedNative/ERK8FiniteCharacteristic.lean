module

public import RKCert.ReviewedNative.ERK8CVQuadraticCertificate
public import RKCert.ReviewedNative.ERK8ShanksQuadraticCertificate
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Combining the Cooper–Verner and Shanks charts in positive characteristic.
The product factor at powers of 41 is accompanied by an elementary
constructive lift of the root 12 of X²−21. No étale root descent to an
arbitrary characteristic-zero coefficient ring is claimed. -/

namespace RKResearch.Certified.ERK8FiniteCharacteristic
open FiniteRootedTree
open scoped Matrix

def bush := leaf.addBush 8

/-- A unit (not just nonzero) ninth-order defect survives every
specialization into a nontrivial ring. Its multiplier is part of the data. -/
structure W (R : Type*) [CommRing R] (n : Nat) where
  A : Matrix (Fin n) (Fin n) R
  b : Fin n → R
  explicit : ERK A
  paid : HasOrder 8 A b
  u : R
  fail : u*((bush.factorial:R)*(b ⬝ᵥ Φ bush A)-1) = 1

variable {R S : Type*} [CommRing R] [CommRing S] {n : Nat}

theorem W.noNine [Nontrivial R] (x : W R n) : ¬HasOrder 9 x.A x.b := by
  intro h
  have ht : (bush.order:Nat) ≤ 9 := by decide
  simpa only [h bush ht, sub_self, mul_zero, zero_ne_one] using x.fail

def W.map (x : W R n) (f : R →+* S) : W S n where
  A := x.A.map f
  b := f ∘ x.b
  explicit := by intro i j h; change f (x.A i j) = 0; rw [x.explicit h, map_zero]
  paid := x.paid.map f
  u := f x.u
  fail := by
    have h := congrArg f x.fail
    simpa only [map_mul,map_sub,map_one,map_natCast,RingHom.map_dotProduct,map_Φ] using h

private theorem fst_hom (z : R × S) : z.1 = (RingHom.fst R S) z := rfl
private theorem snd_hom (z : R × S) : z.2 = (RingHom.snd R S) z := rfl

def W.prod (x : W R n) (y : W S n) : W (R × S) n where
  A := Matrix.of fun i j => (x.A i j, y.A i j)
  b := fun i => (x.b i,y.b i)
  explicit := by intro i j hij; exact Prod.ext (x.explicit hij) (y.explicit hij)
  paid := by
    intro t ht
    apply Prod.ext
    · rw [fst_hom]
      rw [map_mul,map_natCast,RingHom.map_dotProduct,map_Φ]
      exact x.paid t ht
    · rw [snd_hom]
      rw [map_mul,map_natCast,RingHom.map_dotProduct,map_Φ]
      exact y.paid t ht
  u := (x.u,y.u)
  fail := by
    apply Prod.ext
    · rw [fst_hom]
      rw [map_mul,map_sub,map_one,map_mul,map_natCast,RingHom.map_dotProduct,map_Φ]
      exact x.fail
    · rw [snd_hom]
      rw [map_mul,map_sub,map_one,map_mul,map_natCast,RingHom.map_dotProduct,map_Φ]
      exact y.fail

def padA (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.of (Fin.lastCases 0 (fun i => Fin.lastCases 0 (A i)))

def padb (b : Fin n → R) : Fin (n+1) → R := Fin.lastCases 0 b

theorem phi_pad (A : Matrix (Fin n) (Fin n) R) (t : FiniteRootedTree) (i : Fin n) :
    Φ t (padA A) i.castSucc = Φ t A i := by
  induction t generalizing i with
  | leaf => rfl
  | butcherProduct u v iu iv =>
    change Φ u (padA A) i.castSucc * _ = Φ u A i * _
    rw [iu, Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_castSucc]
    have h1 (j : Fin n) : padA A i.castSucc j.castSucc = A i j := by simp [padA]
    have h0 : padA A i.castSucc (Fin.last n) = 0 := by simp [padA]
    simp only [h1,h0,zero_mul,add_zero,iv]

theorem read_pad (b : Fin n → R) (A : Matrix (Fin n) (Fin n) R) (t : FiniteRootedTree) :
    padb b ⬝ᵥ Φ t (padA A) = b ⬝ᵥ Φ t A := by
  simp only [dotProduct,Fin.sum_univ_castSucc,padb,Fin.lastCases_castSucc,Fin.lastCases_last,
    zero_mul,add_zero,phi_pad]

def W.pad (x : W R n) : W R (n+1) where
  A := padA x.A
  b := padb x.b
  explicit := by
    intro i j hij
    induction i using Fin.lastCases with
    | last => simp [padA,Matrix.of_apply]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [padA,Matrix.of_apply]
      | cast j =>
        simpa [padA,Matrix.of_apply] using x.explicit (Fin.castSucc_le_castSucc_iff.mp hij)
  paid := by intro t ht; rw [read_pad]; exact x.paid t ht
  u := x.u
  fail := by rw [read_pad]; exact x.fail

def cv {s d : R} (hs : s*s=21) (hd : (282240 : R)*d=1) : W R 11 where
  A := _
  b := _
  explicit := ERK8CVQuadraticCertificate.explicit s d
  paid := ERK8CVQuadraticCertificate.order_eight (s:=s) (by simpa only [Int.cast_ofNat] using hs)
    d (by simpa only [ERK8CVQuadraticCertificate.D,Int.cast_ofNat] using hd)
  u := 3920
  fail := ERK8CVQuadraticCertificate.ninth_defect (s:=s) (by simpa only [Int.cast_ofNat] using hs)
    d (by simpa only [ERK8CVQuadraticCertificate.D,Int.cast_ofNat] using hd)

def shanks {d : R} (hd : (139482000 : R)*d=1) : W R 12 where
  A := _
  b := _
  explicit := ERK8ShanksQuadraticCertificate.explicit 0 d
  paid := ERK8ShanksQuadraticCertificate.order_eight (s:=0) (by simp)
    d (by simpa only [ERK8ShanksQuadraticCertificate.D,Int.cast_ofNat] using hd)
  u := 4320
  fail := ERK8ShanksQuadraticCertificate.ninth_defect (s:=0) (by simp)
    d (by simpa only [ERK8ShanksQuadraticCertificate.D,Int.cast_ofNat] using hd)

/-- Integral linear-precision lifting by x ↦ x−12(x²−21). The factor
1−24x+144(x²−21) is a multiple of 41 when x is 12 modulo 41. -/
theorem lift41 (k : Nat) : ∃ a z : Int,
    (12+41*a)*(12+41*a)-21 = (41:Int)^k*z := by
  induction k with
  | zero => exact ⟨0,123,by decide⟩
  | succ k ih =>
    obtain ⟨a,z,hz⟩ := ih
    let H := 3+24*a+41*a*a
    refine ⟨a-12*H, z*(-7-24*a+144*H), ?_⟩
    rw [pow_succ]
    calc
      _ = ((12+41*a)*(12+41*a)-21)*(41*(-7-24*a+144*H)) := by dsimp [H]; ring
      _ = _ := by rw [hz]; ring

theorem square21_41power (k : Nat) : ∃ s : ZMod (41^k), s*s=21 := by
  obtain ⟨a,z,hz⟩ := lift41 k
  let x : Int := 12+41*a
  have hx : x*x-21 = (41:Int)^k*z := hz
  refine ⟨(x : ZMod (41^k)), ?_⟩
  have heq := congrArg (fun y : Int => (y : ZMod (41^k))) hx
  have hp : (41:ZMod (41^k))^k=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (41^k)
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,hp,zero_mul,sub_eq_zero] using heq

private theorem decompose (v : Nat) (hv : 0<v) :
    ∃ k m : Nat, ¬41∣m ∧ v=41^k*m := by
  induction v using Nat.strong_induction_on
  next v ih =>
    by_cases h : 41∣v
    · obtain ⟨m,hm⟩ := h
      have hm0 : 0<m := by omega
      have hlt : m<v := by omega
      obtain ⟨k,l,hl,he⟩ := ih m hlt hm0
      exact ⟨k+1,l,hl,by rw [hm,he,pow_succ]; ring⟩
    · exact ⟨0,v,h,by simp⟩

theorem zmod_witness (v : Nat) (hv : 0<v) (hpaid : Nat.Coprime 210 v) :
    Nonempty (W (ZMod v) 12) := by
  obtain ⟨k,m,hm,he⟩ := decompose v hv
  subst v
  have hc : Nat.Coprime 41 m := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hm
  have cA : Nat.Coprime 282240 (41^k) := (by decide : Nat.Coprime 282240 41).pow_right k
  have cB : Nat.Coprime 139482000 m := by
    apply Nat.Coprime.of_dvd_left (show 139482000 ∣ (210^8)*41 by decide)
    exact ((hpaid.coprime_dvd_right (dvd_mul_left m (41^k))).pow_left 8).mul_left hc
  obtain ⟨s,hs⟩ := square21_41power k
  let a := cv (s:=s) hs (ZMod.coe_mul_inv_eq_one 282240 cA)
  let b := shanks (ZMod.coe_mul_inv_eq_one 139482000 cB)
  exact ⟨(a.pad.prod b).map (ZMod.chineseRemainder (hc.pow_left k)).symm.toRingHom⟩

/-- The characteristic is allowed to be composite, and R may have nilpotents.
The condition Coprime 210 v is precisely factorial-admissibility in
positive characteristic. -/
theorem twelve_positive_characteristic (v : Nat) [CharP R v] (hv : 0<v)
    (hpaid : Nat.Coprime 210 v) : Nonempty (W R 12) := by
  obtain ⟨w⟩ := zmod_witness v hv hpaid
  exact ⟨w.map (ZMod.castHom (dvd_refl v) R)⟩

/-- A natural number that is invertible in a positive-characteristic
ring must already be a unit in its finite prime subring. -/
theorem coprime_of_isUnit {a v : Nat} [CharP R v] (hv : 0<v)
    (ha : IsUnit (a:R)) : Nat.Coprime a v := by
  let g := Nat.gcd a v
  have hg : IsUnit (g:R) := isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.gcd_dvd_left a v)) ha
  obtain ⟨t,hv'⟩ := Nat.gcd_dvd_right a v
  change v = g*t at hv'
  have ht0 : 0<t := by
    by_contra! hh
    have : t=0 := by omega
    simp [this] at hv'
    omega
  have hr : (g:R)*(t:R)=0 := by
    rw [←Nat.cast_mul,←hv']
    exact (CharP.cast_eq_zero_iff R v v).mpr dvd_rfl
  have ht := (CharP.cast_eq_zero_iff R v t).mp (hg.mul_right_eq_zero.mp hr)
  have hle := Nat.le_of_dvd ht0 ht
  have hgpos : 0<g := Nat.gcd_pos_of_pos_right _ hv
  change g=1
  by_contra! hn
  have hlt : 1*t < g*t := Nat.mul_lt_mul_of_pos_right (by omega) ht0
  rw [one_mul,←hv'] at hlt
  omega

/-- Twelve stages always suffice whenever positive characteristic admits an
order-eight method at all. Nontrivial rings obtain exact, not just paid, order. -/
theorem positive_characteristic_factorial (v : Nat) [CharP R v] (hv : 0<v)
    (h : IsUnit (Nat.factorial 8 : R)) : Nonempty (W R 12) := by
  apply twelve_positive_characteristic v hv
  apply coprime_of_isUnit (R:=R) hv
  exact isUnit_of_dvd_unit (Nat.cast_dvd_cast (show 210 ∣ Nat.factorial 8 by decide)) h

/-- No order, completeness, or algebraic closure of the field is needed. -/
theorem all_fields_factorial (K : Type*) [Field K]
    (h : IsUnit (Nat.factorial 8 : K)) : Nonempty (W K 12) := by
  by_cases hc : ringChar K = 0
  · let : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp hc
    have hd : (139482000 : K) ≠ 0 := by norm_num
    exact ⟨shanks (mul_inv_cancel₀ hd)⟩
  · exact positive_characteristic_factorial (ringChar K) (Nat.pos_of_ne_zero hc) h

end RKResearch.Certified.ERK8FiniteCharacteristic

#print axioms RKResearch.Certified.ERK8FiniteCharacteristic.twelve_positive_characteristic

#print axioms RKResearch.Certified.ERK8FiniteCharacteristic.positive_characteristic_factorial
#print axioms RKResearch.Certified.ERK8FiniteCharacteristic.all_fields_factorial

module

public import RKCert.ERKGoodPrimeDense
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Prime residues as plain natural numbers for certificate checking -/
namespace RKCert.GoodPrimeDense

def intResidue (p : ℕ) (a : ℤ) : ℕ := (a % (p:ℤ)).toNat

def naturalPrime (p : ℕ) : Operations ℕ :=
  ⟨0,intResidue p,fun a b=>(a+b)%p,fun a b=>(a*b)%p,
    fun a => intResidue p (-(a:ℤ)),fun a => decide (a=0)⟩

variable {R : Type*} [CommRing R] {p : ℕ} [CharP R p]

theorem intResidue_cast (pn : p≠0) (a : ℤ) : (intResidue p a:R) = (a:R) := by
  have nag : 0 ≤ a % (p:ℤ) := Int.emod_nonneg a (Int.ofNat_ne_zero.mpr pn)
  have z := congrArg (Int.castRingHom R) (Int.emod_add_mul_ediv a (p:ℤ))
  have pzero : ((p:ℕ):R)=0 := CharP.cast_eq_zero R p
  unfold intResidue
  rw [←Int.cast_natCast,Int.toNat_of_nonneg nag]
  simpa only [map_add,map_mul,Int.coe_castRingHom,Int.cast_natCast,pzero,zero_mul,add_zero] using z

theorem Sound.naturalPrime (pn : p≠0) :
    Sound (naturalPrime p) (fun n : ℕ => (n:R)) where
  zero := Nat.cast_zero
  int := intResidue_cast pn
  add a b := by
    change ((a+b)%p:ℕ) = (_:R)
    rw [←CharP.cast_eq_mod R p,Nat.cast_add]
  mul a b := by
    change ((a*b)%p:ℕ) = (_:R)
    rw [←CharP.cast_eq_mod R p,Nat.cast_mul]
  neg a := by
    change (intResidue p (-(a:ℤ)):R) = -(a:R)
    rw [intResidue_cast pn,Int.cast_neg,Int.cast_natCast]
  isZero a h := by
    have z : a=0 := of_decide_eq_true h
    simp [z]

end RKCert.GoodPrimeDense

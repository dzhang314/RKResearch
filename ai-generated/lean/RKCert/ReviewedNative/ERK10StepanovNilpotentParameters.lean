module

public import RKCert.ReviewedNative.ERK10StepanovLiterals
public import RKCert.ReviewedNative.NilpotentSquareRootLift
import Mathlib.Tactic.Ring

@[expose] public section

/-! The prime-field root triples also lift through arbitrary nilpotent
37 or 227. The coefficient ring need not be a local ring, reduced,
complete, ordered, or a field. -/

namespace RKResearch.Certified.ERK10Stepanov
open ERKNestedRadicalReplay

structure RootResidues (p : ℤ) where
  X : ℤ
  Y : ℤ
  Z : ℤ
  inverseX : ℤ
  inverseY : ℤ
  inverseZ : ℤ
  inverseD : ℤ
  rootX : p ∣ X*X-3
  rootY : p ∣ Y*Y-7
  rootZ : p ∣ Z*Z-(147+42*Y)
  unitX : p ∣ 2*X*inverseX-1
  unitY : p ∣ 2*Y*inverseY-1
  unitZ : p ∣ 2*Z*inverseZ-1
  unitD : p ∣ D*inverseD-1

def rootResidues37 : RootResidues 37 where
  X := 22
  Y := 28
  Z := 19
  inverseX := 16
  inverseY := 2
  inverseZ := 1
  inverseD := 30
  rootX := by decide +kernel
  rootY := by decide +kernel
  rootZ := by decide +kernel
  unitX := by decide +kernel
  unitY := by decide +kernel
  unitZ := by decide +kernel
  unitD := by decide +kernel

def rootResidues227 : RootResidues 227 where
  X := 177
  Y := 190
  Z := 149
  inverseX := 143
  inverseY := 46
  inverseZ := 16
  inverseD := 64
  rootX := by decide +kernel
  rootY := by decide +kernel
  rootZ := by decide +kernel
  unitX := by decide +kernel
  unitY := by decide +kernel
  unitZ := by decide +kernel
  unitD := by decide +kernel

theorem lift_root_residues {R : Type*} [CommRing R] [Nontrivial R] {p : ℤ}
    (r : RootResidues p) (hp : IsNilpotent (p:R)) :
    ∃ x y z : R, Roots x y z ∧ IsUnit (D:R) := by
  let I : Ideal R := Ideal.span ({(p:R)}:Set R)
  have hI : ∀ a ∈ I, IsNilpotent a := by
    intro a ha
    obtain ⟨v,hv⟩ := Ideal.mem_span_singleton.mp ha
    obtain ⟨n,hn⟩ := hp
    exact ⟨n,by rw [hv,mul_pow,hn,zero_mul]⟩
  have hcast (a : ℤ) (h : p∣a) : (a:R)∈I := by
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨v,rfl⟩ := h
    exact ⟨(v:R),by rw [Int.cast_mul]⟩
  have hu (a e : ℤ) (h : p ∣ a*e-1) : IsUnit (a:R) := by
    have ht : (a:R)*(e:R)-1∈I := by
      simpa only [Int.cast_mul,Int.cast_sub,Int.cast_one] using hcast _ h
    have hh := (hI _ ht).isUnit_add_one
    rw [sub_add_cancel] at hh
    exact isUnit_of_mul_isUnit_left hh
  have hxU : IsUnit ((2:R)*(r.X:R)) := by
    simpa only [Int.cast_mul,Int.cast_ofNat] using hu (2*r.X) r.inverseX r.unitX
  have hyU : IsUnit ((2:R)*(r.Y:R)) := by
    simpa only [Int.cast_mul,Int.cast_ofNat] using hu (2*r.Y) r.inverseY r.unitY
  have hzU : IsUnit ((2:R)*(r.Z:R)) := by
    simpa only [Int.cast_mul,Int.cast_ofNat] using hu (2*r.Z) r.inverseZ r.unitZ
  have hxI : (r.X:R)*(r.X:R)-3∈I := by
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_ofNat] using hcast _ r.rootX
  have hyI : (r.Y:R)*(r.Y:R)-7∈I := by
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_ofNat] using hcast _ r.rootY
  obtain ⟨x,hx,-⟩ := sqrt_lift_nilpotent_ideal I hI 3 (r.X:R) hxI hxU
  obtain ⟨y,hy,hyClose⟩ := sqrt_lift_nilpotent_ideal I hI 7 (r.Y:R) hyI hyU
  have hzI : (r.Z:R)*(r.Z:R)-(147+42*(r.Y:R))∈I := by
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_sub,Int.cast_ofNat] using hcast _ r.rootZ
  have hzI' : (r.Z:R)*(r.Z:R)-(147+42*y)∈I := by
    have hzEq : (r.Z:R)*(r.Z:R)-(147+42*y) =
        ((r.Z:R)*(r.Z:R)-(147+42*(r.Y:R))) - 42*(y-(r.Y:R)) := by ring
    rw [hzEq]
    exact I.sub_mem hzI (I.mul_mem_left 42 hyClose)
  obtain ⟨z,hz,-⟩ := sqrt_lift_nilpotent_ideal I hI (147+42*y) (r.Z:R) hzI' hzU
  exact ⟨x,y,z,⟨hx,hy,hz⟩,hu D r.inverseD r.unitD⟩

end RKResearch.Certified.ERK10Stepanov

#print axioms RKResearch.Certified.ERK10Stepanov.lift_root_residues

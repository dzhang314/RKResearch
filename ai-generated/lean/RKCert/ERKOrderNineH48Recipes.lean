module

public import RKCert.ERKGoodPrimeTower
public import RKCert.ERKOrderNineFiveSixAtlas
public import RKCert.ERKOrderNineH48Data

@[expose] public section

namespace RKCert.GoodPrimeDense
open RKCert.Paired Polynomial

def pencilRecipe {A : Type*} (o : Operations A) (l d : A) : Four A :=
  let l' : Box o := ⟨l⟩
  let d' : Box o := ⟨d⟩
  ⟨((2-6*l')*d').value,((-28+54*l')*d').value,((112-126*l')*d').value,(l'-2).value⟩

def pencilAt {R : Type*} [CommRing R] (l d : R) : Four R :=
  ⟨(2-6*l)*d,(-28+54*l)*d,(112-126*l)*d,l-2⟩

theorem map_pencilRecipe {A R : Type*} [CommRing R] {o : Operations A} {f : A→R}
    (s : Sound o f) (l d : A) :
    (pencilRecipe o l d).map f = pencilAt (f l) (f d) := by
  simp only [pencilRecipe,Four.map,pencilAt,Box.cast_add s,Box.cast_sub s,Box.cast_neg s,
    Box.cast_mul s,Box.cast_num s,Nat.cast_ofNat]

theorem pencilAt_eval {K : Type*} [Field K] [CharZero K] (l x : K) :
    (pencilAt l ((84:K)⁻¹)).eval x = (lobattoPencil l).eval x := by
  simp [pencilAt,Four.eval,lobattoPencil]
  ring

def rawCoeff2 {A : Type*} {o : Operations A} (r u v : Box o) : Box o :=
  ((504*u*v^3 - 945*u*v^2 + 540*u*v - 81*u - 504*v^3 + 945*v^2 - 549*v + 90)*r^2 +
      (-756*u^2*v^3 + 1512*u^2*v^2 - 972*u^2*v + 192*u^2 + 504*u*v^3 - 1107*u*v^2 + 816*u*v - 201*u + 252*v^3 - 393*v^2 + 150*v + 3)*r +
      (756*u^2*v^3 - 1512*u^2*v^2 + 984*u^2*v - 204*u^2 - 1008*u*v^3 + 2037*u*v^2 - 1350*u*v + 291*u + 252*v^3 - 537*v^2 + 381*v - 90))

def rawCoeff1 {A : Type*} {o : Operations A} (r u v : Box o) : Box o :=
  ((-168*u^2*v^2 + 336*u^2*v - 168*u^2 - 504*u*v^3 + 1092*u*v^2 - 888*u*v + 276*u + 504*v^3 - 924*v^2 + 564*v - 120)*r^3 +
      (224*u^3*v^2 - 448*u^3*v + 224*u^3 + 224*u^2*v^3 - 588*u^2*v^2 + 576*u^2*v - 204*u^2 - 28*u*v^3 + 72*u*v^2 + 16*u*v - 52*u - 196*v^3 + 288*v^2 - 148*v + 40)*r^2 +
      (672*u^3*v^3 - 1456*u^3*v^2 + 1184*u^3*v - 368*u^3 - 952*u^2*v^3 + 2004*u^2*v^2 - 1608*u^2*v + 508*u^2 + 524*u*v^3 - 1008*u*v^2 + 684*u*v - 176*u - 260*v^3 + 484*v^2 - 272*v + 40)*r +
      (-672*u^3*v^3 + 1232*u^3*v^2 - 752*u^3*v + 160*u^3 + 728*u^2*v^3 - 1244*u^2*v^2 + 704*u^2*v - 148*u^2 + 28*u*v^3 - 184*u*v^2 + 200*u*v - 52*u - 68*v^3 + 176*v^2 - 148*v + 40))

def rawCoeff0 {A : Type*} {o : Operations A} (r u v : Box o) : Box o :=
  ((756*u^2*v^3 - 1260*u^2*v^2 + 576*u^2*v - 36*u^2 - 756*u*v^3 + 1224*u*v^2 - 522*u*v + 18*u + 18*v^2 - 36*v + 18)*r^3 +
      (-1008*u^3*v^3 + 1680*u^3*v^2 - 768*u^3*v + 48*u^3 + 546*u^2*v^3 - 900*u^2*v^2 + 390*u^2*v - 12*u^2 + 510*u*v^3 - 834*u*v^2 + 378*u*v - 30*u - 24*v^3 + 42*v^2 - 12*v - 6)*r^2 +
      (1008*u^3*v^3 - 1632*u^3*v^2 + 696*u^3*v - 24*u^3 - 1362*u^2*v^3 + 2208*u^2*v^2 - 930*u^2*v + 24*u^2 + 318*u*v^3 - 516*u*v^2 + 204*u*v + 6*u + 12*v^3 - 30*v^2 + 24*v - 6)*r +
      (-24*u^3*v^2 + 48*u^3*v - 24*u^3 + 30*u^2*v^3 - 36*u^2*v^2 - 18*u^2*v + 24*u^2 - 42*u*v^3 + 90*u*v^2 - 54*u*v + 6*u + 12*v^3 - 30*v^2 + 24*v - 6))

def k8Recipe {A : Type*} (o : Operations A) (h r u v : A) : A :=
  let h' : Box o := ⟨h⟩
  let r' : Box o := ⟨r⟩
  let u' : Box o := ⟨u⟩
  let v' : Box o := ⟨v⟩
  (rawCoeff2 r' u' v'*h'^2+rawCoeff1 r' u' v'*h'+rawCoeff0 r' u' v').value

theorem eval_k8Recipe {A K : Type*} [Field K] [CharZero K] {o : Operations A} {f : A→K}
    (s : Sound o f) (h r u v : A) :
    f (k8Recipe o h r u v) = sixOnK8Raw (f h) (f r) (f u) (f v) := by
  simp only [k8Recipe,rawCoeff0,rawCoeff1,rawCoeff2,Box.cast_add s,Box.cast_sub s,Box.cast_neg s,
    Box.cast_mul s,Box.cast_pow s,Box.cast_num s,Nat.cast_ofNat,
    sixOnK8Raw,sixOnK8Coeff0,sixOnK8Coeff1,sixOnK8Coeff2]

def k8TowerNorm {A : Type*} (o : Operations A) (l d : A) : A :=
  let t : Tower A := ⟨o,pencilRecipe o l d⟩
  let r : Box t.atV := 2-⟨t.coe l⟩-⟨t.h⟩-⟨t.u⟩-⟨t.v⟩
  t.relativeNorm (k8Recipe t.atV t.h r.value t.u t.v)

set_option maxHeartbeats 1000000 in
theorem k8TowerNorm_zero {A K : Type*} [Field K] [CharZero K] {o : Operations A} {f : A→K}
    (s : Sound o f) (l d : A) (h u v : K)
    (root : RootSystem (pencilAt (f l) (f d)) h u v)
    (k : sixOnK8 h u v (f l)=0) :
    f (k8TowerNorm o l d) = 0 := by
  let t : Tower A := ⟨o,pencilRecipe o l d⟩
  have root' : RootSystem (t.four.map f) h u v := by
    change RootSystem ((pencilRecipe o l d).map f) h u v
    simpa only [map_pencilRecipe s] using root
  have ts := Tower.soundV s h u v root'
  let r : Box t.atV := 2-⟨t.coe l⟩-⟨t.h⟩-⟨t.u⟩-⟨t.v⟩
  change f (t.relativeNorm (k8Recipe t.atV t.h r.value t.u t.v)) = 0
  refine Tower.norm_zero s h u v root' _ ?_
  have er : read (read (read f h) u) v r.value = 2-f l-h-u-v := by
    dsimp only [r]
    simp only [Box.cast_sub ts,Box.cast_num ts,Nat.cast_ofNat,Tower.readCoe s h u v root',
      Tower.readH s h u v root',Tower.readU s h u v root',Tower.readV s h u v root']
  rw [eval_k8Recipe ts,er,Tower.readH s h u v root',Tower.readU s h u v root',
    Tower.readV s h u v root']
  exact k

def h48RawCoeffs : List ℚ :=
  let o := scalar ℚ
  let o' := dense o
  k8TowerNorm o' (generator o) (constant o ((84:ℚ)⁻¹))

def h48ExpectedCoeffs : List ℚ := h48Coeffs.map fun x => h48Scale * (x:ℚ)

end RKCert.GoodPrimeDense

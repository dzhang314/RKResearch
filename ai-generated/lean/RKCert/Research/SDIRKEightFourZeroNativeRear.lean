import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Native, integer, denominator-free Bézout identities for the Gaussian rear.
The preceding flag/chronology theorem determines which scalar gate applies. -/
namespace RKResearch.Certified.SDIRKEightFourZeroNativeRear

def gauss {R : Type*} [CommRing R] (x : R) : R :=
  70*x^4-140*x^3+90*x^2-20*x+1

def pairDD {R : Type*} [CommRing R] (x y : R) : R :=
  70*y^3+(70*x-140)*y^2+(70*x^2-140*x+90)*y+70*x^3-140*x^2+90*x-20

def tripleDD {R : Type*} [CommRing R] (x y s : R) : R :=
  70*(s^2+s*y+y^2)+(70*x-140)*(s+y)+(70*x^2-140*x+90)

def silentNumerator {R : Type*} [CommRing R] (x y : R) : R :=
  -2*x^3+(y-x)*x^2+4*x*(y-x)^2-(y-x)^3

def gapZero {R : Type*} [CommRing R] (v : R) : R := v^2-2*v-1

def canceledNumerator {R : Type*} [CommRing R] (x v n : R) : R :=
  70*(x*n)^3+(70*x-140)*(x*n)^2*(1+v)+
  (70*x^2-140*x+90)*(x*n)*(1+v)^2+
  (70*x^3-140*x^2+90*x-20)*(1+v)^3

theorem silentIdentity {R : Type*} [CommRing R] (x y : R) :
    (-6838259606080*x^3*y^2 - 2035598993680*x^3*y + 1569666653240*x^3 + 13549719473640*x^2*y^2 + 3112508054600*x^2*y - 2585778827898*x^2 - 8434328680840*x*y^2 - 1082214841732*x*y + 1191549726058*x + 1634502068209*y^2 - 103139673642*y - 70443641160)*(pairDD x y) +
    (-478678172425600*x^3*y^2 + 743856561722400*x^3*y - 272879000615200*x^3 + 948480363154800*x^2*y^2 - 1478762307380400*x^2*y + 547575029528030*x^2 - 590403007658800*x*y^2 + 926250597620600*x*y - 347817874008900*x + 114415144774630*y^2 - 181343989855560*y + 69445911530090)*(silentNumerator x y) +
    (20514778818240*x^2*y^2 - 19217445626960*x^2*y + 6226876221480*x^2 - 61544336454720*x*y^3 + 95004702100280*x*y^2 - 43920626683280*x*y + 2533863733680*x + 54706076848640*y^4 - 87167774037400*y^3 + 32110502229560*y^2 + 4277134231560*y - 1381852924594)*(gauss x) = (27019898606 : R) := by
  unfold pairDD silentNumerator gauss
  ring

theorem arithmeticIdentity {R : Type*} [CommRing R] (x y : R) :
    (1260*x^3 - 4410*x^2*y + 315*x^2 + 4410*x*y - 1610*x - 735*y + 385)*(pairDD x y) +
    (630*x^3*y - 315*x^3 + 630*x^2*y^2 - 1575*x^2*y + 630*x^2 - 630*x*y^2 + 1085*x*y - 385*x + 105*y^2 - 175*y + 68)*(tripleDD x y (2*y-x)) +
    (-1260*x^2 + 2520*x*y + 3780*y^2 - 5040*y + 1610)*(gauss x) = (30 : R) := by
  unfold pairDD tripleDD gauss
  ring

theorem starIdentity {R : Type*} [CommRing R] (x y : R) :
    (38353000*x^3 - 63718375*x^2 + 27705486*x - 1514537)*(pairDD x y) +
    (-38353000*x^3*y + 11767875*x^3 + 63718375*x^2*y - 19409180*x^2 - 27705486*x*y + 8193657*x + 1514537*y - 289574)*(tripleDD x y (4*x-y)) +
    (-38353000*x^2 + 767060000*x*y - 183407000*x - 191765000*y^2 + 3315294)*(gauss x) = (7544374 : R) := by
  unfold pairDD tripleDD gauss
  ring

theorem canceledArithmeticIdentity {R : Type*} [CommRing R] (v x : R) :
    (-543963280*v*x^2 + 340369120*v*x + 9822160*v - 656455170*x^2 + 725881380*x - 228811337)*(gauss x) +
    (-538538630*v*x^3 + 749328300*v*x^2 - 333583457*v*x + 21583308*v + 1304817920*x^3 - 1817094020*x^2 + 809091600*x - 52381526)*(canceledNumerator x v (1+2*v)) +
    (565465561500*v^2*x^6 - 1314562572400*v^2*x^5 + 1230009793950*v^2*x^4 - 562663674860*v^2*x^3 + 126205741230*v^2*x^2 - 12499162300*v^2*x + 431666160*v^2 + 816408021800*v*x^6 - 2117464861400*v*x^5 + 2197487211220*v*x^4 - 1122064156780*v*x^3 + 279767371540*v*x^2 - 30228469760*v*x + 1110700280*v + 319397155700*x^6 - 914094431600*x^5 + 1047871209910*x^4 - 597166566500*x^3 + 168211506220*x^2 - 20308398560*x + 805173640)*(gapZero v) = (13645543 : R) := by
  unfold gauss canceledNumerator gapZero
  ring

theorem canceledStarIdentity {R : Type*} [CommRing R] (v x : R) :
    (-11235840*v*x^2 + 2637040*v*x + 28089600*x^2 - 7911120*x + 582744)*(gauss x) +
    (234080*v*x^3 - 454825*v*x^2 + 274290*v*x - 49798*v - 585200*x^3 + 1130395*x^2 - 675008*x + 120938)*(canceledNumerator x v (3-v)) +
    (32771200*v^2*x^5 - 63675500*v^2*x^4 + 43082200*v^2*x^3 - 16068220*v^2*x^2 + 5485800*v^2*x - 995960*v^2 - 131084800*v*x^6 + 205545200*v*x^5 - 143291400*v*x^4 + 147227360*v*x^3 - 111659400*v*x^2 + 31856120*v*x - 2561040*v + 327712000*x^6 - 256152400*x^5 - 481600420*x^4 + 630410200*x^3 - 246958980*x^2 + 37471840*x - 1849640)*(gapZero v) = (13624 : R) := by
  unfold gauss canceledNumerator gapZero
  ring

theorem gauss_sub {R : Type*} [CommRing R] (x y : R) :
    gauss y-gauss x = (y-x)*pairDD x y := by
  unfold gauss pairDD
  ring

theorem pair_sub {R : Type*} [CommRing R] (x y s : R) :
    pairDD x s - pairDD x y = (s-y)*tripleDD x y s := by
  unfold pairDD tripleDD
  ring

theorem pairDD_zero {F : Type*} [CommRing F] [IsDomain F] {x y : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hne : y ≠ x) : pairDD x y = 0 := by
  have hh : (y-x)*pairDD x y = 0 := by rw [← gauss_sub, hx, hy, sub_zero]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)

theorem tripleDD_zero {F : Type*} [CommRing F] [IsDomain F] {x y s : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hs : gauss s = 0)
    (hyx : y ≠ x) (hsx : s ≠ x) (hsy : s ≠ y) : tripleDD x y s = 0 := by
  have hh : (s-y)*tripleDD x y s = 0 := by
    rw [← pair_sub, pairDD_zero hx hs hsx, pairDD_zero hx hy hyx, sub_zero]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hsy)

theorem silent_rear_forces_constant {F : Type*} [CommRing F] [IsDomain F] {x y v : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hne : y ≠ x)
    (hv : y-x = x*v) (hH : -2+v+4*v^2-v^3 = 0) :
    (27019898606 : F) = 0 := by
  have hS : silentNumerator x y = 0 := by
    calc
      silentNumerator x y = x^3*(-2+v+4*v^2-v^3) := by
        unfold silentNumerator
        rw [hv]
        ring
      _ = 0 := by rw [hH, mul_zero]
  simpa [hx, pairDD_zero hx hy hne, hS] using (silentIdentity x y).symm

theorem arithmetic_rear_forces_constant {F : Type*} [CommRing F] [IsDomain F] {x y : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hs : gauss (2*y-x) = 0)
    (h₁ : y ≠ x) (h₂ : 2*y-x ≠ x) (h₃ : 2*y-x ≠ y) :
    (30 : F) = 0 := by
  simpa [hx, pairDD_zero hx hy h₁, tripleDD_zero hx hy hs h₁ h₂ h₃] using
    (arithmeticIdentity x y).symm

theorem star_rear_forces_constant {F : Type*} [CommRing F] [IsDomain F] {x y : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hs : gauss (4*x-y) = 0)
    (h₁ : y ≠ x) (h₂ : 4*x-y ≠ x) (h₃ : 4*x-y ≠ y) :
    (7544374 : F) = 0 := by
  simpa [hx, pairDD_zero hx hy h₁, tripleDD_zero hx hy hs h₁ h₂ h₃] using
    (starIdentity x y).symm

theorem canceledNumerator_zero {F : Type*} [CommRing F] [IsDomain F] {x y v n : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hne : y ≠ x)
    (hr : y*(1+v) = x*n) : canceledNumerator x v n = 0 := by
  calc
    canceledNumerator x v n = pairDD x y*(1+v)^3 := by
      unfold canceledNumerator pairDD
      rw [← hr]
      ring
    _ = 0 := by rw [pairDD_zero hx hy hne, zero_mul]

theorem canceled_arithmetic_forces_constant {F : Type*} [CommRing F] [IsDomain F] {x y v : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hne : y ≠ x)
    (hv : gapZero v = 0) (hr : y*(1+v) = x*(1+2*v)) :
    (13645543 : F) = 0 := by
  simpa [hx, hv, canceledNumerator_zero hx hy hne hr] using
    (canceledArithmeticIdentity v x).symm

theorem canceled_star_forces_constant {F : Type*} [CommRing F] [IsDomain F] {x y v : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hne : y ≠ x)
    (hv : gapZero v = 0) (hr : y*(1+v) = x*(3-v)) :
    (13624 : F) = 0 := by
  simpa [hx, hv, canceledNumerator_zero hx hy hne hr] using
    (canceledStarIdentity v x).symm

theorem integer_factorizations :
    (27019898606 : Nat) = 2*397*487*69877 ∧
    (30 : Nat) = 2*3*5 ∧
    (7544374 : Nat) = 2*37*269*379 ∧
    (13645543 : Nat) = 17*103*7793 ∧
    (13624 : Nat) = 2^3*13*131 := by
  decide +kernel

theorem no_gaussian_rear_characteristic_zero {F : Type*} [CommRing F] [IsDomain F] [CharZero F]
    {x y : F} (hx : gauss x = 0) (hy : gauss y = 0) (hyx : y ≠ x)
    (hphase : (∃ v, y-x = x*v ∧ -2+v+4*v^2-v^3 = 0) ∨
      (gauss (2*y-x) = 0 ∧ 2*y-x ≠ x ∧ 2*y-x ≠ y) ∨
      (gauss (4*x-y) = 0 ∧ 4*x-y ≠ x ∧ 4*x-y ≠ y)) : False := by
  rcases hphase with ⟨v,hgap,hH⟩ | ⟨hs,hsx,hsy⟩ | ⟨hs,hsx,hsy⟩
  · have h := silent_rear_forces_constant hx hy hyx hgap hH
    norm_num at h
  · have h := arithmetic_rear_forces_constant hx hy hs hyx hsx hsy
    norm_num at h
  · have h := star_rear_forces_constant hx hy hs hyx hsx hsy
    norm_num at h

theorem no_canceled_gaussian_rear_characteristic_zero {F : Type*}
    [CommRing F] [IsDomain F] [CharZero F] {x y v : F}
    (hx : gauss x = 0) (hy : gauss y = 0) (hyx : y ≠ x) (hv : gapZero v = 0)
    (hphase : y*(1+v)=x*(1+2*v) ∨ y*(1+v)=x*(3-v)) : False := by
  rcases hphase with ha | hs
  · have h := canceled_arithmetic_forces_constant hx hy hyx hv ha
    norm_num at h
  · have h := canceled_star_forces_constant hx hy hyx hv hs
    norm_num at h

end RKResearch.Certified.SDIRKEightFourZeroNativeRear

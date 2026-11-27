module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Arithmetic cuts for prescribed terminal poles in the DIRK10 front chart.

The input is the full five scalar coefficient equations of the first-three
primitive identity, not an assumed tableau classification. Integer Bézout
identities and finite rational-root obstructions are checked in the kernel. -/

namespace RKResearch.Certified.DIRKTenRationalPoles

def early {K : Type*} [CommRing K] (s t : K) : K :=
  420*s^4-1008*s^3+1008*s^2-504*s+108+(-168*s^2+252*s-108)*t+
    (33-28*s)*t^2-3*t^3

def originNum {K : Type*} [CommRing K] (s t : K) : K :=
  252*s^3+112*s^2*t-672*s^2+42*s*t^2-378*s*t+756*s+
    2*t^3-37*t^2+192*t-252

def slopeNum {K : Type*} [CommRing K] (s t : K) : K :=
  336*s^3*t+1008*s^3+336*s^2*t^2-1848*s^2*t-1008*s^2+
    56*s*t^3-616*s*t^2+1596*s*t+504*s+6*t^4-83*t^3+363*t^2-468*t-108

/-- With s=a+b, t=s/u, p=s²/(6−t), u=s/t, P=X(X²−sX+p),
D=(X-u)P, J=IP, the five hypotheses are exactly the five positive-degree
coefficients of H=(r+zX)D+(e+fX)J, cleared of their denominators.
No identity is obtained by dropping the X² coefficient. -/
theorem coefficient_system {K : Type*} [Field K] [CharZero K]
    (s t r z e f : K) (ht : t ≠ 0)
    (h1 : -r*s^3+t^2-6*t = 0)
    (h2 : e*s^2*t+12*r*s^2-2*s^3*z-28*t^2+168*t = 0)
    (h3 : 2*e*s*t^2-12*e*s*t+3*f*s^2*t+6*r*s*t^2-30*r*s*t-
      36*r*s+36*s^2*z+336*t^2-2016*t = 0)
    (h4 : 3*e*t-4*f*s*t+12*r*t-12*s*t*z-12*s*z+1008*t = 0)
    (h5 : f+4*z-168 = 0) :
    early s t = 0 ∧ 5*s^3*(2*t-3)*e = 12*originNum s t ∧
      5*s^4*(2*t-3)*f = -6*slopeNum s t := by
  refine ⟨?_, ?_, ?_⟩
  · have ha : (2*t)*early s t = 0 := by
      unfold early
      linear_combination (-6*(t-3)*(t-2))*h1+(2*s*(t-3))*h2-
        s^2*h3-(2*s^3)*h4-(5*s^4*t)*h5
    exact (mul_eq_zero.mp ha).resolve_left (mul_ne_zero (by norm_num) ht)
  · have ha : t*(5*s^3*(2*t-3)*e-12*originNum s t)=0 := by
      unfold originNum
      linear_combination (-12*(t-2)*(2*t-21))*h1+(18*s*(t-3))*h2-
        (4*s^2)*h3-(3*s^3)*h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_left ht)
  · have ha : t*(5*s^4*(2*t-3)*f+6*slopeNum s t)=0 := by
      unfold slopeNum
      linear_combination (6*(t-3)*(6*t^2-29*t-6))*h1-
        (6*s*(2*t^2-10*t-3))*h2+(3*s^2*(2*t+1))*h3+(2*s^3*(t+3))*h4
    have hb := (mul_eq_zero.mp ha).resolve_left ht
    linear_combination hb

/-- Homogeneous evaluation in projective coordinates, descending coefficients. -/
def hval {R : Type*} [CommRing R] : List ℤ → R → R → R
  | [], _, _ => 0
  | q::qs, a, b => (q : R)*a^qs.length + b*hval qs a b

theorem hval_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (l : List ℤ) (a b : R) :
    f (hval l a b) = hval l (f a) (f b) := by
  induction l with
  | nil => simp [hval]
  | cons q qs ih => simp only [hval, map_add, map_mul, map_intCast, map_pow, ih]

theorem hval_scale {R : Type*} [CommRing R] (l : List ℤ) (v a b : R) :
    hval l (v*a) (v*b) = v^(l.length-1)*hval l a b := by
  induction l with
  | nil => simp [hval]
  | cons q qs ih =>
    cases qs with
    | nil => simp [hval]
    | cons w ws =>
      have hu : hval (w::ws) (v*a) (v*b) =
          v^ws.length * hval (w::ws) a b := by simpa using ih
      change (q:R)*(v*a)^((w::ws).length) +
          (v*b)*hval (w::ws) (v*a) (v*b) =
        v^((w::ws).length)*((q:R)*a^((w::ws).length)+b*hval (w::ws) a b)
      rw [hu, mul_pow, List.length_cons, pow_succ]
      ring

theorem no_rat_root_of_prime {p : ℕ} [Fact p.Prime] (l : List ℤ)
    (hfinite : ∀ x : ZMod p, hval l x 1 ≠ 0)
    (hinfinity : hval l (1 : ZMod p) 0 ≠ 0) (x : ℚ) :
    hval l x 1 ≠ 0 := by
  intro hx
  have hnd : (x.den : ℚ)*x = x.num := Rat.den_mul_eq_num x
  have hcleared : hval l x.num (x.den : ℤ) = 0 := by
    have h : hval l (x.num : ℚ) (x.den : ℚ) = 0 := by
      have hs := hval_scale l (x.den : ℚ) x (1 : ℚ)
      rw [mul_one, hnd, hx, mul_zero] at hs
      exact hs
    have hh := hval_map (Int.castRingHom ℚ) l x.num (x.den : ℤ)
    simp only [Int.coe_castRingHom, Int.cast_natCast, h] at hh
    exact_mod_cast hh
  have hz := hval_map (Int.castRingHom (ZMod p)) l x.num (x.den : ℤ)
  simp only [hcleared, map_zero, Int.coe_castRingHom, Int.cast_natCast] at hz
  by_cases hd : (x.den : ZMod p) = 0
  · have hn : (x.num : ZMod p) ≠ 0 := by
      intro hn
      have hden := (ZMod.natCast_eq_zero_iff x.den p).mp hd
      have hnum := Int.ofNat_dvd_left.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp hn)
      exact (Fact.out : p.Prime).ne_one ((Nat.gcd_eq_one_iff.mp x.reduced) p hnum hden)
    rw [hd] at hz
    have hs := hval_scale l (x.num : ZMod p) (1 : ZMod p) 0
    rw [mul_one, mul_zero, ← hz] at hs
    exact mul_ne_zero (pow_ne_zero _ hn) hinfinity hs.symm
  · have hs := hval_scale l (x.den : ZMod p) ((x.num : ZMod p)/x.den) 1
    rw [mul_one, show (x.den : ZMod p)*((x.num : ZMod p)/x.den) = x.num by
      field_simp [hd], ← hz] at hs
    exact mul_ne_zero (pow_ne_zero _ hd) (hfinite _) hs.symm

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private instance : Fact (Nat.Prime 13) := ⟨by decide⟩
private instance : Fact (Nat.Prime 23) := ⟨by decide⟩

def polyOrigin : List ℤ := [144, -76572, 917612, -4220844, 10142289, -14054040, 11344536, -4953312, 898128]

theorem no_rat_root_origin (t : ℚ) : hval polyOrigin t 1 ≠ 0 :=
  no_rat_root_of_prime (p := 23) polyOrigin (by decide +kernel) (by decide +kernel) t

private def UOrigin {K : Type*} [CommRing K] (s t : K) : K :=
  s^0*((14914368)+t*((-48326544)+t*((63930384)+t*((-43922340)+t*((16365720)+t*((-3082968)+t*(220836))))))) + s^1*((-17273088)+t*((48459600)+t*((-52771824)+t*((27530076)+t*((-6723388)+t*(592200)))))) + s^2*((8192016)+t*((-21654864)+t*((21409164)+t*((-9366336)+t*(1519560)))))
private def VOrigin {K : Type*} [CommRing K] (s t : K) : K :=
  s^0*((6178032)+t*((-21074256)+t*((29594376)+t*((-21792060)+t*((8798235)+t*((-1816342)+t*((143604)+t*(360)))))))) + s^1*((-18697392)+t*((53003160)+t*((-58938516)+t*((31995054)+t*((-8458002)+t*((892500)+t*((-7560)))))))) + s^2*((25147584)+t*((-65073456)+t*((62397216)+t*((-25862004)+t*((3592260)+t*(138600)))))) + s^3*((-13653360)+t*((36091440)+t*((-35681940)+t*((15610560)+t*((-2532600))))))

private theorem bezout_origin {K : Type*} [CommRing K] (s t : K) :
    5*(t-6)*(t-2)*hval polyOrigin t 1 =
      UOrigin s t * early s t + VOrigin s t * (originNum s t) := by
  unfold UOrigin VOrigin early originNum
  simp only [polyOrigin, hval, List.length_cons, List.length_nil, Int.cast_ofNat,
    one_mul]
  ring

def polyTerminal : List ℤ := [1224720, -14737680, 71305848, -252973320, 786863737, -1853235405, 2926969947, -2995869699, 1958064192, -788814936, 178564176, -17391024]

theorem no_rat_root_terminal (t : ℚ) : hval polyTerminal t 1 ≠ 0 :=
  no_rat_root_of_prime (p := 11) polyTerminal (by decide +kernel) (by decide +kernel) t

private def UTerminal {K : Type*} [CommRing K] (s t : K) : K :=
  s^0*((1296733536)+t*((-2813916672)+t*((-15172593408)+t*((69392748600)+t*((-116694729054)+t*((105016355514)+t*((-56963676366)+t*((19519447454)+t*((-4174709176)+t*((494251992)+t*((-24068160)))))))))))) + s^1*((-9574371072)+t*((47834460576)+t*((-71720065872)+t*((-3020082408)+t*((105292082196)+t*((-105169792896)+t*((45680186076)+t*((-9825291672)+t*((1108284912)+t*((-55369440))))))))))) + s^2*((18392028480)+t*((-110896654176)+t*((257155283952)+t*((-288621072936)+t*((163288138608)+t*((-44621591280)+t*((4947832232)+t*((-294594048)+t*(24665760))))))))) + s^3*((-4677450624)+t*((28535649408)+t*((-67379141088)+t*((77875989408)+t*((-46309115664)+t*((13788232416)+t*((-1755286848)+t*(71487360))))))))
private def VTerminal {K : Type*} [CommRing K] (s t : K) : K :=
  s^0*((-1209778416)+t*((8402232384)+t*((-23962055040)+t*((36792119700)+t*((-33788461581)+t*((19607889483)+t*((-7382754645)+t*((1811236441)+t*((-282044826)+t*((25506180)+t*((-1020600)))))))))))) + s^1*((4334529024)+t*((-27504680112)+t*((69049536696)+t*((-88331757444)+t*((62568265914)+t*((-25222571388)+t*((5509214970)+t*((-460501020)+t*((-50886360)+t*(8845200)))))))))) + s^2*((-6491505888)+t*((39379401936)+t*((-92308738536)+t*((105896088396)+t*((-63022154328)+t*((19715982552)+t*((-3361028076)+t*((435516480)+t*((-33793200)))))))))) + s^3*((3897875520)+t*((-23779707840)+t*((56149284240)+t*((-64896657840)+t*((38590929720)+t*((-11490193680)+t*((1462739040)+t*((-59572800)))))))))

private theorem bezout_terminal {K : Type*} [CommRing K] (s t : K) :
    5*(t-6)^2*(t-3)*hval polyTerminal t 1 =
      UTerminal s t * early s t + VTerminal s t * (2*s*originNum s t-slopeNum s t) := by
  unfold UTerminal VTerminal early originNum slopeNum
  simp only [polyTerminal, hval, List.length_cons, List.length_nil, Int.cast_ofNat,
    one_mul]
  ring

def polyConstant : List ℤ := [3888, -37584, 244216, -1940256, 8813235, -21940163, 32274681, -29284353, 16545168, -5695272, 1123632, -104976]

theorem no_rat_root_constant (t : ℚ) : hval polyConstant t 1 ≠ 0 :=
  no_rat_root_of_prime (p := 11) polyConstant (by decide +kernel) (by decide +kernel) t

private def UConstant {K : Type*} [CommRing K] (s t : K) : K :=
  s^0*((5225472)+t*((-11757312)+t*((-31897152)+t*((241702272)+t*((-488596752)+t*((477505728)+t*((-264909680)+t*((90875008)+t*((-20112960)+t*((2539264)+t*((-132608)))))))))))) + s^1*((-14370048)+t*((30917376)+t*((140470848)+t*((-822636864)+t*((1470446208)+t*((-1227355584)+t*((523048512)+t*((-112301952)+t*((12063744)+t*((-537600))))))))))) + s^2*((30046464)+t*((-194213376)+t*((543195072)+t*((-662522112)+t*((320632704)+t*((-5779200)+t*((-39928896)+t*((8531712)+t*((-456960))))))))))
private def VConstant {K : Type*} [CommRing K] (s t : K) : K :=
  s^0*((4700592)+t*((-31383936)+t*((100958400)+t*((-174226788)+t*((173397249)+t*((-104732355)+t*((39344705)+t*((-9218937)+t*((1306794)+t*((-101404)+t*(3240))))))))))) + s^1*((-16819488)+t*((108238032)+t*((-319792536)+t*((470234268)+t*((-366759288)+t*((157193652)+t*((-36833832)+t*((4396392)+t*((-26880)+t*((-30240))))))))))) + s^2*((23514624)+t*((-152790624)+t*((441080640)+t*((-601142472)+t*((401053968)+t*((-126844536)+t*((16259376)+t*((-1233120)+t*(100800))))))))) + s^3*((-12519360)+t*((85095360)+t*((-254696400)+t*((360949680)+t*((-253913520)+t*((87045840)+t*((-12378240)+t*(571200))))))))

private theorem bezout_constant {K : Type*} [CommRing K] (s t : K) :
    5*(t-6)^2*(t-3)*hval polyConstant t 1 =
      UConstant s t * early s t + VConstant s t * (slopeNum s t) := by
  unfold UConstant VConstant early slopeNum
  simp only [polyConstant, hval, List.length_cons, List.length_nil, Int.cast_ofNat,
    one_mul]
  ring

def polyJacobi : List ℤ := [42, -84, 56, -14, 1]

theorem no_rat_root_jacobi (t : ℚ) : hval polyJacobi t 1 ≠ 0 :=
  no_rat_root_of_prime (p := 11) polyJacobi (by decide +kernel) (by decide +kernel) t

def polyFixedFront : List ℤ := [125, -100, -87, 1314]

theorem no_rat_root_fixedfront (t : ℚ) : hval polyFixedFront t 1 ≠ 0 :=
  no_rat_root_of_prime (p := 13) polyFixedFront (by decide +kernel) (by decide +kernel) t

/-- The exact three prescribed-slope obstructions on the rational scalar chart.
The remaining affine nonshared pole away from 0 and 1 is not addressed. -/
theorem no_prescribed_pole {s t e f : ℚ}
    (ht₂ : t ≠ 2) (ht₃ : t ≠ 3) (ht₆ : t ≠ 6) (he : early s t = 0)
    (h₀ : 5*s^3*(2*t-3)*e = 12*originNum s t)
    (h₁ : 5*s^4*(2*t-3)*f = -6*slopeNum s t) :
    e ≠ 0 ∧ e+f ≠ 0 ∧ f ≠ 0 := by
  have ht₂' : t-2 ≠ 0 := sub_ne_zero.mpr ht₂
  have ht₃' : t-3 ≠ 0 := sub_ne_zero.mpr ht₃
  have ht₆' : t-6 ≠ 0 := sub_ne_zero.mpr ht₆
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hn : originNum s t = 0 := by
      rw [hz, mul_zero] at h₀
      exact (mul_eq_zero.mp h₀.symm).resolve_left (by norm_num)
    have h := bezout_origin s t
    simp only [he, hn, mul_zero, add_zero] at h
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht₆') ht₂')
      (no_rat_root_origin t) h
  · intro hz
    have hz' : f = -e := by linear_combination hz
    rw [hz'] at h₁
    have hn : 2*s*originNum s t-slopeNum s t = 0 := by
      linear_combination (-s/6)*h₀-(1/6)*h₁
    have h := bezout_terminal s t
    simp only [he, hn, mul_zero, add_zero] at h
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ ht₆')) ht₃') (no_rat_root_terminal t) h
  · intro hz
    have hn : slopeNum s t = 0 := by
      rw [hz, mul_zero] at h₁
      exact (mul_eq_zero.mp h₁.symm).resolve_left (by norm_num)
    have h := bezout_constant s t
    simp only [he, hn, mul_zero, add_zero] at h
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ ht₆')) ht₃') (no_rat_root_constant t) h


/-- Guards use the ordinary ordered rational field, only at the negative
square t=3. They do not require the three rational clocks to be positive. -/
theorem paired_rational_guards {a b u : ℚ}
    (ha : a ≠ 0) (_hb : b ≠ 0) (hu : u ≠ 0) (hab : a ≠ b)
    (hau : a ≠ u) (hbu : b ≠ u)
    (hpair : u*(4*a*b-a^2-b^2)=a*b*(a+b)) :
    let t := (a+b)/u
    t ≠ 0 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 6 ∧ t ≠ 3/2 := by
  let t := (a+b)/u
  have htu : t*u = a+b := div_mul_cancel₀ _ hu
  have hs : a+b ≠ 0 := by
    intro hz
    have hba : b = -a := by linear_combination hz
    rw [hba] at hpair
    have hp : u*(-6*a^2) = 0 := by linear_combination hpair
    exact mul_ne_zero hu (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hp
  have hp : (6-t)*(a*b) = (a+b)^2 := by
    have he : u*((6-t)*(a*b)-(a+b)^2) = 0 := by
      linear_combination hpair-(a*b)*htu
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hu)
  change t ≠ 0 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 6 ∧ t ≠ 3/2
  refine ⟨div_ne_zero hs hu, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hp
    have hsq : (a-b)^2 = 0 := by linear_combination -hp
    exact pow_ne_zero _ (sub_ne_zero.mpr hab) hsq
  · intro h
    rw [h] at hp
    have hsq : 3*(a-b)^2+(a+b)^2 = 0 := by linear_combination -4*hp
    have hpos : 0 < (a+b)^2 := sq_pos_of_ne_zero hs
    have hz : 0 ≤ (a-b)^2 := sq_nonneg _
    exact (ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hz) hpos)) hsq
  · intro h
    rw [h, sub_self, zero_mul] at hp
    exact pow_ne_zero _ hs hp.symm
  · intro h
    rw [h] at hp htu
    have he : (u-a)*(u-b) = 0 := by
      linear_combination (2/9)*hp+((6*u-2*(a+b))/9)*htu
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hau))
      (sub_ne_zero.mpr (Ne.symm hbu)) he

/-- Substitute t=2/3 on the early quartic. Its two rational horizontal
points differ: the first needs a genuine cubic extension, while the second
hits the front pivot alignment. -/
theorem fixed_front_two_fifths_no_rat (k : ℚ) :
    -4/225*(125*k^3-100*k^2-87*k+1314) ≠ 0 := by
  intro h
  apply no_rat_root_fixedfront k
  norm_num [polyFixedFront, hval]
  linear_combination (-225/4)*h

theorem fixed_front_two_thirds_degenerate {k y w : ℚ}
    (h : -12/25*(k-6)*(k-3)^2 = 0)
    (hyD : (84/5)*k-504/5 ≠ 0)
    (hy : ((84/5)*k-504/5)*y = -432/5+12*k)
    (hw : (-(84/25)*(k-6))*w =
      -(12/25)*(k-6)*(k+4)) : k = 3 ∧ y = 1 ∧ w = 1 := by
  have hk6 : k ≠ 6 := by
    intro hk
    apply hyD
    norm_num [hk]
  have hprod := (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hk6))
  have hk : k = 3 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hprod)
  rw [hk] at hy hw
  have hey : y = 1 := by linear_combination (-5/252)*hy
  have hew : w = 1 := by linear_combination (25/252)*hw
  exact ⟨hk, hey, hew⟩

end RKResearch.Certified.DIRKTenRationalPoles

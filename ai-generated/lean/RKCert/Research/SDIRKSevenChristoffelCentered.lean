module

public import RKCert.Research.SDIRKSevenChristoffelScalar
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar and primitive integer gates for the centered Christoffel chart

The external exact polynomial replay derives the split-discriminant receipt.
This module verifies the underlying reductions and proves that its homogeneous
numerator cannot be a square on a primitive elliptic triple. -/

namespace RKResearch.Certified.SDIRKSevenChristoffelCentered

def cub {R : Type*} [CommRing R] (a b c d x : R) : R := a+b*x+c*x^2+d*x^3
def suffixM {R : Type*} [CommRing R] (u : R) : R := u^2-4*u+2
def suffixT {R : Type*} [CommRing R] (u : R) : R := u^3-7*u^2+10*u-2
def suffixJ {R : Type*} [CommRing R] (u : R) : R := 4*u^3-24*u^2+39*u-17

theorem reflection_opener {R : Type*} [CommRing R] (u a b c d : R) :
    (4-u-1)*cub a b c d u-(u-1)*cub a b c d (4-u)+
      (4-u-u)*suffixM u*cub a b c d 1 =
    (4-u-u)*(suffixM u+1)*(a+b+2*c+6*d) := by
  simp only [cub,suffixM]
  ring

def a₀ {R : Type*} [CommRing R] (u : R) : R := (u-3)*(2*u^2-10*u+11)
def a₁ {R : Type*} [CommRing R] (u : R) : R := (u-3)*(u-2)*(2*u-3)
def a₂ {R : Type*} [CommRing R] (u : R) : R := 4*(u-2)^2*(u-1)
def a₃ {R : Type*} [CommRing R] (u : R) : R := 6*(u-1)^2*(2*u-3)

theorem arithmetic_opener {R : Type*} [CommRing R] (u a b c d : R) :
    suffixT u*cub a b c d (2*u-1)-2*suffixJ u*cub a b c d u-
      suffixM u*suffixJ u*cub a b c d 1 =
    -2*(u-1)^2*(a₀ u*a+a₁ u*b+a₂ u*c+a₃ u*d) := by
  simp only [cub,suffixM,suffixT,suffixJ,a₀,a₁,a₂,a₃]
  ring

def A₀ (u : ℚ) : ℚ := a₀ u
def B₀ (u : ℚ) : ℚ := -5*a₁ u
def C₀ (u : ℚ) : ℚ := 10*(u-2)^2*(u-1)
def radicalH (u : ℚ) : ℚ := 4*u^3-24*u^2+57*u-47

theorem centered_opener (u m : ℚ) :
    a₀ u*(2*m^2)+a₁ u*(-10*m)+a₂ u*5 =
      2*(A₀ u*m^2+B₀ u*m+C₀ u) := by
  simp only [A₀,B₀,C₀,a₀,a₁,a₂]
  ring

theorem centered_discriminant (u : ℚ) :
    (B₀ u)^2-4*A₀ u*C₀ u=5*(u-3)*(u-2)^2*radicalH u := by
  simp only [A₀,B₀,C₀,radicalH,a₀,a₁]
  ring

theorem elliptic_of_centered {u m : ℚ} (h₂ : u≠2) (h₃ : u≠3)
    (h : A₀ u*m^2+B₀ u*m+C₀ u=0) :
    let w := (2*A₀ u*m+B₀ u)/(u-2)
    let X := 80/(u-3)
    let Y := X^2*w/80
    Y^2=X^3+105*X^2+4800*X+128000 := by
  have d₂ := sub_ne_zero.mpr h₂
  have d₃ := sub_ne_zero.mpr h₃
  let w := (2*A₀ u*m+B₀ u)/(u-2)
  have hw : (2*A₀ u*m+B₀ u)^2=(u-2)^2*(5*(u-3)*radicalH u) := by
    linear_combination 4*A₀ u*h+centered_discriminant u
  have z : w^2=5*(u-3)*radicalH u := by
    dsimp [w]
    field_simp [d₂]
    linear_combination hw
  change ((80/(u-3))^2*w/80)^2=(80/(u-3))^3+
    105*(80/(u-3))^2+4800*(80/(u-3))+128000
  unfold radicalH at z
  field_simp [d₃]
  linear_combination 6400*z

/-- A useful branch-independent factor of the exact fourth read. -/
theorem fourth_linear_factor {R : Type*} [CommRing R]
    {g q G E L R₃ κ σ : R} (hκ : g-q*L=κ*R₃) (hσ : G+E*q=σ*R₃) :
    G*L+E*g=R₃*(σ*L+κ*E) := by
  linear_combination L*hσ+E*hκ

def secondTapNumer (x : ℚ) : ℚ := x^3-6*x^2+9*x-3
def secondTap (x : ℚ) : ℚ := (2/3)*secondTapNumer x / suffixM x

theorem second_helper_linear {x t : ℚ} (h : suffixM x≠0) :
    x^3/3-(2+t/2)*x^2+(3+2*t)*x-1-t=0 ↔ t=secondTap x := by
  unfold secondTap
  rw [eq_div_iff h]
  simp only [suffixM,secondTapNumer]
  constructor
  · intro f
    linear_combination -2*f
  · intro f
    linear_combination (-1/2:ℚ)*f

theorem second_helper_minor {x : ℚ} (h : suffixM x≠0) :
    suffixM x*(x-1-secondTap x)=x^2*(x-3)/3 := by
  unfold secondTap
  rw [mul_sub]
  have k : suffixM x*((2/3)*secondTapNumer x/suffixM x)=(2/3)*secondTapNumer x := by
    rw [mul_comm,div_mul_cancel₀ _ h]
  rw [k]
  unfold suffixM secondTapNumer
  ring

def evalH {R : Type*} [CommRing R] : List R → R → R → R
  | [],_,_ => 0
  | c::l,x,r => c*r^l.length+x*evalH l x r

def scaleArg (k : ℤ) : List ℤ → List ℤ
  | [] => []
  | c::l => c::(scaleArg k l).map (k*·)

private theorem scaleArg_len (k : ℤ) (l : List ℤ) : (scaleArg k l).length=l.length := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [scaleArg,ih]

private theorem evalH_scale (k : ℤ) (l : List ℤ) (a r : ℤ) :
    evalH (l.map (k*·)) a r=k*evalH l a r := by
  induction l with
  | nil => simp [evalH]
  | cons c l ih => simp only [List.map_cons,evalH,List.length_map,ih]; ring

private theorem evalH_arg_scale (k : ℤ) (l : List ℤ) (a r : ℤ) :
    evalH (scaleArg k l) a r=evalH l (k*a) r := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [scaleArg,evalH,List.length_map,scaleArg_len,evalH_scale,ih]
    ring

private theorem evalH_cast (l : List ℤ) (a r : ℤ) :
    (↑(evalH l a r : ℤ) : ZMod 5)=
    evalH (l.map (fun v : ℤ => (v : ZMod 5))) (a : ZMod 5) (r : ZMod 5) := by
  induction l with
  | nil => simp [evalH]
  | cons c l ih => simp [evalH,ih]

def numA : List ℤ :=
  [863173035204845230740209664000000000000000000000000000000, 836878898628227046190350336000000000000000000000000000000, 354869124010304479265197916160000000000000000000000000000, 87789374948215718206381228032000000000000000000000000000, 14279087547398345999769403392000000000000000000000000000, 1632137319226464429741535395840000000000000000000000000, 136681505938281336352228245504000000000000000000000000, 8607328105887914407936131072000000000000000000000000, 413088372110864593636766515200000000000000000000000, 15104833959506197610797989888000000000000000000000, 411975677033718051191232921600000000000000000000, 7812784259323132031344312320000000000000000000, 77447335642197867330797568000000000000000000, -634356089325092055338188800000000000000000, -38416094917523752542535680000000000000000, -606434370466469734514688000000000000000, -1081451658352985427148800000000000000, 134122958805943713792000000000000000, 2529544311998144053248000000000000, 13363935819372429312000000000000, -240067595735260938240000000000, -5181977877362700288000000000, -33715918800463603200000000, 152560285719211200000000, 4194286927392486000000, 25745373304788000000, -10071059804790000, -837765489420000, -2645036299200, 7668911400, 42007017]

def numB : List ℤ :=
  [408012464119937346463334400000000000000000000000000000, 104553193930733945031229440000000000000000000000000000, -62763792332199737123930112000000000000000000000000000, -36476872121863187750662963200000000000000000000000000, -8494003801789214172276326400000000000000000000000000, -1185435358561720237163544576000000000000000000000000, -112444465243502828958253056000000000000000000000000, -7708546922246319289443287040000000000000000000000, -394676107987236850658967552000000000000000000000, -15302840371949349660052684800000000000000000000, -446904855839808369878630400000000000000000000, -9461670960145794557018112000000000000000000, -126408877439106991679078400000000000000000, -300529034001972807598080000000000000000, 31128563423894348759040000000000000000, 803805068252438278963200000000000000, 9742152087922236456960000000000000, 27417389558006808576000000000000, -1150266998069880422400000000000, -21651168008350679040000000000, -166988844906633216000000000, 17370932093683200000000, 13724147202981120000000, 141534357097950000000, 634359148727400000, 142864413120000, -12774284064000, -59165451000, -92745540]

def numA5 : List ℤ := (scaleArg 5 numA).map (· / (5^30))
def numB5 : List ℤ := ((scaleArg 5 numB).map (5*·)).map (· / (5^30))

def receiptNum (a b d : ℤ) : ℤ :=
  evalH numA a (d^2)+b*d*evalH numB a (d^2)

def receiptNum5 (a b d : ℤ) : ℤ :=
  evalH numA5 a (d^2)+b*d*evalH numB5 a (d^2)

set_option maxRecDepth 12000 in
private theorem receipt_scaleA :
    scaleArg 5 numA=numA5.map ((5^30)*·) := by decide +kernel

set_option maxRecDepth 12000 in
private theorem receipt_scaleB :
    (scaleArg 5 numB).map (5*·)=numB5.map ((5^30)*·) := by decide +kernel

theorem receipt_scale (a b d : ℤ) :
    receiptNum (5*a) (5*b) d=5^30*receiptNum5 a b d := by
  unfold receiptNum receiptNum5
  have ha := congrArg (fun l => evalH l a (d^2)) receipt_scaleA
  rw [evalH_arg_scale,evalH_scale] at ha
  rw [ha]
  have hb := congrArg (fun l => evalH l a (d^2)) receipt_scaleB
  rw [evalH_scale,evalH_arg_scale,evalH_scale] at hb
  linear_combination b*d*hb

def receiptMod (a b d : ZMod 5) : ZMod 5 :=
  evalH (numA.map (fun v : ℤ => (v : ZMod 5))) a (d^2)+
  b*d*evalH (numB.map (fun v : ℤ => (v : ZMod 5))) a (d^2)

def receiptMod5 (a b d : ZMod 5) : ZMod 5 :=
  evalH (numA5.map (fun v : ℤ => (v : ZMod 5))) a (d^2)+
  b*d*evalH (numB5.map (fun v : ℤ => (v : ZMod 5))) a (d^2)

private theorem receipt_cast (a b d : ℤ) :
    (receiptNum a b d : ZMod 5)=receiptMod a b d := by
  simp [receiptNum,receiptMod,evalH_cast]

private theorem receipt_cast5 (a b d : ℤ) :
    (receiptNum5 a b d : ZMod 5)=receiptMod5 a b d := by
  simp [receiptNum5,receiptMod5,evalH_cast]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
private theorem base_residue : ∀ a b d : ZMod 5,
    receiptMod a b d=2*a^30 := by decide +kernel

def curve5 {R : Type*} [CommRing R] (a d : R) : R :=
  a^3+21*a^2*d^2+192*a*d^4+1024*d^6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
private theorem scaled_residue : ∀ a b d : ZMod 5,
    d≠0 → b=0 → curve5 a d=0 → receiptMod5 a b d≠0 := by decide +kernel

private theorem five_dvd_of_square (s : ℤ) (h : (5:ℤ)∣s^2) : (5:ℤ)∣s := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd s 5).mp
  apply sq_eq_zero_iff.mp
  simpa only [Int.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd (s^2) 5).mpr h

private theorem odd_five_square (k : ℕ) {s n : ℤ}
    (h : s^2=(5:ℤ)^(2*k+1)*n) : (5:ℤ)∣n := by
  induction k generalizing s with
  | zero =>
    have hd : (5:ℤ)∣s := five_dvd_of_square s ⟨n, by simpa using h⟩
    obtain ⟨r,rfl⟩ := hd
    refine ⟨r^2,?_⟩
    apply mul_left_cancel₀ (a:=(5:ℤ)) (by norm_num)
    norm_num at h
    linear_combination -h
  | succ k ih =>
    have hd : (5:ℤ)∣s :=
      five_dvd_of_square s ⟨5^(2*(k+1))*n,by rw [h,pow_succ]; ring⟩
    obtain ⟨r,rfl⟩ := hd
    apply ih (s:=r)
    apply mul_left_cancel₀ (a:=(5:ℤ)^2) (by norm_num)
    rw [show 2*(k+1)+1=2*k+1+2 by omega,pow_add] at h
    linear_combination h

/-- Primitive weighted projective elliptic coordinates cannot satisfy the
squared discriminate equation. Only mod-five primitivity is needed. -/
theorem no_primitive_square {a b d s : ℤ}
    (prim : ¬((a:ZMod 5)=0 ∧ (d:ZMod 5)=0))
    (curve : b^2=a^3+105*a^2*d^2+4800*a*d^4+128000*d^6)
    (sqr : s^2=5*receiptNum a b d) : False := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have n0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (receiptNum a b d) 5).mpr
    (odd_five_square 0 (by simpa using sqr))
  rw [receipt_cast,base_residue] at n0
  have a0 : (a:ZMod 5)=0 := by
    by_contra bad
    exact (mul_ne_zero (by decide) (pow_ne_zero 30 bad)) n0
  have d0 : (d:ZMod 5)≠0 := fun e => prim ⟨a0,e⟩
  have curveMod := congrArg (Int.castRingHom (ZMod 5)) curve
  change (↑(b^2 : ℤ):ZMod 5) = ↑((a^3+105*a^2*d^2+4800*a*d^4+128000*d^6) : ℤ) at curveMod
  have b0 : (b:ZMod 5)=0 := by
    apply sq_eq_zero_iff.mp
    norm_num [Int.cast_pow,Int.cast_add,Int.cast_mul,a0] at curveMod
    rw [show (128000:ZMod 5)=0 by decide +kernel,zero_mul] at curveMod
    exact curveMod
  obtain ⟨a₁,rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp a0
  obtain ⟨b₁,rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp b0
  have c₁ : b₁^2=5*curve5 a₁ d := by
    apply mul_left_cancel₀ (a:=(25:ℤ)) (by norm_num)
    unfold curve5
    linear_combination curve
  have bb : (b₁:ZMod 5)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd b₁ 5).mpr (five_dvd_of_square b₁ ⟨_,c₁⟩)
  have cc : curve5 (a₁:ZMod 5) (d:ZMod 5)=0 := by
    have ck := (ZMod.intCast_zmod_eq_zero_iff_dvd (curve5 a₁ d) 5).mpr
      (odd_five_square 0 (by simpa using c₁))
    simpa [curve5] using ck
  have hn := scaled_residue (a₁:ZMod 5) (b₁:ZMod 5) (d:ZMod 5) d0 bb cc
  change s^2=5*receiptNum ((5:ℤ)*a₁) ((5:ℤ)*b₁) d at sqr
  rw [receipt_scale] at sqr
  have hbig : s^2=(5:ℤ)^(2*15+1)*receiptNum5 a₁ b₁ d := by
    linear_combination sqr
  have bad := (ZMod.intCast_zmod_eq_zero_iff_dvd (receiptNum5 a₁ b₁ d) 5).mpr
    (odd_five_square 15 hbig)
  rw [receipt_cast5] at bad
  exact hn bad

end RKResearch.Certified.SDIRKSevenChristoffelCentered

module

public import RKCert.ReviewedNative.LaguerreGauss76Data
import Mathlib.Tactic.IntervalCases
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact order six by an integer certificate

A common denominator clears all stage entries at once. The integer arithmetic
is in the same pair of quadratic algebras (now over ℤ), and native tree-stage
columns are homogeneous of degree one less than the rooted order. The finite
certificate checks each rooted order condition using cached integer stage
columns with kernel-checked recurrence equations. -/

namespace RKResearch.Certified.LaguerreGauss76

open FiniteRootedTree
open scoped FiniteRootedTree Matrix

private abbrev Z2 := QuadraticAlgebra ℤ 2 0
private abbrev ZCoeff := QuadraticAlgebra Z2 15 0

private structure P where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

private def P.out (x : P) : ZCoeff := ⟨⟨x.a,x.b⟩,⟨x.c,x.d⟩⟩
private def P.ofNat (n : ℕ) : P := ⟨n,0,0,0⟩

private def P.add (x y : P) : P := ⟨x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩

private def P.mul (x y : P) : P :=
  ⟨x.a*y.a + 2*x.b*y.b + 15*x.c*y.c + 30*x.d*y.d,
    x.a*y.b + x.b*y.a + 15*(x.c*y.d+x.d*y.c),
    x.a*y.c + x.c*y.a + 2*(x.b*y.d+x.d*y.b),
    x.a*y.d + x.d*y.a + x.b*y.c + x.c*y.b⟩

private theorem P.out_ofNat (n : ℕ) : (P.ofNat n).out = (n:ZCoeff) := rfl
private theorem P.out_add (x y : P) : (x.add y).out = x.out + y.out := rfl
private theorem P.out_mul (x y : P) : (x.mul y).out = x.out * y.out := by
  have hr : (15:Z2).re = 15 := rfl
  have hi : (15:Z2).im = 0 := rfl
  ext <;> simp [P.out, P.mul, hr, hi] <;> ring

private def pdot (v w : Fin 7→P) : P :=
  (List.finRange 7).foldl (fun a i => a.add ((v i).mul (w i))) (P.ofNat 0)

private theorem pdot_out (v w : Fin 7→P) :
    (pdot v w).out = (P.out ∘ v) ⬝ᵥ (P.out ∘ w) := by
  simp [pdot, dotProduct, List.finRange_succ, P.out_add, P.out_mul, P.out_ofNat,
    Fin.sum_univ_succ, add_assoc]

private def den : ℕ := 139551138371248800

private def AP : Matrix (Fin 7) (Fin 7) P := Matrix.of fun i j =>
  if i = j then P.mk (69775569185624400) 0 0 0 else
    match i.val, j.val with
    | 1, 0 => P.mk 69775569185624400 (-69775569185624400) 0 0
    | 2, 0 => P.mk 69775569185624400 69775569185624400 0 0
    | 3, 0 => P.mk (-42653073028994400) 0 8550183716865000 0
    | 3, 1 => P.mk 18412475620434000 14649583737508650 (-8322398655742500) (-6353881780706250)
    | 3, 2 => P.mk 18412475620434000 (-14649583737508650) (-8322398655742500) 6353881780706250
    | 4, 1 => P.mk (-61730686129001680) (-39916946176256660) (-4472448699557384) (-2806302629131344)
    | 4, 2 => P.mk (-61730686129001680) 39916946176256660 (-4472448699557384) 2806302629131344
    | 4, 3 => P.mk 123461372258003360 0 22900011236239648 0
    | 5, 1 => P.mk (-8813808022186720) (-2216712038116100) (-7209696038195336) (-5137611388281456)
    | 5, 2 => P.mk (-8813808022186720) 2216712038116100 (-7209696038195336) 5137611388281456
    | 5, 3 => P.mk (-14035247283556960) 0 1636976881040992 0
    | 5, 4 => P.mk 31662863327930400 0 (-1172698641775200) 0
    | 6, 1 => P.mk 44090308844492750 26333536383982975 7301340461095450 4964946260883000
    | 6, 2 => P.mk 44090308844492750 (-26333536383982975) 7301340461095450 (-4964946260883000)
    | 6, 3 => P.mk (-68391328109029000) 0 (-15335617573300400) 0
    | 6, 4 => P.mk (-19789289579956500) 0 (-7989009497093550) 0
    | 6, 5 => P.mk 0 0 8721946148203050 0
    | _, _ => P.ofNat 0

private def BP (i : Fin 7) : P :=
  match i.val with
  | 4 | 5 => P.ofNat 5
  | 6 => P.ofNat 8
  | _ => P.ofNat 0

private def AI : Matrix (Fin 7) (Fin 7) ZCoeff := AP.map P.out
private def bI : Fin 7 → ZCoeff := P.out ∘ BP

private def join (u v : Fin 7 → P) : Fin 7 → P :=
  fun i => (u i).mul (pdot (AP i) v)

private theorem join_out (u v : Fin 7 → P) :
    P.out ∘ join u v = (P.out ∘ u) * (AI *ᵥ (P.out ∘ v)) := by
  funext i
  change ((u i).mul (pdot (AP i) v)).out = (u i).out * (AI *ᵥ (P.out ∘ v)) i
  rw [P.out_mul, pdot_out]
  rfl

private def intToCoeff : ZCoeff →+* Coeff := by
  let f : Z2 →+* Q2 := QuadraticAlgebra.mapRingHom (Int.castRingHom ℚ) 2 0
  exact QuadraticAlgebra.mapRingHom f 15 0

private theorem scale_A : AI.map intToCoeff = (den:Coeff) • A := by
  funext i j
  exact (by decide +kernel : ∀ i j : Fin 7, intToCoeff (AI i j) = (den:Coeff)*A i j) i j

private theorem scale_b : intToCoeff ∘ bI = (18:Coeff) • b := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 7, intToCoeff (bI i) = (18:Coeff)*b i) i

private theorem Φ_smul {R : Type*} [CommRing R] (T : Matrix (Fin 7) (Fin 7) R)
    (r : R) (t : FiniteRootedTree) :
    Φ t (r • T) = r^((t.order:ℕ)-1) • Φ t T := by
  induction t with
  | leaf => simp [Φ, order]
  | butcherProduct t u ht hu =>
    have step : ((t ◂ u).order:ℕ)-1 = ((t.order:ℕ)-1) + (1+((u.order:ℕ)-1)) := by
      have ht := t.order.pos
      have hu := u.order.pos
      simp only [order, PNat.add_coe]
      omega
    simp only [step, Φ, ht, hu, Matrix.smul_mulVec, Matrix.mulVec_smul, pow_add, pow_one]
    funext i
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ac_rfl

private theorem natUnit (n : ℕ) (hn : n ≠ 0) : IsUnit (n:Coeff) := by
  have hu : IsUnit (n:ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
  simpa only [map_natCast] using hu.map (algebraMap ℚ Coeff)

private def Paid (t : FiniteRootedTree) : Prop :=
  (t.factorial : ZCoeff) * (bI ⬝ᵥ Φ t AI) = 18*(den:ZCoeff)^((t.order:ℕ)-1)

private theorem cancel_paid {R : Type*} [CommMonoid R] {a e d x : R}
    (he : IsUnit e) (hd : IsUnit d) (h : a * (d * (e*x)) = e*d) : a*x = 1 := by
  apply (he.mul hd).mul_left_cancel
  rw [mul_one]
  exact (by ac_rfl : e*d*(a*x) = a*(d*(e*x))).trans h

private theorem transport_paid {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : FiniteRootedTree) (d e : ℕ)
    (T : Matrix (Fin 7) (Fin 7) R) (U : Matrix (Fin 7) (Fin 7) S)
    (v : Fin 7 → R) (w : Fin 7 → S)
    (hA : T.map f = (d:S) • U) (hB : f ∘ v = (e:S) • w)
    (hd : IsUnit (d:S)) (he : IsUnit (e:S))
    (h : (t.factorial:R) * (v ⬝ᵥ Φ t T) = (e:R)*(d:R)^((t.order:ℕ)-1)) :
    (t.factorial:S) * (w ⬝ᵥ Φ t U) = 1 := by
  have ht := congrArg f h
  simp only [map_mul, map_pow, map_natCast, RingHom.map_dotProduct, map_Φ,
    hA, hB, Φ_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at ht
  exact cancel_paid he (hd.pow _) ht

private theorem native_paid {t : FiniteRootedTree} (h : Paid t) :
    (t.factorial : Coeff) * (b ⬝ᵥ Φ t A) = 1 :=
  transport_paid intToCoeff t den 18 AI A bI b scale_A scale_b
    (natUnit den (by decide)) (natUnit 18 (by decide)) h

private def PackedPaid (t : FiniteRootedTree) (v : Fin 7 → P) : Prop :=
  (P.ofNat t.factorial).mul (pdot BP v) = P.ofNat (18*den^((t.order:ℕ)-1))

private theorem finish_paid {t : FiniteRootedTree} {v : Fin 7 → P}
    (hv : Φ t AI = P.out ∘ v) (h : PackedPaid t v) : Paid t := by
  have hp := congrArg P.out h
  unfold Paid
  simp only [P.out_mul, P.out_ofNat, pdot_out, Nat.cast_mul, Nat.cast_pow] at hp
  rw [hv]
  exact hp

set_option maxRecDepth 5000
set_option maxHeartbeats 2000000

private def t0 : FiniteRootedTree := leaf
private def t1 : FiniteRootedTree := t0 ◂ t0
private def t2 : FiniteRootedTree := t0 ◂ t1
private def t3 : FiniteRootedTree := t1 ◂ t0
private def t4 : FiniteRootedTree := t0 ◂ t2
private def t5 : FiniteRootedTree := t0 ◂ t3
private def t6 : FiniteRootedTree := t1 ◂ t1
private def t7 : FiniteRootedTree := t2 ◂ t0
private def t8 : FiniteRootedTree := t3 ◂ t0
private def t9 : FiniteRootedTree := t0 ◂ t4
private def t10 : FiniteRootedTree := t0 ◂ t5
private def t11 : FiniteRootedTree := t0 ◂ t6
private def t12 : FiniteRootedTree := t0 ◂ t7
private def t13 : FiniteRootedTree := t0 ◂ t8
private def t14 : FiniteRootedTree := t1 ◂ t2
private def t15 : FiniteRootedTree := t1 ◂ t3
private def t16 : FiniteRootedTree := t2 ◂ t1
private def t17 : FiniteRootedTree := t3 ◂ t1
private def t18 : FiniteRootedTree := t4 ◂ t0
private def t19 : FiniteRootedTree := t5 ◂ t0
private def t20 : FiniteRootedTree := t6 ◂ t0
private def t21 : FiniteRootedTree := t7 ◂ t0
private def t22 : FiniteRootedTree := t8 ◂ t0
private def t23 : FiniteRootedTree := t0 ◂ t9
private def t24 : FiniteRootedTree := t0 ◂ t10
private def t25 : FiniteRootedTree := t0 ◂ t11
private def t26 : FiniteRootedTree := t0 ◂ t12
private def t27 : FiniteRootedTree := t0 ◂ t13
private def t28 : FiniteRootedTree := t0 ◂ t14
private def t29 : FiniteRootedTree := t0 ◂ t15
private def t30 : FiniteRootedTree := t0 ◂ t16
private def t31 : FiniteRootedTree := t0 ◂ t17
private def t32 : FiniteRootedTree := t0 ◂ t18
private def t33 : FiniteRootedTree := t0 ◂ t19
private def t34 : FiniteRootedTree := t0 ◂ t20
private def t35 : FiniteRootedTree := t0 ◂ t21
private def t36 : FiniteRootedTree := t0 ◂ t22
private def t37 : FiniteRootedTree := t1 ◂ t4
private def t38 : FiniteRootedTree := t1 ◂ t5
private def t39 : FiniteRootedTree := t1 ◂ t6
private def t40 : FiniteRootedTree := t1 ◂ t7
private def t41 : FiniteRootedTree := t1 ◂ t8
private def t42 : FiniteRootedTree := t2 ◂ t2
private def t43 : FiniteRootedTree := t2 ◂ t3
private def t44 : FiniteRootedTree := t3 ◂ t2
private def t45 : FiniteRootedTree := t3 ◂ t3
private def t46 : FiniteRootedTree := t4 ◂ t1
private def t47 : FiniteRootedTree := t5 ◂ t1
private def t48 : FiniteRootedTree := t6 ◂ t1
private def t49 : FiniteRootedTree := t7 ◂ t1
private def t50 : FiniteRootedTree := t8 ◂ t1
private def t51 : FiniteRootedTree := t9 ◂ t0
private def t52 : FiniteRootedTree := t10 ◂ t0
private def t53 : FiniteRootedTree := t11 ◂ t0
private def t54 : FiniteRootedTree := t12 ◂ t0
private def t55 : FiniteRootedTree := t13 ◂ t0
private def t56 : FiniteRootedTree := t14 ◂ t0
private def t57 : FiniteRootedTree := t15 ◂ t0
private def t58 : FiniteRootedTree := t16 ◂ t0
private def t59 : FiniteRootedTree := t17 ◂ t0
private def t60 : FiniteRootedTree := t18 ◂ t0
private def t61 : FiniteRootedTree := t19 ◂ t0
private def t62 : FiniteRootedTree := t20 ◂ t0
private def t63 : FiniteRootedTree := t21 ◂ t0
private def t64 : FiniteRootedTree := t22 ◂ t0
private def v0 : Fin 7 → P := fun _ => P.ofNat 1

private theorem v0_ok : Φ t0 AI = P.out ∘ v0 := rfl

private def v1 : Fin 7 → P :=
  ![(P.mk 69775569185624400 0 0 0), (P.mk 139551138371248800 (-69775569185624400) 0 0), (P.mk 139551138371248800 69775569185624400 0 0), (P.mk 63947447397498000 0 (-8094613594620000) 0), (P.mk 69775569185624400 0 13955113837124880 0), (P.mk 69775569185624400 0 (-13955113837124880) 0), (P.mk 69775569185624400 0 0 0)]

private theorem v1_ok : Φ t1 AI = P.out ∘ v1 := by
  change Φ t0 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v0 i = v1 i))

private def v2 : Fin 7 → P :=
  ![(P.mk 4868630055177857295023617875360000 0 0 0), (P.mk 14605890165533571885070853626080000 (-9737260110355714590047235750720000) 0 0), (P.mk 14605890165533571885070853626080000 9737260110355714590047235750720000 0 0), (P.mk 2536058783674438749305413002000000 0 (-517629877045034649774260760000000) 0), (P.mk 3894904044142285836018894300288000 0 973726011035571459004723575072000 0), (P.mk 3894904044142285836018894300288000 0 (-973726011035571459004723575072000) 0), (P.mk 2434315027588928647511808937680000 0 0 0)]

private theorem v2_ok : Φ t2 AI = P.out ∘ v2 := by
  change Φ t0 AI * (AI *ᵥ Φ t1 AI) = _
  rw [v0_ok, v1_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v1 i = v2 i))

private def v3 : Fin 7 → P :=
  ![(P.mk 4868630055177857295023617875360000 0 0 0), (P.mk 29211780331067143770141707252160000 (-19474520220711429180094471501440000) 0 0), (P.mk 29211780331067143770141707252160000 19474520220711429180094471501440000 0 0), (P.mk 5072117567348877498610826004000000 0 (-1035259754090069299548521520000000) 0), (P.mk 7789808088284571672037788600576000 0 1947452022071142918009447150144000 0), (P.mk 7789808088284571672037788600576000 0 (-1947452022071142918009447150144000) 0), (P.mk 4868630055177857295023617875360000 0 0 0)]

private theorem v3_ok : Φ t3 AI = P.out ∘ v3 := by
  change Φ t1 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v1_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v1 v0 i = v3 i))

private def v4 : Fin 7 → P :=
  ![(P.mk 339711433254272921775430459366197133782974784000000 0 0 0), (P.mk 1358845733017091687101721837464788535131899136000000 (-1019134299762818765326291378098591401348924352000000) 0 0), (P.mk 1358845733017091687101721837464788535131899136000000 1019134299762818765326291378098591401348924352000000 0 0), (P.mk (-63433124442559728366898695790858128891226656000000) 0 9875279200548413163082264202806103124057600000000 0), (P.mk 158532002185327363495200881037558662432054899200000 0 40765371990512750613051655123943656053956974080000 0), (P.mk 158532002185327363495200881037558662432054899200000 0 (-40765371990512750613051655123943656053956974080000) 0), (P.mk 56618572209045486962571743227699522297162464000000 0 0 0)]

private theorem v4_ok : Φ t4 AI = P.out ∘ v4 := by
  change Φ t0 AI * (AI *ᵥ Φ t2 AI) = _
  rw [v0_ok, v2_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v2 i = v4 i))

private def v5 : Fin 7 → P :=
  ![(P.mk 339711433254272921775430459366197133782974784000000 0 0 0), (P.mk 2377980032779910452428013215563379936480823488000000 (-1698557166271364608877152296830985668914873920000000) 0 0), (P.mk 2377980032779910452428013215563379936480823488000000 1698557166271364608877152296830985668914873920000000 0 0), (P.mk 80795784409538725726276383934951509622884672000000 0 (-21877123020124435599247063547892812851831200000000) 0), (P.mk 317064004370654726990401762075117324864109798400000 0 81530743981025501226103310247887312107913948160000 0), (P.mk 317064004370654726990401762075117324864109798400000 0 (-81530743981025501226103310247887312107913948160000) 0), (P.mk 113237144418090973925143486455399044594324928000000 0 0 0)]

private theorem v5_ok : Φ t5 AI = P.out ∘ v5 := by
  change Φ t0 AI * (AI *ᵥ Φ t3 AI) = _
  rw [v0_ok, v3_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v3 i = v5 i))

private def v6 : Fin 7 → P :=
  ![(P.mk 339711433254272921775430459366197133782974784000000 0 0 0), (P.mk 3397114332542729217754304593661971337829747840000000 (-2377980032779910452428013215563379936480823488000000) 0 0), (P.mk 3397114332542729217754304593661971337829747840000000 2377980032779910452428013215563379936480823488000000 0 0), (P.mk 225024693261637179819451463660761148136996000000000 0 (-53629525240797284361576391298591728827720000000000) 0), (P.mk 475596006555982090485602643112675987296164697600000 0 122296115971538251839154965371830968161870922240000 0), (P.mk 475596006555982090485602643112675987296164697600000 0 (-122296115971538251839154965371830968161870922240000) 0), (P.mk 169855716627136460887715229683098566891487392000000 0 0 0)]

private theorem v6_ok : Φ t6 AI = P.out ∘ v6 := by
  change Φ t1 AI * (AI *ᵥ Φ t1 AI) = _
  rw [v1_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v1 v1 i = v6 i))

private theorem v7_ok : Φ t7 AI = P.out ∘ v6 := by
  change Φ t2 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v2_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v2 v0 i = v6 i))

private def v8 : Fin 7 → P :=
  ![(P.mk 339711433254272921775430459366197133782974784000000 0 0 0), (P.mk 6794228665085458435508609187323942675659495680000000 (-4755960065559820904856026431126759872961646976000000) 0 0), (P.mk 6794228665085458435508609187323942675659495680000000 4755960065559820904856026431126759872961646976000000 0 0), (P.mk 450049386523274359638902927321522296273992000000000 0 (-107259050481594568723152782597183457655440000000000) 0), (P.mk 951192013111964180971205286225351974592329395200000 0 244592231943076503678309930743661936323741844480000 0), (P.mk 951192013111964180971205286225351974592329395200000 0 (-244592231943076503678309930743661936323741844480000) 0), (P.mk 339711433254272921775430459366197133782974784000000 0 0 0)]

private theorem v8_ok : Φ t8 AI = P.out ∘ v8 := by
  change Φ t3 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v3_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v3 v0 i = v8 i))

private def v9 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 118517793070905728845688045315094990687254556532182602475648000000000 (-94814234456724583076550436252075992549803645225746081980518400000000) 0 0), (P.mk 118517793070905728845688045315094990687254556532182602475648000000000 94814234456724583076550436252075992549803645225746081980518400000000 0 0), (P.mk (-28595964128935692255937879674639367362358213648693951453747200000000) 0 6877772025906211513485161731992851026903408785573551255040000000000 0), (P.mk 1580237240945409717942507270867933209163394087095768033008640000000 0 1896284689134491661531008725041519850996072904514921639610368000000 0), (P.mk 1580237240945409717942507270867933209163394087095768033008640000000 0 (-632094896378163887177002908347173283665357634838307213203456000000) 0), (P.mk 5135771033072581583313148630320782929781030783061246107278080000000 0 (-790118620472704858971253635433966604581697043547884016504320000000) 0)]

private theorem v9_ok : Φ t9 AI = P.out ∘ v9 := by
  change Φ t0 AI * (AI *ᵥ Φ t4 AI) = _
  rw [v0_ok, v4_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v4 i = v9 i))

private def v10 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 189628468913449166153100872504151985099607290451492163961036800000000 (-142221351685086874614825654378113988824705467838619122970777600000000) 0 0), (P.mk 189628468913449166153100872504151985099607290451492163961036800000000 142221351685086874614825654378113988824705467838619122970777600000000 0 0), (P.mk (-20815787728477442347953776974293642890826790561659633298060800000000) 0 4966836526829021655620084893463514807711568409535424195200000000000 0), (P.mk 2199866228694305871845717778470440662408437244216846449664000000000 0 2633973164489982230556606086755274286457035527075637482397696000000 0), (P.mk 2199866228694305871845717778470440662408437244216846449664000000000 0 (-2422786006535328866859417180022111982865825551630820223229952000000) 0), (P.mk 11472302382640805121675418214723348054460000228590854234997760000000 0 (-131991973721658352310743066708226439744506234653010786979840000000) 0)]

private theorem v10_ok : Φ t10 AI = P.out ∘ v10 := by
  change Φ t0 AI * (AI *ᵥ Φ t5 AI) = _
  rw [v0_ok, v5_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v5 i = v10 i))

private def v11 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 260739144755992603460513699693208979511960024370801725446425600000000 (-189628468913449166153100872504151985099607290451492163961036800000000) 0 0), (P.mk 260739144755992603460513699693208979511960024370801725446425600000000 189628468913449166153100872504151985099607290451492163961036800000000 0 0), (P.mk (-13035611328019192439969674273947918419295367474625315142374400000000) 0 3055901027751831797755008054934178588519728033497297135360000000000 0), (P.mk 2819495216443202025748928286072948115653480401337924866319360000000 0 3371661639845472799582203448469028721917998149636353325185024000000 0), (P.mk 2819495216443202025748928286072948115653480401337924866319360000000 0 (-4213477116692493846541831451697050682066293468423333233256448000000) 0), (P.mk 17808833732209028660037687799125913179138969674120462362717440000000 0 526134673029388154349767502017513725092684574241862442544640000000 0)]

private theorem v11_ok : Φ t11 AI = P.out ∘ v11 := by
  change Φ t0 AI * (AI *ᵥ Φ t6 AI) = _
  rw [v0_ok, v6_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v6 i = v11 i))

private theorem v12_ok : Φ t12 AI = P.out ∘ v11 := by
  change Φ t0 AI * (AI *ᵥ Φ t7 AI) = _
  rw [v0_ok, v7_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v6 i = v11 i))

private def v13 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 497774730897804061151889790323398960886469137435166930397721600000000 (-355553379212717186537064135945284972061763669596547807426944000000000) 0 0), (P.mk 497774730897804061151889790323398960886469137435166930397721600000000 355553379212717186537064135945284972061763669596547807426944000000000 0 0), (P.mk (-11581486084659525205180932755000355847907479154382314207539200000000) 0 3207206890460107982561042709969351415570631070076903738560000000000 0), (P.mk 5638990432886404051497856572145896231306960802675849732638720000000 0 6743323279690945599164406896938057443835996299272706650370048000000 0), (P.mk 5638990432886404051497856572145896231306960802675849732638720000000 0 (-8426954233384987693083662903394101364132586936846666466512896000000) 0), (P.mk 35617667464418057320075375598251826358277939348240924725434880000000 0 1052269346058776308699535004035027450185369148483724885089280000000 0)]

private theorem v13_ok : Φ t13 AI = P.out ∘ v13 := by
  change Φ t0 AI * (AI *ᵥ Φ t8 AI) = _
  rw [v0_ok, v8_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v0 v8 i = v13 i))

private def v14 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 331849820598536040767926526882265973924312758290111286931814400000000 (-237035586141811457691376090630189981374509113064365204951296000000000) 0 0), (P.mk 331849820598536040767926526882265973924312758290111286931814400000000 237035586141811457691376090630189981374509113064365204951296000000000 0 0), (P.mk (-5255434927560942531985571573602193947763944387590996986688000000000) 0 1144965528674641939889931216404842369327887657459170075520000000000 0), (P.mk 19594941787723080502487090158762371793626086679987523609307136000000 0 5056759171025311097416023266777386269322861078706457705627648000000 0), (P.mk 19594941787723080502487090158762371793626086679987523609307136000000 0 (-5056759171025311097416023266777386269322861078706457705627648000000) 0), (P.mk 3950593102363524294856268177169833022908485217739420082521600000000 0 0 0)]

private theorem v14_ok : Φ t14 AI = P.out ∘ v14 := by
  change Φ t1 AI * (AI *ᵥ Φ t2 AI) = _
  rw [v1_ok, v2_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v1 v2 i = v14 i))

private def v15 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 568885406740347498459302617512455955298821871354476491883110400000000 (-402960496441079478075339354071322968336665492209420848417203200000000) 0 0), (P.mk 568885406740347498459302617512455955298821871354476491883110400000000 402960496441079478075339354071322968336665492209420848417203200000000 0 0), (P.mk 7822987034616667792737219470238696356030126971131817510656000000000 0 (-2052996828407438744008456088315329937247585853355218002240000000000) 0), (P.mk 39189883575446161004974180317524743587252173359975047218614272000000 0 10113518342050622194832046533554772538645722157412915411255296000000 0), (P.mk 39189883575446161004974180317524743587252173359975047218614272000000 0 (-10113518342050622194832046533554772538645722157412915411255296000000) 0), (P.mk 7901186204727048589712536354339666045816970435478840165043200000000 0 0 0)]

private theorem v15_ok : Φ t15 AI = P.out ∘ v15 := by
  change Φ t1 AI * (AI *ᵥ Φ t3 AI) = _
  rw [v1_ok, v3_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v1 v3 i = v15 i))

private def v16 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 402960496441079478075339354071322968336665492209420848417203200000000 (-284442703370173749229651308756227977649410935677238245941555200000000) 0 0), (P.mk 402960496441079478075339354071322968336665492209420848417203200000000 284442703370173749229651308756227977649410935677238245941555200000000 0 0), (P.mk 10450704498397139058730005257039793329912099164927316004000000000000 0 (-2625479592744759713953421696517751121911529682084803040000000000000) 0), (P.mk 29392412681584620753730635238143557690439130019981285413960704000000 0 7585138756537966646124034900166079403984291618059686558441472000000 0), (P.mk 29392412681584620753730635238143557690439130019981285413960704000000 0 (-7585138756537966646124034900166079403984291618059686558441472000000) 0), (P.mk 5925889653545286442284402265754749534362727826609130123782400000000 0 0 0)]

private theorem v16_ok : Φ t16 AI = P.out ∘ v16 := by
  change Φ t2 AI * (AI *ᵥ Φ t1 AI) = _
  rw [v2_ok, v1_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v2 v1 i = v16 i))

private def v17 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 805920992882158956150678708142645936673330984418841696834406400000000 (-568885406740347498459302617512455955298821871354476491883110400000000) 0 0), (P.mk 805920992882158956150678708142645936673330984418841696834406400000000 568885406740347498459302617512455955298821871354476491883110400000000 0 0), (P.mk 20901408996794278117460010514079586659824198329854632008000000000000 0 (-5250959185489519427906843393035502243823059364169606080000000000000) 0), (P.mk 58784825363169241507461270476287115380878260039962570827921408000000 0 15170277513075933292248069800332158807968583236119373116882944000000 0), (P.mk 58784825363169241507461270476287115380878260039962570827921408000000 0 (-15170277513075933292248069800332158807968583236119373116882944000000) 0), (P.mk 11851779307090572884568804531509499068725455653218260247564800000000 0 0 0)]

private theorem v17_ok : Φ t17 AI = P.out ∘ v17 := by
  change Φ t3 AI * (AI *ᵥ Φ t1 AI) = _
  rw [v3_ok, v1_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v3 v1 i = v17 i))

private theorem v18_ok : Φ t18 AI = P.out ∘ v14 := by
  change Φ t4 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v4_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v4 v0 i = v14 i))

private theorem v19_ok : Φ t19 AI = P.out ∘ v15 := by
  change Φ t5 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v5_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v5 v0 i = v15 i))

private theorem v20_ok : Φ t20 AI = P.out ∘ v17 := by
  change Φ t6 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v6_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v6 v0 i = v17 i))

private theorem v21_ok : Φ t21 AI = P.out ∘ v17 := by
  change Φ t7 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v7_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v6 v0 i = v17 i))

private def v22 : Fin 7 → P :=
  ![(P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0), (P.mk 1611841985764317912301357416285291873346661968837683393668812800000000 (-1137770813480694996918605235024911910597643742708952983766220800000000) 0 0), (P.mk 1611841985764317912301357416285291873346661968837683393668812800000000 1137770813480694996918605235024911910597643742708952983766220800000000 0 0), (P.mk 41802817993588556234920021028159173319648396659709264016000000000000 0 (-10501918370979038855813686786071004487646118728339212160000000000000) 0), (P.mk 117569650726338483014922540952574230761756520079925141655842816000000 0 30340555026151866584496139600664317615937166472238746233765888000000 0), (P.mk 117569650726338483014922540952574230761756520079925141655842816000000 0 (-30340555026151866584496139600664317615937166472238746233765888000000) 0), (P.mk 23703558614181145769137609063018998137450911306436520495129600000000 0 0 0)]

private theorem v22_ok : Φ t22 AI = P.out ∘ v22 := by
  change Φ t8 AI * (AI *ᵥ Φ t0 AI) = _
  rw [v8_ok, v0_ok, ← join_out]
  exact congrArg (P.out ∘ ·)
    (funext (by decide +kernel : ∀ i : Fin 7, join v8 v0 i = v22 i))

private theorem pay0 : Paid t0 :=
  finish_paid v0_ok (by unfold PackedPaid; decide +kernel)

private theorem pay1 : Paid t1 :=
  finish_paid v1_ok (by unfold PackedPaid; decide +kernel)

private theorem pay2 : Paid t2 :=
  finish_paid v2_ok (by unfold PackedPaid; decide +kernel)

private theorem pay3 : Paid t3 :=
  finish_paid v3_ok (by unfold PackedPaid; decide +kernel)

private theorem pay4 : Paid t4 :=
  finish_paid v4_ok (by unfold PackedPaid; decide +kernel)

private theorem pay5 : Paid t5 :=
  finish_paid v5_ok (by unfold PackedPaid; decide +kernel)

private theorem pay6 : Paid t6 :=
  finish_paid v6_ok (by unfold PackedPaid; decide +kernel)

private theorem pay7 : Paid t7 :=
  finish_paid v7_ok (by unfold PackedPaid; decide +kernel)

private theorem pay8 : Paid t8 :=
  finish_paid v8_ok (by unfold PackedPaid; decide +kernel)

private theorem pay9 : Paid t9 :=
  finish_paid v9_ok (by unfold PackedPaid; decide +kernel)

private theorem pay10 : Paid t10 :=
  finish_paid v10_ok (by unfold PackedPaid; decide +kernel)

private theorem pay11 : Paid t11 :=
  finish_paid v11_ok (by unfold PackedPaid; decide +kernel)

private theorem pay12 : Paid t12 :=
  finish_paid v12_ok (by unfold PackedPaid; decide +kernel)

private theorem pay13 : Paid t13 :=
  finish_paid v13_ok (by unfold PackedPaid; decide +kernel)

private theorem pay14 : Paid t14 :=
  finish_paid v14_ok (by unfold PackedPaid; decide +kernel)

private theorem pay15 : Paid t15 :=
  finish_paid v15_ok (by unfold PackedPaid; decide +kernel)

private theorem pay16 : Paid t16 :=
  finish_paid v16_ok (by unfold PackedPaid; decide +kernel)

private theorem pay17 : Paid t17 :=
  finish_paid v17_ok (by unfold PackedPaid; decide +kernel)

private theorem pay18 : Paid t18 :=
  finish_paid v18_ok (by unfold PackedPaid; decide +kernel)

private theorem pay19 : Paid t19 :=
  finish_paid v19_ok (by unfold PackedPaid; decide +kernel)

private theorem pay20 : Paid t20 :=
  finish_paid v20_ok (by unfold PackedPaid; decide +kernel)

private theorem pay21 : Paid t21 :=
  finish_paid v21_ok (by unfold PackedPaid; decide +kernel)

private theorem pay22 : Paid t22 :=
  finish_paid v22_ok (by unfold PackedPaid; decide +kernel)

private theorem pay23 : Paid t23 := by
  apply finish_paid (v := join v0 v9)
  · change Φ t0 AI * (AI *ᵥ Φ t9 AI) = _
    rw [v0_ok, v9_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay24 : Paid t24 := by
  apply finish_paid (v := join v0 v10)
  · change Φ t0 AI * (AI *ᵥ Φ t10 AI) = _
    rw [v0_ok, v10_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay25 : Paid t25 := by
  apply finish_paid (v := join v0 v11)
  · change Φ t0 AI * (AI *ᵥ Φ t11 AI) = _
    rw [v0_ok, v11_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay26 : Paid t26 := by
  apply finish_paid (v := join v0 v11)
  · change Φ t0 AI * (AI *ᵥ Φ t12 AI) = _
    rw [v0_ok, v12_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay27 : Paid t27 := by
  apply finish_paid (v := join v0 v13)
  · change Φ t0 AI * (AI *ᵥ Φ t13 AI) = _
    rw [v0_ok, v13_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay28 : Paid t28 := by
  apply finish_paid (v := join v0 v14)
  · change Φ t0 AI * (AI *ᵥ Φ t14 AI) = _
    rw [v0_ok, v14_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay29 : Paid t29 := by
  apply finish_paid (v := join v0 v15)
  · change Φ t0 AI * (AI *ᵥ Φ t15 AI) = _
    rw [v0_ok, v15_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay30 : Paid t30 := by
  apply finish_paid (v := join v0 v16)
  · change Φ t0 AI * (AI *ᵥ Φ t16 AI) = _
    rw [v0_ok, v16_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay31 : Paid t31 := by
  apply finish_paid (v := join v0 v17)
  · change Φ t0 AI * (AI *ᵥ Φ t17 AI) = _
    rw [v0_ok, v17_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay32 : Paid t32 := by
  apply finish_paid (v := join v0 v14)
  · change Φ t0 AI * (AI *ᵥ Φ t18 AI) = _
    rw [v0_ok, v18_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay33 : Paid t33 := by
  apply finish_paid (v := join v0 v15)
  · change Φ t0 AI * (AI *ᵥ Φ t19 AI) = _
    rw [v0_ok, v19_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay34 : Paid t34 := by
  apply finish_paid (v := join v0 v17)
  · change Φ t0 AI * (AI *ᵥ Φ t20 AI) = _
    rw [v0_ok, v20_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay35 : Paid t35 := by
  apply finish_paid (v := join v0 v17)
  · change Φ t0 AI * (AI *ᵥ Φ t21 AI) = _
    rw [v0_ok, v21_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay36 : Paid t36 := by
  apply finish_paid (v := join v0 v22)
  · change Φ t0 AI * (AI *ᵥ Φ t22 AI) = _
    rw [v0_ok, v22_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay37 : Paid t37 := by
  apply finish_paid (v := join v1 v4)
  · change Φ t1 AI * (AI *ᵥ Φ t4 AI) = _
    rw [v1_ok, v4_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay38 : Paid t38 := by
  apply finish_paid (v := join v1 v5)
  · change Φ t1 AI * (AI *ᵥ Φ t5 AI) = _
    rw [v1_ok, v5_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay39 : Paid t39 := by
  apply finish_paid (v := join v1 v6)
  · change Φ t1 AI * (AI *ᵥ Φ t6 AI) = _
    rw [v1_ok, v6_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay40 : Paid t40 := by
  apply finish_paid (v := join v1 v6)
  · change Φ t1 AI * (AI *ᵥ Φ t7 AI) = _
    rw [v1_ok, v7_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay41 : Paid t41 := by
  apply finish_paid (v := join v1 v8)
  · change Φ t1 AI * (AI *ᵥ Φ t8 AI) = _
    rw [v1_ok, v8_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay42 : Paid t42 := by
  apply finish_paid (v := join v2 v2)
  · change Φ t2 AI * (AI *ᵥ Φ t2 AI) = _
    rw [v2_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay43 : Paid t43 := by
  apply finish_paid (v := join v2 v3)
  · change Φ t2 AI * (AI *ᵥ Φ t3 AI) = _
    rw [v2_ok, v3_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay44 : Paid t44 := by
  apply finish_paid (v := join v3 v2)
  · change Φ t3 AI * (AI *ᵥ Φ t2 AI) = _
    rw [v3_ok, v2_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay45 : Paid t45 := by
  apply finish_paid (v := join v3 v3)
  · change Φ t3 AI * (AI *ᵥ Φ t3 AI) = _
    rw [v3_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay46 : Paid t46 := by
  apply finish_paid (v := join v4 v1)
  · change Φ t4 AI * (AI *ᵥ Φ t1 AI) = _
    rw [v4_ok, v1_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay47 : Paid t47 := by
  apply finish_paid (v := join v5 v1)
  · change Φ t5 AI * (AI *ᵥ Φ t1 AI) = _
    rw [v5_ok, v1_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay48 : Paid t48 := by
  apply finish_paid (v := join v6 v1)
  · change Φ t6 AI * (AI *ᵥ Φ t1 AI) = _
    rw [v6_ok, v1_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay49 : Paid t49 := by
  apply finish_paid (v := join v6 v1)
  · change Φ t7 AI * (AI *ᵥ Φ t1 AI) = _
    rw [v7_ok, v1_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay50 : Paid t50 := by
  apply finish_paid (v := join v8 v1)
  · change Φ t8 AI * (AI *ᵥ Φ t1 AI) = _
    rw [v8_ok, v1_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay51 : Paid t51 := by
  apply finish_paid (v := join v9 v0)
  · change Φ t9 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v9_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay52 : Paid t52 := by
  apply finish_paid (v := join v10 v0)
  · change Φ t10 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v10_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay53 : Paid t53 := by
  apply finish_paid (v := join v11 v0)
  · change Φ t11 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v11_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay54 : Paid t54 := by
  apply finish_paid (v := join v11 v0)
  · change Φ t12 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v12_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay55 : Paid t55 := by
  apply finish_paid (v := join v13 v0)
  · change Φ t13 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v13_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay56 : Paid t56 := by
  apply finish_paid (v := join v14 v0)
  · change Φ t14 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v14_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay57 : Paid t57 := by
  apply finish_paid (v := join v15 v0)
  · change Φ t15 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v15_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay58 : Paid t58 := by
  apply finish_paid (v := join v16 v0)
  · change Φ t16 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v16_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay59 : Paid t59 := by
  apply finish_paid (v := join v17 v0)
  · change Φ t17 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v17_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay60 : Paid t60 := by
  apply finish_paid (v := join v14 v0)
  · change Φ t18 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v18_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay61 : Paid t61 := by
  apply finish_paid (v := join v15 v0)
  · change Φ t19 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v19_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay62 : Paid t62 := by
  apply finish_paid (v := join v17 v0)
  · change Φ t20 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v20_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay63 : Paid t63 := by
  apply finish_paid (v := join v17 v0)
  · change Φ t21 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v21_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

private theorem pay64 : Paid t64 := by
  apply finish_paid (v := join v22 v0)
  · change Φ t22 AI * (AI *ᵥ Φ t0 AI) = _
    rw [v22_ok, v0_ok, ← join_out]
  · unfold PackedPaid
    decide +kernel

theorem order_six : HasOrder 6 A b := by
  apply (checkOrder_iff A b 6).mp
  simp only [checkOrder, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro n hn t ht
  apply native_paid
  interval_cases n
  · have he : treesOfOrderSucc 0 = [t0] := by
      simp [treesOfOrderSucc, t0]
    rw [he] at ht
    have h : t = t0 := List.mem_singleton.mp ht
    exact h ▸ pay0
  · have he : treesOfOrderSucc 1 = [t1] := by
      simp [treesOfOrderSucc, List.finRange_succ, t0, t1]
    rw [he] at ht
    have h : t = t1 := List.mem_singleton.mp ht
    exact h ▸ pay1
  · have he : treesOfOrderSucc 2 = [t2, t3] := by
      simp [treesOfOrderSucc, List.finRange_succ, t0, t1, t2, t3]
    rw [he] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact pay2
    · exact pay3
  · have he : treesOfOrderSucc 3 = [t4, t5, t6, t7, t8] := by
      simp [treesOfOrderSucc, List.finRange_succ, t0, t1, t2, t3, t4, t5, t6, t7, t8]
    rw [he] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact pay4
    · exact pay5
    · exact pay6
    · exact pay7
    · exact pay8
  · have he : treesOfOrderSucc 4 = [t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22] := by
      simp [treesOfOrderSucc, List.finRange_succ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22]
    rw [he] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pay9
    · exact pay10
    · exact pay11
    · exact pay12
    · exact pay13
    · exact pay14
    · exact pay15
    · exact pay16
    · exact pay17
    · exact pay18
    · exact pay19
    · exact pay20
    · exact pay21
    · exact pay22
  · have he : treesOfOrderSucc 5 = [t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64] := by
      simp [treesOfOrderSucc, List.finRange_succ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64]
    rw [he] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pay23
    · exact pay24
    · exact pay25
    · exact pay26
    · exact pay27
    · exact pay28
    · exact pay29
    · exact pay30
    · exact pay31
    · exact pay32
    · exact pay33
    · exact pay34
    · exact pay35
    · exact pay36
    · exact pay37
    · exact pay38
    · exact pay39
    · exact pay40
    · exact pay41
    · exact pay42
    · exact pay43
    · exact pay44
    · exact pay45
    · exact pay46
    · exact pay47
    · exact pay48
    · exact pay49
    · exact pay50
    · exact pay51
    · exact pay52
    · exact pay53
    · exact pay54
    · exact pay55
    · exact pay56
    · exact pay57
    · exact pay58
    · exact pay59
    · exact pay60
    · exact pay61
    · exact pay62
    · exact pay63
    · exact pay64

section Specialization

variable {K : Type*} [Field K] [CharZero K]

theorem exact_map (f : Coeff →+* K) :
    (A.map f).IsLowerTriangular ∧ (∀ i, (A.map f) i i = (1/2:K)) ∧ (1/2:K) ≠ 0 ∧
      HasOrder 6 (A.map f) (f ∘ b) ∧ ¬ HasOrder 7 (A.map f) (f ∘ b) := by
  refine ⟨lowerTriangular.map f, fun i => ?_, by norm_num,
    order_six.map f, not_order_seven_map f⟩
  exact (congrArg f (diagonal i)).trans (map_gamma f)

end Specialization
end RKResearch.Certified.LaguerreGauss76

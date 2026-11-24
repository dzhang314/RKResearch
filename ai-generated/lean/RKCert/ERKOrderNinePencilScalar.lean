module

public import RKCert.ERKLowEndpointCore

@[expose] public section

/-! # Exact six-node Jacobi pencil obstruction

The divided difference and the Vieta quadratic are eliminated by
pseudo-remainders. Every division is by a fixed nonzero rational scalar
after a multiplication, never by a value of the pencil parameter.
The final twelfth degree polynomial is positive in every ordered field.
-/
namespace RKCert.Paired
variable {K : Type*} [Field K] [CharZero K]

/-- Forty-two times the monic quartic in the six-node Lobatto pencil. -/
def pencilScaled (l h : K) : K :=
  42*h^4+(42*l-84)*h^3+(56-63*l)*h^2+(27*l-14)*h+1-3*l

/-- The divided difference of the scaled quartic in its node variable. -/
def pencilDifference (l h d : K) : K :=
  42*d^3+(42*l-84+42*h)*d^2+
    (56-63*l+(42*l-84)*h+42*h^2)*d+
    (27*l-14+(56-63*l)*h+(42*l-84)*h^2+42*h^3)

def pencilK (l h d : K) : K :=
  6*d^2+(10*h-12+6*l)*d+13*h^2-20*h+10*l*h+8-9*l

omit [CharZero K] in
theorem pencil_difference_eq (l h d : K) :
    pencilScaled l d-pencilScaled l h = (d-h)*pencilDifference l h d := by
  unfold pencilScaled pencilDifference
  ring

private def pencilR1 (l h d : K) : K :=
    (-42 + 280*h - 532*h^2 + 308*h^3 + 81*l - 315*l*h + 266*l*h^2) +
    (-7*h^2)*d

private def pencilR2 (l h : K) : K :=
    3528 - 47040*h + 247352*h^2 - 656404*h^3 + 932568*h^4 - 676788*h^5 + 197127*h^6 - 13608*l + 143640*l*h - 572712*l*h^2 + 1082662*l*h^3 - 976521*l*h^4 + 338394*l*h^5 + 13122*l^2 - 102060*l^2*h + 285768*l^2*h^2 - 339570*l^2*h^3 + 145236*l^2*h^4

private def pencilR3 (l h : K) : K :=
    (4144 - 13503*l + 19035*l^2 + 1134*l^3) +
    (-21700 + 56896*l - 64911*l^2 - 10206*l^3)*h +
    (35714 - 74270*l + 64071*l^2 + 23814*l^3)*h^2 +
    (-18620 + 30366*l - 15876*l^2 - 15876*l^3)*h^3

omit [CharZero K] in
private theorem pencil_step1 (l h d : K) :
    (12:K)*pencilR1 l h d = (36)*pencilDifference l h d - ((-168*h) +
    (252)*d)*pencilK l h d := by
  unfold pencilR1 pencilDifference pencilK
  ring

omit [CharZero K] in
private theorem pencil_step2 (l h d : K) :
    (3:K)*pencilR2 l h = (49*h^4)*pencilK l h d - ((252 - 1680*h + 3276*h^2 - 1918*h^3 - 486*l + 1890*l*h - 1638*l*h^2) +
    (-42*h^2)*d)*pencilR1 l h d := by
  unfold pencilR2 pencilK pencilR1
  ring

omit [CharZero K] in
private theorem pencil_step3 (l h : K) :
    (18522:K)*pencilR3 l h = (74088)*pencilR2 l h - ((184627296 - 204205050*l + 7001316*l^2) +
    (-498389976 + 249194988*l)*h +
    (347732028)*h^2)*pencilScaled l h := by
  unfold pencilR3 pencilR2 pencilScaled
  ring

def p07 (l : K) : K :=
  92289883 + 1110230926*l + 5703489701*l^2 + 20465544477*l^3 + 83502297270*l^4 + 309198661506*l^5 + 921636478287*l^6 + 2665965319857*l^7 + 6743339317809*l^8 + 13563601314480*l^9 + 32457261226320*l^10 + 53871268752000*l^11 + 96959024870400*l^12

private def pencilBezoutLeft (l h : K) : K :=
    (-182652523284 + 384207766180*l + 2604996925832*l^2 - 10518527041722*l^3 - 6410380467015*l^4 + 95916370990167*l^5 - 323220407107185*l^6 + 659974778269884*l^7 - 2096305675486029*l^8 + 4658117468264190*l^9 - 6737861172659400*l^10 + 2045202425784000*l^11 + 146994029683200*l^12) +
    (685752203080 - 606165593796*l - 8118566823584*l^2 + 34103703682104*l^3 + 41516718646032*l^4 - 284978991747807*l^5 + 1008911498492898*l^6 - 2006944261077168*l^7 + 6686780908624803*l^8 - 13566339794125566*l^9 + 16507377665674056*l^10 - 5960549572689600*l^11 - 1244549451317760*l^12)*h +
    (-517100488800 + 240179191840*l + 6066119240160*l^2 - 23810845421160*l^3 - 36592520669586*l^4 + 204554255289048*l^5 - 673988592330900*l^6 + 1356901593478830*l^7 - 4496761484398260*l^8 + 8676838840085388*l^9 - 7555621777898544*l^10 + 45459264735360*l^11 + 2789620029987840*l^12)*h^2

private def pencilBezoutRight (l h : K) : K :=
    (44165464 - 79960944*l - 808388490*l^2 + 2164981455*l^3 + 4802341635*l^4 - 21563322417*l^5 + 55409956902*l^6 - 112393702575*l^7 + 375307789500*l^8 - 904541450400*l^9 + 388873094400*l^10) +
    (-551278224 + 309374632*l + 8914511592*l^2 - 17545914414*l^3 - 54094860855*l^4 + 219593558142*l^5 - 531087880176*l^6 + 1150614096219*l^7 - 3996780824988*l^8 + 7833066625440*l^9 - 3292458865920*l^10)*h +
    (1642401012 + 1104328680*l - 19426658874*l^2 + 48222602064*l^3 + 190833514704*l^4 - 414305353224*l^5 + 1525014397116*l^6 - 2290639487850*l^7 + 11253969348552*l^8 - 14242117014720*l^9 + 7379947169280*l^10)*h^2 +
    (-1166392080 - 1360426200*l + 12458858580*l^2 - 31235985018*l^3 - 142942884084*l^4 + 244295422308*l^5 - 973361028906*l^6 + 1386880398792*l^7 - 7259684564160*l^8 + 7379947169280*l^9)*h^3

set_option maxHeartbeats 1000000 in
omit [CharZero K] in
private theorem pencil_bezout (l h : K) :
    (4:K)*p07 l =
      pencilBezoutLeft l h*pencilScaled l h + pencilBezoutRight l h*pencilR3 l h := by
  unfold p07 pencilBezoutLeft pencilBezoutRight pencilScaled pencilR3
  ring

/-- Pseudo-remainder identities and a single Bézout identity, with no
genericity premise on the pencil parameter. -/
theorem pencil_forces_p07 {l h d : K} (hh : pencilScaled l h=0)
    (hd : pencilScaled l d=0) (hneq : d≠h) (hk : pencilK l h d=0) :
    p07 l=0 := by
  have hdiff : pencilDifference l h d=0 := by
    have e:=pencil_difference_eq l h d
    rw [hh,hd,sub_self] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (sub_ne_zero.mpr hneq)

  have e1 : pencilR1 l h d=0 := by
    have e := pencil_step1 l h d
    rw [hdiff,hk,mul_zero,mul_zero,sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have e2 : pencilR2 l h=0 := by
    have e := pencil_step2 l h d
    rw [hk,e1,mul_zero,mul_zero,sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have e3 : pencilR3 l h=0 := by
    have e := pencil_step3 l h
    rw [e2,hh,mul_zero,mul_zero,sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have e := pencil_bezout l h
  rw [hh,e3,mul_zero,mul_zero,add_zero] at e
  exact (mul_eq_zero.mp e).resolve_left (by norm_num : (4:K)≠0)

def p07Even (t : K) : K :=
  92289883 + 5703489701*t + 83502297270*t^2 + 921636478287*t^3 + 6743339317809*t^4 + 32457261226320*t^5 + 96959024870400*t^6

def p07Odd (t : K) : K :=
  1110230926 + 20465544477*t + 309198661506*t^2 + 2665965319857*t^3 + 13563601314480*t^4 + 53871268752000*t^5

def p07Low (t : K) : K :=
  8517422504153689 - 179863914652827510*t + 2499668468384316817*t^2

def p07High (t : K) : K :=
  17222087174250300741*t^3 + 154893756601595350080*t^4 + 1987477523705171199744*t^5 + 40300544937101197597065*t^6 + 1256260828724923700897757*t^7 + 15858789836479393085721441*t^8 + 145253450913856874014476960*t^9 + 899752192248888573276729600*t^10 + 3391935199985449328633856000*t^11 + 9401052503818845736796160000*t^12

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
/-- Exact positive ordered-root product for the free six-on-node pencil. -/
theorem p07_pos (l : K) : 0 < p07 l := by
  by_cases hn : 0 ≤ l
  · unfold p07
    positivity
  · let y := -l
    let t := y^2
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have ht : 0 ≤ t := sq_nonneg _
    have hA : 0 < p07Even t := by unfold p07Even; positivity
    have hB : 0 < p07Odd t := by unfold p07Odd; positivity
    have hH : 0 ≤ p07High t := by unfold p07High; positivity
    have hL : 0 < p07Low t := by
      have hp : 0 < (4*2499668468384316817:K)*p07Low t := by
        have e : (4*2499668468384316817:K)*p07Low t =
            (2*2499668468384316817*t+(-179863914652827510))^2+52811902067920237842943830328351552 := by
          unfold p07Low
          ring
        rw [e]
        positivity
      exact pos_of_mul_pos_right hp (by norm_num)
    have hsum : 0 < p07Even t+y*p07Odd t := by positivity
    have hprod : (p07Even t-y*p07Odd t)*(p07Even t+y*p07Odd t) =
        p07Low t+p07High t := by
      dsimp [t]
      unfold p07Even p07Odd p07Low p07High
      ring
    have hdiff : 0 < p07Even t-y*p07Odd t := by
      apply pos_of_mul_pos_left _ hsum.le
      rw [hprod]
      positivity
    convert hdiff using 1
    dsimp [t,y]
    unfold p07 p07Even p07Odd
    ring

/-- Distinct roots of the pencil cannot make the Vieta quadratic vanish. -/
theorem six_node_pencil_quadratic_ne_zero {l h d : K} (hh : pencilScaled l h=0)
    (hd : pencilScaled l d=0) (hneq : d≠h) : pencilK l h d≠0 := by
  intro hk
  exact (ne_of_gt (p07_pos l)) (pencil_forces_p07 hh hd hneq hk)

end Ordered
end RKCert.Paired


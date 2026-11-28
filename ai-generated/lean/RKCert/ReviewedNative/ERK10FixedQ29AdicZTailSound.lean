module
public import RKCert.ReviewedNative.ERK10FixedQ29AdicZTailCore
@[expose] public section

namespace RKResearch.Certified.ERK10ZTailCore

open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

variable {R : Type u} [Lean.Grind.CommRing R]

theorem int_ofNat_cast (n : Nat) : ((Int.ofNat n:Int):R)=(n:R) :=
  Ring.intCast_natCast n

/-- Ascending signed-integer coefficients evaluated in the coefficient ring. -/
def evalI (c : R) : List Int → R
  | [] => 0
  | a::as => (a:R)+c*evalI c as

theorem eval_zipSum (c : R) (as bs : List Int) :
    evalI c (zipSum as bs) = evalI c as + evalI c bs := by
  induction as generalizing bs with
  | nil => simp only [evalI,zipSum]; grind
  | cons a as ih =>
    cases bs with
    | nil => simp only [evalI,zipSum]; grind
    | cons b bs =>
      simp only [evalI,zipSum,Ring.intCast_add,ih]
      grind

theorem eval_scale (c : R) (a : Int) (bs : List Int) :
    evalI c (scale a bs) = (a:R)*evalI c bs := by
  induction bs with
  | nil => simp only [scale,List.map_nil,evalI]; grind
  | cons b bs ih =>
    change evalI c ((a*b)::scale a bs)=_
    rw [evalI,evalI,Ring.intCast_mul,ih]
    grind

theorem eval_conv (c : R) (as bs : List Int) :
    evalI c (conv as bs) = evalI c as * evalI c bs := by
  induction as with
  | nil => simp only [conv,evalI]; grind
  | cons a as ih =>
    rw [conv,eval_zipSum,eval_scale,evalI,evalI,Ring.intCast_zero,ih]
    grind

theorem eval_shift_zero (c : R) (bs : List Int)
    (h : evalI c bs=0) (n : Nat) :
    evalI c (List.replicate n 0++bs)=0 := by
  induction n with
  | zero => simpa only [List.replicate_zero,List.nil_append] using h
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,evalI,Ring.intCast_zero,ih]
    grind

theorem coeff_zipSum (as bs : List Int) (n : Nat) :
    (zipSum as bs)[n]?.getD 0 = as[n]?.getD 0 + bs[n]?.getD 0 := by
  induction as generalizing bs n with
  | nil => simp [zipSum]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipSum]
    | cons b bs => cases n <;> simp [zipSum,ih]

theorem length_zipSum (as bs : List Int) :
    (zipSum as bs).length ≤ max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [zipSum]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipSum]
    | cons b bs =>
      have L := ih bs
      simp only [zipSum,List.length_cons]
      omega

theorem coeff_scale (i : Int) (as : List Int) (n : Nat) :
    (scale i as)[n]?.getD 0 = i*as[n]?.getD 0 := by
  unfold scale
  rw [List.getElem?_map]
  cases as[n]? <;> simp

theorem coeff_shift (as : List Int) (m n : Nat) :
    (List.replicate m 0++as)[m+n]?.getD 0=as[n]?.getD 0 := by
  rw [List.getElem?_append_right (by simp only [List.length_replicate];omega)]
  rw [List.length_replicate, Nat.add_sub_cancel_left]

/-- A list of length at most n+1 with a zero n-th coefficient
can safely be truncated to n at any ring-valued root. -/
theorem eval_take_zeroTop (c : R) (n : Nat) (as : List Int)
    (hlen : as.length≤n+1) (hz : as[n]?.getD 0=0) :
    evalI c (as.take n)=evalI c as := by
  induction n generalizing as with
  | zero =>
    cases as with
    | nil => rfl
    | cons a as =>
      have h1 : as.length=0 := by simp only [List.length_cons] at hlen; omega
      have h2 : as=[] := List.eq_nil_of_length_eq_zero h1
      subst as
      have h3 : a=0 := by simpa using hz
      subst a
      simp only [List.take_zero,evalI,Ring.intCast_zero]
      grind
  | succ n ih =>
    cases as with
    | nil => rfl
    | cons a as =>
      have h1 : as.length≤n+1 := by simp only [List.length_cons] at hlen;omega
      have hz' : as[n]?.getD 0=0 := by simpa using hz
      simp only [List.take_succ_cons,evalI,ih as h1 hz']

/-- The leading integer of the actual decic is exactly the paid multiplier. -/
theorem decic_head : decic.length=11 ∧ decic[10]?.getD 0=(leading:Int) := by
  decide +kernel

def nextNumer (m : Nat) (xs : List Int) : List Int :=
  let a := xs[m+10]?.getD 0
  zipSum (scale leading xs) (List.replicate m 0++scale (-a) decic)

theorem next_top (m : Nat) (xs : List Int) :
    (nextNumer m xs)[m+10]?.getD 0=0 := by
  unfold nextNumer
  rw [coeff_zipSum,coeff_scale,coeff_shift,coeff_scale,decic_head.2]
  grind

theorem next_length (m : Nat) (xs : List Int) (h : xs.length≤m+11) :
    (nextNumer m xs).length≤m+11 := by
  change (zipSum (scale leading xs)
    (List.replicate m 0++scale (-(xs[m+10]?.getD 0)) decic)).length≤m+11
  refine Nat.le_trans (length_zipSum _ _) ?_
  simp only [scale,List.length_append,List.length_replicate,List.length_map,decic_head.1]
  omega

theorem eval_next (c : R) (hroot : evalI c decic=0) (m : Nat) (xs : List Int) :
    evalI c (nextNumer m xs) = (leading:R)*evalI c xs := by
  unfold nextNumer
  rw [eval_zipSum,eval_scale]
  have hv : evalI c (scale (-(xs[m+10]?.getD 0)) decic)=0 := by
    rw [eval_scale,hroot]
    grind
  rw [eval_shift_zero c _ hv,Ring.intCast_natCast]
  grind

/-- Direct fraction-free read; no quotient or division is built into it. -/
def Represents (c : R) (a : Rep) (x : R) : Prop :=
  evalI c a.nums = (a.den:R)*x

theorem reduce_den (n : Nat) (xs : List Int) (d : Nat) :
    (reduce n xs d).den=d*leading^n := by
  induction n generalizing xs d with
  | zero => simp [reduce]
  | succ n ih =>
    simp only [reduce,ih,Nat.pow_succ]
    simp [Nat.mul_assoc,Nat.mul_comm]

theorem reduce_represents (c : R) (hroot : evalI c decic=0)
    (n : Nat) (xs : List Int) (d : Nat) (x : R)
    (hl : xs.length≤n+10) (h : Represents c ⟨xs,d⟩ x) :
    Represents c (reduce n xs d) x := by
  induction n generalizing xs d with
  | zero => exact h
  | succ n ih =>
    change Represents c (reduce n ((nextNumer n xs).take (n+10)) (d*leading)) x
    apply ih _ _ (List.length_take_le _ _)
    unfold Represents
    change evalI c ((nextNumer n xs).take (n+10))=((d*leading:Nat):R)*x
    have hl' : (nextNumer n xs).length≤(n+10)+1 := next_length n xs (by omega)
    rw [eval_take_zeroTop c _ _ hl' (next_top n xs),eval_next c hroot,
        Semiring.natCast_mul]
    change evalI c xs=(d:R)*x at h
    rw [h]
    grind

theorem represents_add (c : R) {a b : Rep} {x y : R}
    (ha : Represents c a x) (hb : Represents c b y) :
    Represents c (a+b) (x+y) := by
  change evalI c (zipSum (scale (Int.ofNat b.den) a.nums)
      (scale (Int.ofNat a.den) b.nums)) = ((a.den*b.den:Nat):R)*(x+y)
  rw [eval_zipSum,eval_scale,eval_scale,int_ofNat_cast,int_ofNat_cast,
      Semiring.natCast_mul,ha,hb]
  grind

theorem represents_mul (c : R) (hroot : evalI c decic=0)
    {a b : Rep} {x y : R} (ha : Represents c a x) (hb : Represents c b y) :
    Represents c (a*b) (x*y) := by
  let p:=conv a.nums b.nums
  change Represents c (reduce (p.length-10) p (a.den*b.den)) (x*y)
  apply reduce_represents c hroot _ _ _ _ (by omega)
  change evalI c (conv a.nums b.nums)=((a.den*b.den:Nat):R)*(x*y)
  rw [eval_conv,ha,hb,Semiring.natCast_mul]
  grind

theorem represents_neg (c : R) {a : Rep} {x : R}
    (ha : Represents c a x) : Represents c (-a) (-x) := by
  change evalI c (scale (-1) a.nums)=(a.den:R)*(-x)
  rw [eval_scale,Ring.intCast_neg_one,ha]
  grind

theorem eval_zero (c : R) (a : List Int) (h : a.all (·==0)=true) :
    evalI c a=0 := by
  induction a with
  | nil => rfl
  | cons d a ih =>
    have hd : d=0 := by simpa using (Bool.and_eq_true_iff.mp h).1
    have ht : a.all (·==0)=true := (Bool.and_eq_true_iff.mp h).2
    rw [evalI,hd,Ring.intCast_zero,ih ht]
    grind

/-- To cancel, the only added hypothesis is a left inverse of the
actual representation denominator. -/
theorem check_sound (c : R) {a : Rep} {x v : R}
    (h : Represents c a x) (hz : zero a=true) (hu : v*(a.den:R)=1) :
    x=0 := by
  have hs : (a.den:R)*x=0 := h.symm.trans (eval_zero c _ hz)
  grind

end RKResearch.Certified.ERK10ZTailCore

#print axioms RKResearch.Certified.ERK10ZTailCore.reduce_represents
#print axioms RKResearch.Certified.ERK10ZTailCore.represents_add
#print axioms RKResearch.Certified.ERK10ZTailCore.represents_mul
#print axioms RKResearch.Certified.ERK10ZTailCore.represents_neg
#print axioms RKResearch.Certified.ERK10ZTailCore.check_sound

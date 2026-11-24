module

public import RKCert.ERKOrderNineH48Recipes
public import RKCert.ERKGoodPrimePoly

@[expose] public section

/-! # The terminal product as a list of executable scalar operations

The only fractional input is d, corresponding to 1/84. Polynomial
pseudo-division uses the same fixed degrees as the physical atlas.
The interpretation lemmas below are exact in every commutative ring.
-/
namespace RKCert.GoodPrimeDense
open Polynomial RKCert.Paired RKCert.Endpoint

variable {A R S : Type*} [CommRing R] [CommRing S]
variable {o : Operations A} {f : A→R}

def cubicAt (d z : R) : R := z^3+(-126*z^2+54*z-6)*d

def fAt (d u v : R) (P : R→R) : R :=
  (1-u)*(2*u-3*v+1)*cubicAt d v*P u-(1-v)^2*cubicAt d u*P v

def p0At (h x : R) : R := 3*h^2-6*x^2
def p1At (h x : R) : R := 3*h*x-4*x^2

def hatAt (h u v d : R) : Three R :=
  let F0 := fAt d u v (p0At h)
  let F1 := fAt d u v (p1At h)
  ⟨3*h^2*F1,-(3*h)*F0,4*F0-6*F1⟩

def cubicBox (d z : Box o) : Box o := z^3+(-126*z^2+54*z-6)*d

def fBox (d u v : Box o) (P : Box o→Box o) : Box o :=
  (1-u)*(2*u-3*v+1)*cubicBox d v*P u-(1-v)^2*cubicBox d u*P v

def p0Box (h x : Box o) : Box o := 3*h^2-6*x^2
def p1Box (h x : Box o) : Box o := 3*h*x-4*x^2

def hatRecipe (o : Operations A) (h u v d : A) : List A :=
  let H : Box o := ⟨h⟩
  let F0 := fBox ⟨d⟩ ⟨u⟩ ⟨v⟩ (p0Box H)
  let F1 := fBox ⟨d⟩ ⟨u⟩ ⟨v⟩ (p1Box H)
  [(3*H^2*F1).value, (-(3*H)*F0).value, (4*F0-6*F1).value]

def portAt (u v : R) : List R :=
  [-(4*u^2-5*u*v+2*v-1),3*(u-v)]

def portRecipe (o : Operations A) (u v : A) : List A :=
  let U : Box o := ⟨u⟩
  let V : Box o := ⟨v⟩
  [(-(4*U^2-5*U*V+2*V-1)).value,(3*(U-V)).value]

def w5InputRecipe (o : Operations A) (h : A) : List A :=
  let H : Box o := ⟨h⟩
  [o.zero,o.zero,(H^2).value,(-2*H).value,o.int 1]

noncomputable def w5At (h u v : R) : R[X] :=
  ofCoeffList (portAt u v) * ofCoeffList [0,0,h^2,-2*h,1]

def w6InputRecipe (o : Operations A) (d : A) (p : List A) : List A :=
  let D : Box o := ⟨d⟩
  [o.zero,o.zero,(42*D*⟨coeff o p 0⟩).value, (28*D*⟨coeff o p 1⟩).value,
    (21*D*⟨coeff o p 2⟩).value]

noncomputable def w6At (u v d : R) (p : R[X]) : R[X] :=
  ofCoeffList (portAt u v) *
    ofCoeffList [0,0,42*d*p.coeff 0,28*d*p.coeff 1,21*d*p.coeff 2]

def qRecipe (o : Operations A) (l d : A) : List A :=
  let q := pencilRecipe o l d
  [o.zero,q.a,q.b,q.c,q.d,o.int 1]

noncomputable def qAt (l d : R) : R[X] :=
  let q := pencilAt l d
  ofCoeffList [0,q.a,q.b,q.c,q.d,1]

def pseudoStepRecipe (o : Operations A) (p w : List A) (n : ℕ) : List A :=
  plus o (timesScalar o (coeff o p 2) w)
    (opposite o (timesScalar o (coeff o w n) (List.replicate (n-2) o.zero ++ p)))

noncomputable def pseudoStepAt (p w : R[X]) (n : ℕ) : R[X] :=
  C (p.coeff 2)*w - C (w.coeff n)*(X^(n-2)*p)

def pseudoRecipe (o : Operations A) (p w : List A) : List A :=
  pseudoStepRecipe o p (pseudoStepRecipe o p (pseudoStepRecipe o p
    (pseudoStepRecipe o p w 5) 4) 3) 2

noncomputable def pseudoAt (p w : R[X]) : R[X] :=
  pseudoStepAt p (pseudoStepAt p (pseudoStepAt p (pseudoStepAt p w 5) 4) 3) 2

def detRecipe (o : Operations A) (a b : List A) : A :=
  ((⟨coeff o a 0⟩ : Box o)*⟨coeff o b 1⟩ - ⟨coeff o a 1⟩*⟨coeff o b 0⟩).value

def detAt (a b : R[X]) : R :=
  a.coeff 0*b.coeff 1-a.coeff 1*b.coeff 0

def hcAt (h F0 F1 : R) : R :=
  (378*h^4-882*h^3+753*h^2-280*h+40)*F0^2 -
  (2268*h^5-3843*h^4+1302*h^3+912*h^2-660*h+120)*F0*F1 +
  (2646*h^6-2268*h^5-2268*h^4+2520*h^3-144*h^2-360*h+90)*F1^2

def hcBox (h F0 F1 : Box o) : Box o :=
  (378*h^4-882*h^3+753*h^2-280*h+40)*F0^2 -
  (2268*h^5-3843*h^4+1302*h^3+912*h^2-660*h+120)*F0*F1 +
  (2646*h^6-2268*h^5-2268*h^4+2520*h^3-144*h^2-360*h+90)*F1^2

def terminalRecipe (o : Operations A) (h u v l d : A) : A :=
  let p := hatRecipe o h u v d
  let po := portRecipe o u v
  let Q := pseudoRecipe o p (qRecipe o l d)
  let W5 := pseudoRecipe o p (times o po (w5InputRecipe o h))
  let W6 := pseudoRecipe o p (times o po (w6InputRecipe o d p))
  let D5 : Box o := ⟨detRecipe o W5 Q⟩
  let D6 : Box o := ⟨detRecipe o W6 Q⟩
  let H := hcBox ⟨h⟩ (fBox ⟨d⟩ ⟨u⟩ ⟨v⟩ (p0Box ⟨h⟩)) (fBox ⟨d⟩ ⟨u⟩ ⟨v⟩ (p1Box ⟨h⟩))
  ((⟨coeff o p 2⟩ : Box o)*D5*D6*H).value

noncomputable def hatPolyAt (h u v d : R) : R[X] :=
  let p := hatAt h u v d
  ofCoeffList [p.a,p.b,p.c]

noncomputable def terminalAt (h u v l d : R) : R :=
  let p := hatPolyAt h u v d
  let Q := pseudoAt p (qAt l d)
  let W5 := pseudoAt p (w5At h u v)
  let W6 := pseudoAt p (w6At u v d p)
  p.coeff 2*detAt W5 Q*detAt W6 Q*hcAt h (fAt d u v (p0At h)) (fAt d u v (p1At h))

section Sound

variable (s : Sound o f)
include s

theorem map_fBox (d h u v : Box o) :
    f ((fBox d u v (p0Box h)).value) = fAt (f d.value) (f u.value) (f v.value) (p0At (f h.value)) ∧
    f ((fBox d u v (p1Box h)).value) = fAt (f d.value) (f u.value) (f v.value) (p1At (f h.value)) := by
  constructor <;> simp only [fBox,cubicBox,p0Box,p1Box,p0At,p1At,fAt,cubicAt,
    Box.cast_add s,Box.cast_sub s,Box.cast_neg s,Box.cast_mul s,Box.cast_pow s,Box.cast_num s,
    Nat.cast_one,Nat.cast_ofNat]

theorem decode_hatRecipe (h u v d : A) :
    decode f (hatRecipe o h u v d) = hatPolyAt (f h) (f u) (f v) (f d) := by
  simp only [decode,hatRecipe,hatPolyAt,hatAt,List.map_cons,List.map_nil,
    Box.cast_sub s,Box.cast_neg s,Box.cast_mul s,Box.cast_pow s,Box.cast_num s,Nat.cast_ofNat,
    (map_fBox s ⟨d⟩ ⟨h⟩ ⟨u⟩ ⟨v⟩).1,(map_fBox s ⟨d⟩ ⟨h⟩ ⟨u⟩ ⟨v⟩).2]

theorem decode_portRecipe (u v : A) :
    decode f (portRecipe o u v) = ofCoeffList (portAt (f u) (f v)) := by
  simp only [decode,portRecipe,portAt,List.map_cons,List.map_nil,Box.cast_add s,Box.cast_sub s,
    Box.cast_neg s,Box.cast_mul s,Box.cast_pow s,Box.cast_num s,Nat.cast_one,Nat.cast_ofNat]

theorem decode_w5Recipe (h u v : A) :
    decode f (times o (portRecipe o u v) (w5InputRecipe o h)) = w5At (f h) (f u) (f v) := by
  rw [decode_times s,decode_portRecipe s]
  simp only [decode,w5InputRecipe,w5At,List.map_cons,List.map_nil,Box.cast_neg s,
    Box.cast_mul s,Box.cast_pow s,Box.cast_num s,Nat.cast_ofNat,s.zero,s.int,Int.cast_one]

theorem decode_w6Recipe (u v d : A) (p : List A) :
    decode f (times o (portRecipe o u v) (w6InputRecipe o d p)) =
      w6At (f u) (f v) (f d) (decode f p) := by
  rw [decode_times s,decode_portRecipe s]
  unfold w6At
  simp only [←coeff_decode s,decode,w6InputRecipe,List.map_cons,List.map_nil,
    Box.cast_mul s,Box.cast_num s,Nat.cast_ofNat,s.zero]

theorem decode_qRecipe (l d : A) :
    decode f (qRecipe o l d) = qAt (f l) (f d) := by
  have eq := map_pencilRecipe s l d
  simp only [decode,qRecipe,qAt,List.map_cons,List.map_nil,s.zero,s.int,Int.cast_one]
  rw [←eq]
  rfl

theorem decode_pseudoStepRecipe (p w : List A) (n : ℕ) :
    decode f (pseudoStepRecipe o p w n) = pseudoStepAt (decode f p) (decode f w) n := by
  simp only [pseudoStepRecipe,pseudoStepAt,decode_plus s,decode_opposite s,decode_timesScalar s,
    decode_shift s,coeff_decode s,sub_eq_add_neg]

theorem decode_pseudoRecipe (p w : List A) :
    decode f (pseudoRecipe o p w) = pseudoAt (decode f p) (decode f w) := by
  simp only [pseudoRecipe,pseudoAt,decode_pseudoStepRecipe s]

theorem eval_detRecipe (a b : List A) :
    f (detRecipe o a b) = detAt (decode f a) (decode f b) := by
  simp only [detRecipe,detAt,Box.cast_sub s,Box.cast_mul s,coeff_decode s]

theorem eval_hcBox (h F0 F1 : Box o) :
    f (hcBox h F0 F1).value = hcAt (f h.value) (f F0.value) (f F1.value) := by
  simp only [hcBox,hcAt,Box.cast_add s,Box.cast_sub s,Box.cast_mul s,Box.cast_pow s,
    Box.cast_num s,Nat.cast_ofNat]

theorem eval_terminalRecipe (h u v l d : A) :
    f (terminalRecipe o h u v l d) = terminalAt (f h) (f u) (f v) (f l) (f d) := by
  simp only [terminalRecipe,terminalAt,Box.cast_mul s,←coeff_decode s,eval_detRecipe s,
    decode_pseudoRecipe s,decode_hatRecipe s,decode_qRecipe s,decode_w5Recipe s,decode_w6Recipe s,
    eval_hcBox s,(map_fBox s ⟨d⟩ ⟨h⟩ ⟨u⟩ ⟨v⟩).1,(map_fBox s ⟨d⟩ ⟨h⟩ ⟨u⟩ ⟨v⟩).2]

end Sound
end RKCert.GoodPrimeDense

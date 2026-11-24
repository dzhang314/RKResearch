module
public import RKCert.ERKGoodPrimePoly
public import RKCert.DirkResultantTransfer
public import RKCert.LobattoFactorTables

@[expose] public section

/-! # Dense exact common-root certificates
An elimination step certifies a polynomial identity over the integers,
not an inference from fixed-prime solutions of the original equations.
Only the final univariate coprimality uses a degree-preserving good
prime, via the exact Mathlib resultant.
-/
namespace RKCert.DenseCommonRoot
open RKCert.GoodPrimeDense RKCert.FixedFactor RKCert.FixedPolynomial Polynomial
variable {K:Type*} [Field K] [CharZero K]

abbrev ZOp : Operations ℤ := scalar ℤ
abbrev UOp : Operations (List ℤ) := dense ZOp
abbrev VOp : Operations (List (List ℤ)) := dense UOp
abbrev Bi := List (List ℤ)

def checkStep (A B R Q : Bi) (L scale : List ℤ) : Prop :=
  plus UOp (times UOp (constant UOp L) A) (opposite UOp (times UOp Q B)) =
    times UOp (constant UOp scale) R

instance (A B R Q : Bi) (L scale : List ℤ) :
    Decidable (checkStep A B R Q L scale) := by
  unfold checkStep
  infer_instance

omit [CharZero K] in
theorem propagate (u v:K) {A B R Q:Bi} {L scale:List ℤ}
    (cert:checkStep A B R Q L scale)
    (a:read (read (Int.castRingHom K) u) v A=0)
    (b:read (read (Int.castRingHom K) u) v B=0)
    (unit:read (Int.castRingHom K) u scale≠0) :
    read (read (Int.castRingHom K) u) v R=0 := by
  let sf := (Sound.scalar (Int.castRingHom K)).dense u
  have h := congrArg (read (read (Int.castRingHom K) u) v) cert
  simp only [read_plus sf,read_times sf,read_opposite sf,read_constant sf,a,b,
    mul_zero,neg_zero,add_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left unit


def unitDigits (anchor : List ℤ) (c:ℤ) (m n:ℕ) : List ℤ :=
  times ZOp [c] (times ZOp (pow UOp anchor m) (List.replicate n 0 ++ [1]))

omit [CharZero K] in
theorem unitDigits_eval (u:K) (anchor:List ℤ) (c:ℤ) (m n:ℕ) :
    read (Int.castRingHom K) u (unitDigits anchor c m n)
      = (c:K)*(read (Int.castRingHom K) u anchor)^m*u^n := by
  let sf := Sound.scalar (Int.castRingHom K)
  rw [unitDigits,read_times sf,read_times sf,read_pow (sf.dense u),read_append]
  have z (j:ℕ) : read (Int.castRingHom K) u (List.replicate j 0)=0 := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [List.replicate_succ,GoodPrimeDense.read,map_zero,ih,mul_zero,add_zero]
  rw [z]
  simp only [GoodPrimeDense.read,List.length_replicate,map_one,mul_zero,add_zero,zero_add,
    mul_one,Int.coe_castRingHom]
  ring

theorem unitDigits_ne (u:K) (anchor:List ℤ) {c:ℤ} (cn:c≠0) (m n:ℕ)
    (un:u≠0) (an:read (Int.castRingHom K) u anchor≠0) :
    read (Int.castRingHom K) u (unitDigits anchor c m n)≠0 := by
  rw [unitDigits_eval]
  exact mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr cn) (pow_ne_zero _ an)) (pow_ne_zero _ un)

theorem intHorner_eval₂ {S:Type*} [CommRing S] (f:ℤ→+*S) (x:S) (v:List ℤ) :
    (intHorner v).eval₂ f x=read f x v := by
  induction v with
  | nil => simp only [intHorner,eval₂_zero,GoodPrimeDense.read]
  | cons a v ih => simp only [intHorner,eval₂_add,eval₂_C,eval₂_mul,eval₂_X,GoodPrimeDense.read,ih]

def modCheck {p:ℕ} (f g a b:List ℤ) : Prop :=
  let o := scalar (ZMod p)
  plus o (times o (a.map (Int.castRingHom (ZMod p))) (f.map (Int.castRingHom (ZMod p))))
    (times o (b.map (Int.castRingHom (ZMod p))) (g.map (Int.castRingHom (ZMod p))))=[1]

instance {p:ℕ} (f g a b:List ℤ) : Decidable (modCheck (p:=p) f g a b) := by
  unfold modCheck
  infer_instance

private theorem horner_eq_decode {S:Type*} [CommRing S] (f:ℤ→+*S) (v:List ℤ) :
    (intHorner v).map f=decode f v := by
  induction v with
  | nil => simp [intHorner,decode]
  | cons a v ih =>
    change (C a+X*intHorner v).map f=ofCoeffList (f a :: v.map f)
    rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,map_X,ofCoeffList_cons,ih]
    rfl

private theorem decode_id_map {S:Type*} [CommRing S] (f:ℤ→+*S) (v:List ℤ) :
    decode (id:S→S) (v.map f)=(intHorner v).map f := by
  rw [horner_eq_decode]
  simp [decode]

private theorem mod_coprime {p:ℕ} (f g a b:List ℤ) (h:modCheck (p:=p) f g a b) :
    IsCoprime ((intHorner f).map (Int.castRingHom (ZMod p)))
      ((intHorner g).map (Int.castRingHom (ZMod p))) := by
  let φ:=Int.castRingHom (ZMod p)
  let σ:=Sound.scalar (RingHom.id (ZMod p))
  refine ⟨(intHorner a).map φ,(intHorner b).map φ,?_⟩
  have e := congrArg (decode (id:ZMod p→ZMod p)) h
  change decode (RingHom.id (ZMod p)) _=decode (RingHom.id (ZMod p)) [1] at e
  rw [decode_plus σ,decode_times σ,decode_times σ] at e
  change decode id _*decode id _+decode id _*decode id _=decode id [1] at e
  rw [decode_id_map φ a,decode_id_map φ f,decode_id_map φ b,decode_id_map φ g] at e
  simpa only [decode,List.map_cons,List.map_nil,id_eq,ofCoeffList_cons,ofCoeffList_nil,
    mul_zero,add_zero,C_1] using e

private theorem degree_from_last {p:ℕ} (f:List ℤ) (m:ℕ) (h:f.length≤m+1)
    (hl:(readCoeff f m:ZMod p)≠0) :
    ((intHorner f).map (Int.castRingHom (ZMod p))).natDegree=m := by
  refine le_antisymm (natDegree_map_le.trans (degree_horner_le f m h)) ?_
  apply le_natDegree_of_ne_zero
  rw [coeff_map,coeff_horner]
  exact hl

/-- The check is a modular Bézout identity, combined with exact degree
bounds and both top coefficients staying nonzero. -/
theorem no_common_read {p:ℕ} [Fact p.Prime]
    (f g a b:List ℤ) (m n:ℕ) (mf:f.length≤m+1) (ng:g.length≤n+1)
    (topf:(readCoeff f m:ZMod p)≠0) (topg:(readCoeff g n:ZMod p)≠0)
    (pos:m≠0∨n≠0) (check:modCheck (p:=p) f g a b) (u:K) :
    read (Int.castRingHom K) u f≠0 ∨ read (Int.castRingHom K) u g≠0 := by
  have h:=no_common_eval_of_good_prime (q:=p) (intHorner f) (intHorner g) m n
    (degree_horner_le f m mf) (degree_horner_le g n ng)
    (degree_from_last f m mf topf) (degree_from_last g n ng topg)
    pos (mod_coprime f g a b check) u
  simpa only [←eval₂_eq_eval_map,intHorner_eval₂] using h

end RKCert.DenseCommonRoot

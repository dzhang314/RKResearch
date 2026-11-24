module

@[expose] public section

/-! Compact arithmetic certificates. Lists are in ascending degree order;
    missing coefficients are zero. No representative bounds or normalization
    are required. A multiplication step checks AB + RQ = C + X^n Q
    coefficientwise modulo the chosen characteristic, with n = R.length. -/
namespace RKCert.CompactResidue

def atCoeff (a : List Nat) (i : Nat) : Nat := a[i]?.getD 0

def convolution (a b : List Nat) (i : Nat) : Nat :=
  ((List.range (i+1)).map fun j => atCoeff a j * atCoeff b (i-j)).sum

def shiftCoeff (n : Nat) (q : List Nat) (i : Nat) : Nat :=
  if n ≤ i then atCoeff q (i-n) else 0

def equalCoeffs (p n : Nat) (lhs rhs : Nat → Nat) : Bool :=
  (List.range n).all fun i => decide (lhs i % p = rhs i % p)

def addCheck (p : Nat) (a b c : List Nat) : Bool :=
  equalCoeffs p (max a.length (max b.length c.length))
    (fun i => atCoeff a i + atCoeff b i) (atCoeff c)

def negCheck (p : Nat) (a c : List Nat) : Bool :=
  equalCoeffs p (max a.length c.length) (fun i => atCoeff a i + atCoeff c i) (fun _ => 0)

def mulCheck (p : Nat) (r a b c q : List Nat) : Bool :=
  equalCoeffs p (max (a.length+b.length) (max c.length (r.length+q.length)))
    (fun i => convolution a b i + convolution r q i)
    (fun i => atCoeff c i + shiftCoeff r.length q i)

/-- Syntax of a commutative ring expression with parameter-polynomial leaves. -/
inductive Term where
  | raw (coeffs : List Nat)
  | add (a b : Term)
  | mul (a b : Term)
  | neg (a : Term)

def Term.isZero : Term → Bool
  | .raw [] => true
  | _ => false

def Term.isOne : Term → Bool
  | .raw [1] => true
  | _ => false

def Term.int (p : Nat) (z : Int) : Term :=
  let w := (z % (p:Int)).toNat
  if w = 0 then .raw [] else .raw [w]

def Term.plus (a b : Term) : Term :=
  if a.isZero then b else if b.isZero then a else .add a b

def Term.times (a b : Term) : Term :=
  if a.isZero || b.isZero then .raw []
  else if a.isOne then b else if b.isOne then a else .mul a b

def Term.opposite (a : Term) : Term :=
  if a.isZero then .raw [] else .neg a

/-- An ordinary proof tree. Each gate cites only its local coefficient witness;
    callers use named nodes for sharing. The quotient polynomial itself is
    existential proof data, not part of the resulting value. -/
inductive Value (p : Nat) (r : List Nat) : Term → List Nat → Prop
  | raw (a) : Value p r (.raw a) a
  | add : Value p r a x → Value p r b y → addCheck p x y v = true →
      Value p r (.add a b) v
  | neg : Value p r a x → negCheck p x v = true →
      Value p r (.neg a) v
  | mul (q) : Value p r a x → Value p r b y → mulCheck p r x y v q = true →
      Value p r (.mul a b) v

/-- Certified equal evaluation of two coefficient lists, entry by entry. -/
inductive SameValues (p : Nat) (r : List Nat) : List Term → List Term → Prop
  | nil : SameValues p r [] []
  | cons : Value p r a v → Value p r b v → SameValues p r aa bb →
      SameValues p r (a::aa) (b::bb)

end RKCert.CompactResidue

/-! A Lean-core exact coefficient replay of the integer first-ghost identity.
This is independent of Mathlib and of the formal scalar ring adapter. -/

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixSlopeMinusOneCoefficientReplay

private abbrev Mon := Nat × Nat × Nat × Nat
private abbrev Poly := List (Mon × Int)

private def insert (m : Mon) (a : Int) : Poly → Poly
  | [] => if a = 0 then [] else [(m,a)]
  | (n,b)::xs =>
      if m = n then
        if a+b = 0 then xs else (m,a+b)::xs
      else (n,b)::insert m a xs

private def add (p q : Poly) : Poly :=
  q.foldl (fun cs (m,a) => insert m a cs) p

private def neg (p : Poly) : Poly := p.map fun (m,a) => (m,-a)

private def mm (m n : Mon) : Mon :=
  (m.1+n.1,m.2.1+n.2.1,m.2.2.1+n.2.2.1,m.2.2.2+n.2.2.2)

private def mul (p q : Poly) : Poly :=
  p.foldl (fun cs (m,a) =>
    q.foldl (fun ds (n,b) => insert (mm m n) (a*b) ds) cs) []

private def mon (a : Int) (y r s z : Nat) : Poly :=
  if a = 0 then [] else [((y,r,s,z), a)]

private def rho : Poly :=
  add (add (mon (-9) 2 2 0 0) (mon 48 2 0 1 0))
    (add (add (mon 8 1 2 0 1) (mon 3 1 1 1 0))
      (add (mon (-42) 1 0 1 1) (mon (-2) 0 1 1 1)))

private def m : Poly :=
  add (mon 1 2 0 0 0) (add (mon 1 1 1 0 0) (mon 1 0 0 1 0))

private def hull : Poly :=
  add (mon 15 3 0 0 0)
    (add (add (mon 16 2 1 0 0) (mon (-12) 2 0 0 1))
      (add (add (mon 18 1 0 1 0) (mon (-12) 1 1 0 1))
        (mon (-12) 0 0 1 1)))

private def delta : Poly := add (mon 2 0 2 0 0) (mon (-9) 0 0 1 0)

private def prim2 : Poly :=
  add (mon 10 2 0 1 0) (add (mon 5 3 1 0 0) (mon 3 4 0 0 0))

private def cofactor : Poly :=
  add (mon 4 1 2 0 0) (add (mon (-21) 1 0 1 0) (mon (-1) 0 1 1 0))

private def difference : Poly :=
  add (mul delta prim2)
    (neg (add (mul (mon 6 0 0 0 0) (mul m rho)) (mul hull cofactor)))

/-- Every coefficient of the cleared four-variable integer identity is zero.
Ordinary kernel reduction, not compiler-backed native_decide, verifies
the sparse coefficient computation. -/
theorem exact_integer_coefficients : difference = [] := by
  decide

#print axioms exact_integer_coefficients

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixSlopeMinusOneCoefficientReplay

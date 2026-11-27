module

public import RKCert.ReviewedNative.DIRKOrderTenOneOffSharedScalar

@[expose] public section

/-! # All-fixed one-local DIRK10 absent-column separators

The finite inputs are fixed Lobatto clocks, ordinary quartic cardinals,
and a degree-four nominal donor polynomial at the first new clean
clock. The companion note contains the actual-tableau argument. -/
namespace RKResearch.Certified.Graded.AllFixedPrefixScalar

open OneOffSharedScalar

def distinct4 (a b c d : Nat) : Bool :=
  a != b && a != c && a != d && b != c && b != d && c != d

/-- At a regular interior receiver x, the signed aggregate taps of the
degree-four cardinal tests to each of the other three interior nodes
are nonzero. This does not presume an order of those other clocks. -/
def receiverTaps (ξ a b x : Nat) : Option (Nat × Nat × Nat) :=
  match tap 0 a b x ξ x, tap 0 ξ b x a x, tap 0 ξ a x b x with
  | some Sξ, some Sa, some Sb => some (Sξ,Sa,Sb)
  | _, _, _ => none

def eachOtherTap (ξ a b x : Nat) : Bool :=
  if distinct4 ξ a b x then (receiverTaps ξ a b x).isSome else true

set_option maxRecDepth 100000 in
theorem other_interior_taps_nonzero :
    interior.all (fun ξ => interior.all (fun a => interior.all (fun b =>
      interior.all (eachOtherTap ξ a b)))) = true := by decide

/-- The strict prefix observes A N = 0. Evaluate −I N / h at
the two head rows to recover the affine coefficient at ξ, then test it
against the first changed core row. All I N reads are scaled by 60. -/
def absentColumnGuard (ξ a b pa pb pξ γ ha hb J : Nat) : Bool :=
  let la := div (sub 0 pa) ha
  let lb := div (sub 0 pb) hb
  let lξ := add la (div (mul (sub lb la) (sub ξ a)) (sub b a))
  unit ha && unit hb && unit (sub b a) && mul γ (mul lξ J) != pξ

def validInteriorCase (ξ a b x : Nat) : Bool :=
  if distinct4 ξ a b x then
    match receiverTaps ξ a b x with
    | none => false
    | some (Sξ,Sa,Sb) =>
      let pξ := primitive60 0 ξ a b ξ
      let pa := primitive60 0 ξ a b a
      let pb := primitive60 0 ξ a b b
      let da := mul 36 (sub a ξ)
      let γ := div (pow ξ 3) 6
      let ha := div (mul (pow ξ 2) (pow a 3)) da
      let α := div (mul 3 (mul (sub a ξ) (sub a (mul 2 ξ)))) (pow ξ 2)
      let Jbefore := div (sub a (div ξ 2)) α
      let hbefore := div (sub (mul γ (mul Sξ Jbefore)) (mul Sa ha)) Sb
      let dafter := mul 36 (mul (sub ξ a) (sub a (mul 2 b)))
      let hafter := div (mul (pow ξ 2) (mul (pow b 3) (sub (mul 2 a) b))) dafter
      let Jafter := div (add (mul Sa ha) (mul Sb hafter)) (mul γ Sξ)
      unit pξ && unit pa && unit pb && unit da && unit (pow ξ 2) && unit α && unit dafter &&
        unit Sb && unit (mul γ Sξ) &&
        absentColumnGuard ξ a b pa pb pξ γ ha hbefore Jbefore &&
        absentColumnGuard ξ a b pa pb pξ γ ha hafter Jafter
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3500000 in
theorem all_first_change_guards :
    interior.all (fun ξ => interior.all (fun a => interior.all (fun b =>
      interior.all (validInteriorCase ξ a b)))) = true := by decide

end RKResearch.Certified.Graded.AllFixedPrefixScalar

import Lean

/-! The finite arithmetic part of the nonzero three-clean norm.
There are no Mathlib dependencies and no native compiler axioms. -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixConstantArithmetic

def grid : List Int := [2,9,22,35,42]
def red (a : Int) : Int := a % 43
def div43 (a b : Int) : Int := red (red a * (red b)^41)
def j4 (x : Int) : Int := 42*x^4-84*x^3+56*x^2-14*x+1
def j5 (x : Int) : Int := (2*x-1)*(66*x^4-132*x^3+84*x^2-18*x+1)
def h (x : Int) : Int := x*j4 x

def res (v u w : Int) : Int :=
  let k s := div43 (v^3 * h s) (6*h v)
  let K s := red (div43 (s^4) 4 - div43 ((u+v)*s^3) 3 + div43 (u*v*s*s) 2)
  let aff s l r := div43 ((u-s)*l+(s-v)*r) (u-v)
  let L := red (u+v-aff w (div43 (K v) (k v)) (div43 (K u) (k u)))
  let m1 := div43 (u*u) 2
  let m2 := div43 (u^3) 3 + k u
  let av := div43 (u*m1-m2) (v*(u-v))
  let au := div43 (m2-v*m1) (u*(u-v))
  let mark := aff w (div43 v 2) (div43 (av*k v+au*k u) (k u))
  let t1 := div43 (w*w) 2
  let t2 := div43 (w^3) 3 + k w
  let t3 := div43 (w^4) 4 + L*k w
  let tap s a b := div43 (t3-(a+b)*t2+a*b*t1) (s*(s-a)*(s-b))
  red (tap v u w * k v + tap u v w * k u + tap w v u * k w - mark*k w)

def triples : List (Int × Int × Int) :=
  grid.flatMap fun v => grid.flatMap fun u =>
    if v=u then [] else (grid.filter fun w => decide (w≠u ∧ w≠v)).map (fun w => (v,u,w))

theorem split_guard :
    grid.all (fun x => decide (red (j5 x)=0 ∧
      red (h x)≠0 ∧ x≠0 ∧ x≠1)) = true := by decide

theorem clock_receipt : triples.length = 60 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem norm_residue :
    triples.foldl (fun acc (v,u,w) => red (acc * res v u w)) 1 = 4 := by decide

end RKResearch.Certified.Graded.OrderElevenInvisibleSixConstantArithmetic

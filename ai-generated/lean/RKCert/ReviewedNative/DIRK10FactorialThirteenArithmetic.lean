module

@[expose] public section

/-! Core numeral replay for the compact factorial-localized DIRK10.
The two scaled next-tree equalities are checked directly on the literal
integer row and weight arrays without importing Mathlib. -/

namespace RKResearch.Certified.DIRK10FactorialThirteen.Arithmetic
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def D : Int := 1555848000
def A : List (List Int) := [
  [0],
  [64827000, 64827000],
  [43218000, 172872000, 43218000],
  [86436000, 0, 345744000, 86436000],
  [87127488, 0, 341397504, 149361408, 44452800],
  [94539375, 0, 626661000, -102642750, 48234375, -407484000],
  [56723625, 0, -1750329000, -437582250, 723515625, 2250423000, -64827000],
  [14060256000, 0, 691488000, 503230392000, -623831250000, -96166224000, 223926864000, -20874294000],
  [-9132871125, 0, 3133305000, -331170603750, 410554921875, 60401565000, -146541360000, 13917960000, 133623000],
  [699912184125, 0, 24785523000, 11509721070750, -12533093671875, -3000283524000, 3437975289000, 997542000, -70429905000, -69843816000],
  [5146472881200, 0, 144866736000, 77177070054000, -82164685312500, -20976338754000, 21267194277000, 510168071700, -545103871200, -563965882200, 3803184000],
  [22102294753875, 0, 491842449000, 305445795646250, -317997416953125, -86315577845000, 77329926240000, 3943578016000, -2435213221000, -2591760136000, 24586240000, 1166886000],
  [28411654500, 0, -8001504000, 1427988856500, -1819664578125, -241169634000, 682310891250, -73241260875, 2649291750, 2412920250, -167580000, 26790750, 0]
]
def b : List Int := [-110761560, 0, 0, -276718680, 0, 703465560, 737175600, -56677320, 428413860, 73347120, -16669800, 1666980, 72606240]
def c : List Int := A.map List.sum

def action (v : List Int) : List Int :=
  A.map (fun row => (List.zipWith (·*·) row v).sum)

def star : Int :=
  11*(List.zipWith (fun w x => w*x^10) b c).sum - D^11

def mixed : Int :=
  88*(List.zipWith (·*·) (List.zipWith (fun w x => w*x^2) b c)
    (action (c.map (·^7)))).sum - D^11

theorem denominator_paid : (3628800:Nat)^4 % D.natAbs = 0 := by decide +kernel
theorem paid_star : 279936*star=179*D^11 := by decide +kernel
theorem paid_mixed : 1049760*mixed=(-9809)*D^11 := by decide +kernel
theorem next_bezout : (274:Int)*179+5*(-9809)=1 := by decide +kernel

#print axioms denominator_paid
#print axioms paid_star
#print axioms paid_mixed
#print axioms next_bezout

end RKResearch.Certified.DIRK10FactorialThirteen.Arithmetic

/- Exact directed integer re-evaluation of the cubic and compatibility signs. -/
namespace RKResearch.Core.ERK149SevenClockBracket

structure Box where
  lo : Int
  hi : Int
  valid : Bool := true

def S : Int := 2^272

def int (n : Int) : Box := ⟨S*n,S*n,true⟩

def flo (a b : Int) : Int := if b < 0 then (-a)/(-b) else a/b

def cei (a b : Int) : Int := -flo (-a) b

def frac (a b : Int) : Box := ⟨flo (S*a) b,cei (S*a) b,b != 0⟩

instance : Add Box where
  add a b := ⟨a.lo+b.lo,a.hi+b.hi,a.valid && b.valid⟩

instance : Neg Box where
  neg a := ⟨-a.hi,-a.lo,a.valid⟩

instance : Sub Box where
  sub a b := a + -b

instance : Mul Box where
  mul a b :=
    let w := a.lo*b.lo
    let x := a.lo*b.hi
    let y := a.hi*b.lo
    let z := a.hi*b.hi
    ⟨flo (min (min w x) (min y z)) S,
     cei (max (max w x) (max y z)) S,a.valid && b.valid⟩

def inv (a : Box) : Box :=
  ⟨flo (S*S) a.hi, cei (S*S) a.lo,
   a.valid && ((a.lo > 0) || (a.hi < 0))⟩

instance : Div Box where
  div a b := a * inv b

def sq (a : Box) := a*a

def cube (a : Box) := a*a*a

def negB (a : Box) : Bool := a.valid && a.hi < 0

def posB (a : Box) : Bool := a.valid && a.lo > 0

def opp (a b : Box) : Bool := (posB a && negB b) || (negB a && posB b)

def pe (c : List Box) (x : Box) : Box :=
  c.foldr (fun u e => u+x*e) (int 0)

def pi (c : List Int) (x : Box) : Box := pe (c.map int) x

def cubic (x : Box) : Box × Box × Box :=
  let m := pi [20,-210,910,-1995,2303,-1323,294] x
  (-(x-int 1)*pi [-20,160,-498,735,-504,126] x/(int 6*m),
   pi [120,-1164,4634,-9387,10080,-5418,1134] x/(int 6*m),
   -pi [36,-366,1533,-3255,3647,-2037,441] x/m)

def branch (x r : Box) : Bool :=
  let (a,b,c) := cubic x
  let e (u : Int) := pe [a,b,c,int 1] ⟨u,u,true⟩
  let der := pe [b,int 2*c,int 3] r
  opp (e r.lo) (e r.hi) && (negB der || posB der)

def moment (x : Box) (k : Int) : Box :=
  frac 1 (4+k) - frac 3 (2*(3+k))*x + frac 1 (2*(2+k))*sq x

/-- The D-weighted cardinal mass at t among t,a,b,1. -/
def mass (x t a b : Box) : Box :=
  (moment x 3-(a+b+int 1)*moment x 2+(a*b+a+b)*moment x 1-
      a*b*moment x 0) / ((t-int 1)*(t-a)*(t-b))

def gate (x v w z : Box) : Box :=
  let k (u : Box) := u*(u-x)
  let V := int 1-v
  let U := int 1-w
  mass x v w z*(k z-k v)*cube V-
    mass x w v z*(k w-k z)*sq U*(int 3*V-int 2*U)

def whole : Box := ⟨3753203868948235219382629617676364842923694441533357949697030997010119745707312926, 3753203868948235219382629617676364918809198044100899782488511732303827036426330077, true⟩

def lower : Box := ⟨3753203868948235219382629617676364842923694441533357949697030997010119745707312926, 3753203868948235219382629617676364842923694441533357949697030997010119745707312927, true⟩

def upper : Box := ⟨3753203868948235219382629617676364918809198044100899782488511732303827036426330076, 3753203868948235219382629617676364918809198044100899782488511732303827036426330077, true⟩

def global0 : Box := ⟨540099686362393541478186236446653734674290046798146397442386749663034515027116854, 540099686362393541478186251623754455187798413356442544501128207806837945121956864, true⟩

def lo0 : Box := ⟨540099686362393541478186244035206955306992897538549502953189886500912437715089816, 540099686362393541478186244035206955306992897538549502953189886500912437715092352, true⟩

def hi0 : Box := ⟨540099686362393541478186244035206964125023591559734902160941785434651309203974282, 540099686362393541478186244035206964125023591559734902160941785434651309203976818, true⟩

def global1 : Box := ⟨7008309388849642360812729496009768436751562704681573917538396159773418785882585871, 7008309388849642360812729511186869157265071071239870064597137617917222215977425882, true⟩

def lo1 : Box := ⟨7008309388849642360812729503598319766862685274744618738710796618142769068342315695, 7008309388849642360812729503598319766862685274744618738710796618142769068342318231, true⟩

def hi1 : Box := ⟨7008309388849642360812729503598319827180773328589399433169069994879751176232604299, 7008309388849642360812729503598319827180773328589399433169069994879751176232606835, true⟩

def global2 : Box := ⟨5639174958869000124492039780318623395923304459446194139501670348929291976328862585, 5639174958869000124492039795495724116436812826004490286560411807073095406423702596, true⟩

def lo2 : Box := ⟨5639174958869000124492039787907177509408941531315773667184206625959400018687809049, 5639174958869000124492039787907177509408941531315773667184206625959400018687811586, true⟩

def hi2 : Box := ⟨5639174958869000124492039787907177603664309461776801618789206611306860728491119058, 5639174958869000124492039787907177603664309461776801618789206611306860728491121594, true⟩

theorem cubic_branches :
    (branch whole global0 && branch whole global1 && branch whole global2) = true := by
  decide +kernel

def pad (r : Box) : Box := ⟨r.lo - (2^80), r.hi + (2^80), r.valid⟩

theorem endpoint_branches :
    (branch lower (pad lo0) && branch lower (pad lo1) && branch lower (pad lo2) &&
      branch upper (pad hi0) && branch upper (pad hi1) && branch upper (pad hi2)) = true := by
  decide +kernel

theorem compatibility_signs :
    negB (gate lower (pad lo0) (pad lo1) (pad lo2)) = true ∧ posB (gate upper (pad hi0) (pad hi1) (pad hi2)) = true := by
  decide +kernel

end RKResearch.Core.ERK149SevenClockBracket

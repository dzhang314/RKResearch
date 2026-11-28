
/-! Cleared integer-polynomial certificate for the mixed-overlap two-cross ERK11 chart. -/
namespace RKResearch.ERK11MixedOverlapTwoCrossGate
set_option maxRecDepth 40000
set_option maxHeartbeats 0

abbrev P := List Int

def fin (p : P) : P := (p.reverse.dropWhile (· == 0)).reverse

def pa : P → P → P
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y) :: pa xs ys

def psc (c : Int) (p : P) : P := if c == 0 then [] else p.map (c * ·)
def pn (p : P) : P := psc (-1) p
def ps (p q : P) : P := pa p (pn q)

def pm (p q : P) : P :=
  if q.isEmpty then [] else
    p.foldr (fun c t => pa (psc c q) (0::t)) []

def pprod (xs : List P) : P := xs.foldl pm [1]
def psum (xs : List P) : P := xs.foldl pa []
def pw (p : P) (n : Nat) : P := pprod (List.replicate n p)

def pg (p : List P) (i : Nat) : P := p[i]?.getD []
def peq (x y : P) : Bool := fin x == fin y
def pvar : P := [0,1]
def widthB : P := [2,-2]
def rightD : P := [-1,2]

def polyEval (coefs : P) (x : P) : P :=
  coefs.foldr (fun e t => pa [e] (pm x t)) []

def ym (p q : List P) : List P :=
  p.foldr (fun c acc =>
    (List.range (max q.length (acc.length+1))).map
      (fun k => pa (pm c (pg q k)) (if k==0 then [] else pg acc (k-1)))) []

def yprod (ps : List (List P)) : List P := ps.foldl ym [[1]]

def anchors : List P := yprod [[pn pvar,[1]], [pn pvar,[2]], [pn rightD,[1]]]
def pivot : P := [ -476, 6624, -40926, 145804, -328125, 482244, -462126, 278124, -95256, 14112 ]

def r0 : P := [ 5632, -70164, 385608, -1223709, 2465496, -3264222, 2835108, -1555092, 487872, -66528 ]

def r1 : P := [ -32760, 430128, -2502090, 8404080, -17877054, 24900036, -22663998, 12978504, -4235616, 598752 ]

def r2 : P := [ 57600, -782532, 4717248, -16407822, 36086820, -51880626, 48666744, -28684656, 9624384, -1397088 ]

def numContact : P := [ 0, 0, 0, -230365598301161917842980864, 20970179022515807862171893760, -936040127596645356207715319808, 27306034209433432934848302596096, -585422644425486373406172018430464, 9835014596363958996388981098914304, -134809182176964666312159542179129728, 1550061865653833009805913446504968832, -15255478126981053132920934139437208320, 130494360560745455970486392230677114624, -981836026160504972177620764145356747264, 6560297801664802729047159941962116263232, -39231458016589017315502533466266854292552, 211337138242192622035121867740892152965768, -1031086391510189700429300358791598196734410, 4576938430184207292126259380652845581241630, -18556777014841057367714074901330351283899406, 68947626850023914284294887351139218861516474, -235429960671841751581798057246205881695337332, 740612733309985428078430280689998054679664988, -2150889507396520292289615768867691634639082516, 5777247460459432788636346001910561876230981580, -14373460999983269421343117388557027528752366504, 33166219647106714082859370173993237787572184824, -71053628801016139221663558024178373916908668776, 141450976469003232910196374778551752361091623032, -261846590328254131919896801637824392730921274160, 450945106631951647513864111139367826216229252880, -722730692211142359293810786416859713569440815920, 1078135851376544422060527360139806231020072513616, -1496964674901532153765509556915481437082769504576, 1934266643616288820307377860943673614372100511936, -2325097557926259670424539356896406913159551823872, 2598752454083411031638263638582495951634616901888, -2698911422118752527033501325394070130383976037120, 2602142792844552063320734926587801864018398046976, -2326606253322395331352502462077800710662801022208, 1926630657250991942461873602611375248572298652928, -1475321738259823247266596660054006457945114070016, 1042794694579071085090056956076031199183957213184, -678910892256785638255255755941067601916280619008, 406120242559485542132950101920653977782843006976, -222573887551210431635806071756341988890201161728, 111381857087224715700507574493623146961776967680, -50695799671111658107300348156021234580959789056, 20890341167965729110099985446988967237171281920, -7751177278203747504655105446286837096198963200, 2572837007117221292346449416729775287534878720, -757995232893727143365645493478239815482736640, 196312582007942393390393821859598953978265600, -44160783323241315513395418706123269813043200, 8496885903970418808485176528701683348275200, -1370319578609581369569446073119356747776000, 180152829030255333458128261126910115840000, -18541061341606781388923118013900652544000, 1400919575691830181143520519798128640000, -69096791410226571252899158740172800000, 1669004623435424426398530404352000000 ]

def numCross : P := [ 4854226944, -164729150208, 2671015882752, -27498658749824, 201614238558720, -1119671575159392, 4892074269069888, -17243844789769632, 49890045479234400, -119905949105692464, 241351199094466512, -408935876549827896, 584720744573450232, -705637378229470731, 717077323900996740, -610633838655038682, 432285761480251140, -251410345630716888, 118068580161455616, -43659270102216384, 12235004251303680, -2441546942833152, 308992052920320, -18630403190784 ]

def bezContact : P := [ 68, 53, 52, 96, 40, 61, 49, 97, 74, 85, 30, 89, 79, 48, 97, 26, 101, 102, 64, 8, 15, 49, 97 ]

def bezCross : P := [ 44, 23, 2, 98, 99, 7, 40, 97, 8, 26, 42, 20, 50, 15, 22, 35, 80, 52, 65, 22, 54, 92, 72, 82, 47, 98, 12, 99, 81, 1, 69, 8, 53, 58, 67, 24, 5, 63, 72, 87, 55, 80, 47, 50, 58, 28, 55, 82, 0, 101, 101, 44, 77, 60, 9, 25, 18, 68, 89, 88 ]


def scale : P := psc 66 pivot

def moment (j : Nat) : P :=
  psum ((List.range 4).map (fun i =>
    psc (27720 / Int.ofNat ((i+j+2)*(i+j+3))) (pg anchors i)))

def checkPivot : Bool :=
  let A := moment 0
  let B := moment 1
  let C := moment 2
  let D := moment 3
  let E := moment 4
  let det := ps (psum [pprod [A,C,E], psc 2 (pprod [B,C,D])])
      (psum [pprod [A,D,D],pprod [B,B,E],pprod [C,C,C]])
  peq (pa (psc 21337344000 det) (psc (55440^3) pivot)) []

def checkFits : Bool :=
  (List.range 3).all (fun j =>
    peq (psum [pm r0 (moment j), pm r1 (moment (j+1)), pm r2 (moment (j+2)),
      pm scale (moment (j+3))]) [])

-- Coefficients of the monic cubic in the cleared variable W=scale*w.
def f0 : P := pprod [scale,scale,r0]
def f1 : P := pm scale r1
def f2 : P := r2

structure R3 where
  c0 : P
  c1 : P
  c2 : P

def rc (p : P) : R3 := ⟨p,[],[]⟩
def ra (u v : R3) : R3 := ⟨pa u.c0 v.c0,pa u.c1 v.c1,pa u.c2 v.c2⟩
def rn (u : R3) : R3 := ⟨pn u.c0,pn u.c1,pn u.c2⟩
def rs (u v : R3) : R3 := ra u (rn v)
def re (p : P) (u : R3) : R3 := ⟨pm p u.c0,pm p u.c1,pm p u.c2⟩
def rx (u : R3) : R3 := ⟨pn (pm f0 u.c2),ps u.c0 (pm f1 u.c2),ps u.c1 (pm f2 u.c2)⟩
def rm (u v : R3) : R3 := ra (re u.c0 v) (rx (ra (re u.c1 v) (rx (re u.c2 v))))

def rnorm (u : R3) : P :=
  let v := rx u
  let w := rx v
  ps (psum [pprod [u.c0,v.c1,w.c2], pprod [v.c0,w.c1,u.c2], pprod [w.c0,u.c1,v.c2]])
     (psum [pprod [u.c0,w.c1,v.c2], pprod [w.c0,v.c1,u.c2], pprod [v.c0,u.c1,w.c2]])

def tracePair : R3 := ⟨pn r2,[-1],[]⟩
def prodPair : R3 := ⟨pm scale r1,r2,[1]⟩
def t4 : P := [1,-32,216,-480,330]
def u44 : List P :=
  [[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],
   [-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def evalU : P := u44.foldr (fun f t => pa (polyEval f widthB) (pm pvar t)) []

def halfForm (x : P) : R3 :=
  let xM := pm x scale
  ra (rs (rc (pm xM xM)) (re xM tracePair)) prodPair

def contact : R3 :=
  let l0 := halfForm pvar
  let l1 := rn prodPair
  let r0 := halfForm rightD
  let r1 := rn (ra (rs (rc (pm scale scale)) (re scale tracePair)) prodPair)
  ra (ra (rm l0 r0) (re t4 (rm l1 r0)))
     (ra (re (polyEval t4 widthB) (rm l0 r1)) (re evalU (rm l1 r1)))

-- Hhat = 2*scale*H, and Jhat = 2*840*scale*J.
def hhat : List P := ym anchors [r0,r1,r2,scale]
def jhat : List P := (List.range 6).map (fun j =>
  pn (psum ((List.range (6-j)).map (fun t =>
    psc (840 / Int.ofNat ((t+2)*(t+3))) (pg hhat (j+t+1))))))
def xihat : List P := yprod [jhat,[[],[1]],[[1],[-1]],[pvar,[-1]],[pn rightD,[1]]]
def scaledXi : List P := (List.range 10).map (fun i => pm (pg xihat i) (pw scale (9-i)))

-- The coefficient of U after reducing by U² - tracePair*U + prodPair.
def cross : R3 :=
  (scaledXi.foldr (fun e (z : R3 × R3) =>
    (rs (rc e) (rm prodPair z.2), ra z.1 (rm tracePair z.2))) (rc [],rc [])).2

theorem computedCofactor : checkPivot = true ∧ checkFits = true := by decide +kernel


-- Check the cleared identities on exact integer grids.  The paper proof
-- bounds their degrees by 132 and 258 by assigning W and Y weight 9.
def ev (q : P) (a : Int) : Int := q.foldr (fun x y => x+a*y) 0

structure Z3 where
  x0 : Int
  x1 : Int
  x2 : Int

def za (u v : Z3) : Z3 := ⟨u.x0+v.x0,u.x1+v.x1,u.x2+v.x2⟩
def zc (x : Int) : Z3 := ⟨x,0,0⟩
def zs (a : Int) (u : Z3) : Z3 := ⟨a*u.x0,a*u.x1,a*u.x2⟩
def zd (u v : Z3) : Z3 := za u (zs (-1) v)
def zx (f u : Z3) : Z3 := ⟨-f.x0*u.x2,u.x0-f.x1*u.x2,u.x1-f.x2*u.x2⟩
def zm (f u v : Z3) : Z3 := za (zs u.x0 v) (zx f (za (zs u.x1 v) (zx f (zs u.x2 v))))
def zn (f u : Z3) : Int :=
  let v := zx f u
  let w := zx f v
  u.x0*v.x1*w.x2+v.x0*w.x1*u.x2+w.x0*u.x1*v.x2
    -u.x0*w.x1*v.x2-w.x0*v.x1*u.x2-v.x0*u.x1*w.x2

def scalarContact (a : Int) : Bool :=
  let D := ev pivot a
  let M := 66*D
  let b := 2-2*a
  let d := 2*a-1
  let R0 := ev r0 a
  let R1 := ev r1 a
  let R2 := ev r2 a
  let f : Z3 := ⟨M^2*R0,M*R1,R2⟩
  let S : Z3 := ⟨-R2,-1,0⟩
  let P : Z3 := ⟨M*R1,R2,1⟩
  let l0 := za (zd (zc ((a*M)^2)) (zs (a*M) S)) P
  let l1 := zs (-1) P
  let r0 := za (zd (zc ((d*M)^2)) (zs (d*M) S)) P
  let r1 := zs (-1) (za (zd (zc (M^2)) (zs M S)) P)
  let U := u44.foldr (fun row val => ev row b + a*val) 0
  let q := za (za (zm f l0 r0) (zs (ev t4 a) (zm f l1 r0)))
    (za (zs (ev t4 b) (zm f l0 r1)) (zs U (zm f l1 r1)))
  1185921 * zn f q == 66^12 * D^8 * ev numContact a

def scalarCross (a : Int) : Bool :=
  let D := ev pivot a
  let M := 66*D
  let d := 2*a-1
  let R0 := ev r0 a
  let R1 := ev r1 a
  let R2 := ev r2 a
  let f : Z3 := ⟨M^2*R0,M*R1,R2⟩
  let S : Z3 := ⟨-R2,-1,0⟩
  let P : Z3 := ⟨M*R1,R2,1⟩
  let H := pprod [[-a,1],[-a,2],[-d,1],[R0,R1,R2,M]]
  let J := (List.range 6).map (fun j =>
    -(List.range (6-j)).foldl (fun val i =>
       val + 840 / Int.ofNat ((i+2)*(i+3)) * (H[j+i+1]?.getD 0)) 0)
  let X := pprod [J,[0,1],[1,-1],[a,-1],[-d,1]]
  let Y := (List.range 10).map (fun i => (X[i]?.getD 0)*M^(9-i))
  let q := (Y.foldr (fun e (z : Z3 × Z3) =>
    (zd (zc e) (zm f P z.2), za z.1 (zm f S z.2))) (zc 0,zc 0)).2
  511200087552000 * zn f q == 1680^3 * 66^27 * D^26 * ev numCross a

def grid (p : Int → Bool) (start len : Nat) : Bool :=
  (List.range len).all (fun i => p (Int.ofNat (start+i)))

theorem contactGrid0 : grid scalarContact 0 15 = true := by decide +kernel
theorem contactGrid1 : grid scalarContact 15 15 = true := by decide +kernel
theorem contactGrid2 : grid scalarContact 30 15 = true := by decide +kernel
theorem contactGrid3 : grid scalarContact 45 15 = true := by decide +kernel
theorem contactGrid4 : grid scalarContact 60 15 = true := by decide +kernel
theorem contactGrid5 : grid scalarContact 75 15 = true := by decide +kernel
theorem contactGrid6 : grid scalarContact 90 15 = true := by decide +kernel
theorem contactGrid7 : grid scalarContact 105 15 = true := by decide +kernel
theorem contactGrid8 : grid scalarContact 120 13 = true := by decide +kernel
theorem crossGrid0 : grid scalarCross 0 15 = true := by decide +kernel
theorem crossGrid1 : grid scalarCross 15 15 = true := by decide +kernel
theorem crossGrid2 : grid scalarCross 30 15 = true := by decide +kernel
theorem crossGrid3 : grid scalarCross 45 15 = true := by decide +kernel
theorem crossGrid4 : grid scalarCross 60 15 = true := by decide +kernel
theorem crossGrid5 : grid scalarCross 75 15 = true := by decide +kernel
theorem crossGrid6 : grid scalarCross 90 15 = true := by decide +kernel
theorem crossGrid7 : grid scalarCross 105 15 = true := by decide +kernel
theorem crossGrid8 : grid scalarCross 120 15 = true := by decide +kernel
theorem crossGrid9 : grid scalarCross 135 15 = true := by decide +kernel
theorem crossGrid10 : grid scalarCross 150 15 = true := by decide +kernel
theorem crossGrid11 : grid scalarCross 165 15 = true := by decide +kernel
theorem crossGrid12 : grid scalarCross 180 15 = true := by decide +kernel
theorem crossGrid13 : grid scalarCross 195 15 = true := by decide +kernel
theorem crossGrid14 : grid scalarCross 210 15 = true := by decide +kernel
theorem crossGrid15 : grid scalarCross 225 15 = true := by decide +kernel
theorem crossGrid16 : grid scalarCross 240 15 = true := by decide +kernel
theorem crossGrid17 : grid scalarCross 255 4 = true := by decide +kernel

def mod103 (p : P) : P := p.map (· % 103)
def mul103 (p q : P) : P := mod103 (pm (mod103 p) (mod103 q))

theorem coprimeNumerators :
    (fin numContact).length = 61 ∧ (fin numCross).length = 24 ∧
    (fin (mod103 numContact)).length = 61 ∧ (fin (mod103 numCross)).length = 24 ∧
    peq (mod103 (pa (mul103 bezContact numContact) (mul103 bezCross numCross))) [1] = true ∧
    (List.range 101).all (fun i => 103 % (i+2) != 0) = true := by
  decide +kernel

end RKResearch.ERK11MixedOverlapTwoCrossGate
#print axioms RKResearch.ERK11MixedOverlapTwoCrossGate.computedCofactor
#print axioms RKResearch.ERK11MixedOverlapTwoCrossGate.contactGrid0
#print axioms RKResearch.ERK11MixedOverlapTwoCrossGate.crossGrid17
#print axioms RKResearch.ERK11MixedOverlapTwoCrossGate.coprimeNumerators

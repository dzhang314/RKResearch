module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Literal integer receipts at the 30 published SoleInner density corners

The coefficient vectors are not obtained by an in-kernel solve. Each row
pays six exact denominator-cleared moment dot products, a positive top
coefficient, and opposite integer signs at its six original cages.
Only the uniform 15-cell density packet is represented here. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open scoped BigOperators

structure CornerRow where
  breakpoint : ℕ
  upper : Bool
  coefficient : Fin 7 → ℤ
  lower : Fin 6 → ℕ

namespace CornerRow

def remaining (d : CornerRow) : ℕ := 64 - d.breakpoint
def ratioNum (d : CornerRow) : ℕ := if d.upper then 6 else 2
def ratioDen (d : CornerRow) : ℕ := if d.upper then 7 else 3
def rightDen (d : CornerRow) : ℕ := d.ratioNum*d.breakpoint + d.ratioDen*d.remaining

def weight0 (d : CornerRow) : ℕ := d.ratioNum*d.breakpoint^2
def weight1 (d : CornerRow) : ℕ :=
  (d.ratioNum+d.ratioDen)*d.breakpoint*d.remaining
def weight2 (d : CornerRow) : ℕ := d.ratioDen*d.remaining^2

def bubbleDen (j : ℕ) : ℕ := (j+2)*(j+3)
def bubbleQuot (j : ℕ) : ℕ := 720720 / bubbleDen j

def clearedMoment (d : CornerRow) (j : ℕ) : ℕ :=
  d.weight0*bubbleQuot j + d.weight1*bubbleQuot (j+1) + d.weight2*bubbleQuot (j+2)

def clearedDot (d : CornerRow) (i : Fin 6) : ℤ :=
  ∑ j : Fin 7, d.coefficient j * (d.clearedMoment (i.val+j.val) : ℤ)

def clearedValue (d : CornerRow) (m : ℕ) : ℤ :=
  ∑ j : Fin 7, d.coefficient j * (m : ℤ)^j.val * (4096 : ℤ)^(6-j.val)

structure Verified (d : CornerRow) : Prop where
  breakpoint_le : d.breakpoint ≤ 64
  positive_top : 0 < d.coefficient 6
  dot_zero : ∀ i : Fin 6, d.clearedDot i = 0
  endpoint_signs : ∀ j : Fin 6,
    d.clearedValue (d.lower j) * d.clearedValue (d.lower j+1) < 0
  lower_pos : ∀ j : Fin 6, 0 < d.lower j
  upper_lt : ∀ j : Fin 6, d.lower j + 1 < 4096
  separated : ∀ j : Fin 5, d.lower j.castSucc + 1 < d.lower j.succ

theorem bubbleQuot_exact (j : Fin 14) :
    bubbleQuot j.val * bubbleDen j.val = 720720 := by
  fin_cases j <;> decide +kernel

end CornerRow

def row00 : CornerRow :=
  ⟨0, false,
    ![12, -198, 1188, -3432, 5148, -3861, 1144],
    ![557, 1222, 1988, 2754, 3415, 3884]⟩

def row01 : CornerRow :=
  ⟨1, false,
    ![52384864256937911887209433, -890523216605170690234859034, 5449458591974328603378864597, -15964810554747339984696118836, 24199126607248088666720196933, -18297343988563211018701099560, 5456721337671314280124453470],
    ![528, 1198, 1971, 2742, 3410, 3883]⟩

def row02 : CornerRow :=
  ⟨1, true,
    ![12167971096892671552077697, -207560195495705325026915106, 1272982362195345676128710973, -3735229712111927467873044324, 5668428154666232792380054797, -4289880101003838651965080140, 1280274350609848365037124430],
    ![524, 1196, 1969, 2741, 3409, 3882]⟩

def row03 : CornerRow :=
  ⟨2, false,
    ![16067503057236662431225, -280972799764972358372538, 1751235671278363205068309, -5197167222718759049857524, 7953791719497485731091365, -6058829442225090851373768, 1817621864757248842983262],
    ![502, 1177, 1955, 2732, 3404, 3881]⟩

def row04 : CornerRow :=
  ⟨2, true,
    ![2848472836414750422390265, -50135226403507085983838322, 313782247288855699306685557, -933924558398252222256348036, 1432361376425819269476997093, -1092915517973663014939622028, 328301974546855369499113246],
    ![496, 1172, 1951, 2730, 3403, 3881]⟩

def row05 : CornerRow :=
  ⟨3, false,
    ![112407045291983941604977, -2018149061063251008794506, 12792734875095924056013453, -38415728119221228477706004, 59307639981817217149544957, -45483379044983551378260840, 13718212146730421252352430],
    ![479, 1157, 1940, 2723, 3400, 3879]⟩

def row06 : CornerRow :=
  ⟨3, true,
    ![15175361350292996673716667465, -274924053451002478703677786674, 1752662171365592071725393925221, -5283986014450540167698735047812, 8181434282801023285448811618357, -6288477646892607115264572530988, 1900044475485903570981980208958],
    ![472, 1150, 1935, 2719, 3398, 3879]⟩

def row07 : CornerRow :=
  ⟨4, false,
    ![1206009275634157877, -22186498284384401154, 142824802287633095025, -433524458232304853700, 674623029814931513745, -520546170231600794424, 157767249149191925958],
    ![459, 1139, 1926, 2714, 3395, 3878]⟩

def row08 : CornerRow :=
  ⟨4, true,
    ![319351452270516605, -5940048689144855274, 38503421234581012985, -117429733038619758900, 183378058017944145785, -141877933466851459020, 43092399996100418678],
    ![451, 1131, 1920, 2710, 3393, 3877]⟩

def row09 : CornerRow :=
  ⟨5, false,
    ![123903610351625823446982313, -2331114112802429475592473402, 15219720647581754336162164837, -46651745222015251461863959668, 73122848781560118561688401877, -56737352157695794081586839464, 17272307418326953317551260606],
    ![442, 1123, 1914, 2706, 3391, 3877]⟩

def row10 : CornerRow :=
  ⟨5, true,
    ![24882755365740780006869718313, -474052671457300164747410231922, 3119303775240324807508365031237, -9612887122622630118971772856068, 15127085954120389053530025033877, -11773077843853760516977337893164, 3592678879282219476067196393086],
    ![433, 1114, 1907, 2701, 3389, 3876]⟩

def row11 : CornerRow :=
  ⟨6, false,
    ![50441032884459965137, -968779152771722266986, 6407349432328100047693, -19816498089444307146324, 31266640928382573087517, -24384240337467632948040, 7453352398973797574830],
    ![427, 1108, 1902, 2698, 3387, 3875]⟩

def row12 : CornerRow :=
  ⟨6, true,
    ![7668501044348522754022953, -149312233320185843895810834, 995933312041486503960414117, -3098231694671700700813026756, 4909441479935369053611164373, -3841433016378440955759032460, 1177265665719236115664740670],
    ![418, 1098, 1894, 2693, 3384, 3875]⟩

def row13 : CornerRow :=
  ⟨8, false,
    ![3172788505102033, -63202457555683314, 427646072608191877, -1343675122573865796, 2144965936523897773, -1687972509629852160, 519674614205645470],
    ![403, 1081, 1881, 2684, 3380, 3873]⟩

def row14 : CornerRow :=
  ⟨8, true,
    ![710143700338428145, -14361108205486309674, 98081802210192751621, -310165097835800024532, 497484265655228202637, -392927836846936544868, 121323312168421389598],
    ![393, 1070, 1872, 2678, 3377, 3872]⟩

def row15 : CornerRow :=
  ⟨10, false,
    ![75194511362380551490633, -1545284319961613979163482, 10661548122665678825233317, -33956082106218364406702388, 54753478542716058187467957, -43425147809819393160481224, 13452855179769401933382846],
    ![383, 1058, 1862, 2671, 3373, 3871]⟩

def row16 : CornerRow :=
  ⟨10, true,
    ![24645957691929214412017, -514478776168402047210978, 3584301298263005639256333, -11492972405254996455840612, 18625012463067029439770493, -14828784106646460474485676, 4608087000981228298456494],
    ![374, 1047, 1852, 2665, 3370, 3870]⟩

def row17 : CornerRow :=
  ⟨12, false,
    ![206037559128985, -4349403690172618, 30519755582906469, -98359205643052244, 160006807070982245, -127775324309246328, 39802519550123902],
    ![367, 1038, 1845, 2660, 3367, 3869]⟩

def row18 : CornerRow :=
  ⟨12, true,
    ![38145202645236940785, -817999183788629715378, 5796759282850632092733, -18810870957513291193284, 30757991397283314147357, -24660174246095245755612, 7706311755587158956814],
    ![359, 1027, 1835, 2653, 3363, 3868]⟩

def row19 : CornerRow :=
  ⟨16, false,
    ![2739929744293, -60437868077334, 436162680334557, -1433847957709596, 2367578998594953, -1912862932926660, 601501718115870],
    ![344, 1004, 1814, 2639, 3356, 3866]⟩

def row20 : CornerRow :=
  ⟨16, true,
    ![1067262797437, -23898644734206, 174142322389013, -576411803188364, 956695314008577, -776083830447640, 244838164229230],
    ![336, 993, 1804, 2631, 3352, 3864]⟩

def row21 : CornerRow :=
  ⟨20, false,
    ![648150362465127073, -14800164536534230842, 109251606727488908077, -365038013970290975028, 610239698858632187917, -497865077991336942744, 157797502450044497326],
    ![327, 977, 1788, 2620, 3346, 3862]⟩

def row22 : CornerRow :=
  ⟨20, true,
    ![203670415780023123553, -4715572600518810088242, 35128371744108128107597, -118147807279325675645508, 198501708597884830804237, -162590824724026325653884, 51699084792158039156206],
    ![321, 966, 1778, 2612, 3341, 3861]⟩

def row23 : CornerRow :=
  ⟨24, false,
    ![8540147423813, -200565830025066, 1508677516544825, -5110606886685300, 8634085112443505, -7103507493681456, 2266934285397782],
    ![314, 954, 1765, 2603, 3336, 3859]⟩

def row24 : CornerRow :=
  ⟨24, true,
    ![2148403661822016861, -51089330010274203186, 387555942398961472785, -1320976050619444404900, 2242360677414791850345, -1851863681839663441092, 592818803971427220902],
    ![309, 944, 1755, 2595, 3332, 3858]⟩

def row25 : CornerRow :=
  ⟨32, false,
    ![4378466755, -107380930668, 832372148509, -2883469264104, 4957167227155, -4136008700538, 1335256092742],
    ![296, 918, 1726, 2572, 3319, 3854]⟩

def row26 : CornerRow :=
  ⟨32, true,
    ![1792739604715, -44394585779412, 346496596087477, -1206539107155096, 2082676586851003, -1743389949504918, 564359649368086],
    ![292, 910, 1717, 2564, 3315, 3852]⟩

def row27 : CornerRow :=
  ⟨48, false,
    ![99364881397, -2581901963806, 20881655882373, -74747017440524, 131910570545897, -112445075568540, 36957747485230],
    ![275, 869, 1665, 2520, 3288, 3843]⟩

def row28 : CornerRow :=
  ⟨48, true,
    ![40129113326669085, -1047462127076968614, 8500856268928549581, -30512282087644340412, 53965986113263178097, -46086767000187287088, 15170913550221055198],
    ![273, 865, 1660, 2515, 3285, 3842]⟩

def row29 : CornerRow :=
  ⟨64, true,
    ![1, -27, 225, -825, 1485, -1287, 429],
    ![262, 836, 1619, 2476, 3259, 3833]⟩

def rowAt : ℕ → CornerRow
  | 0 => row00
  | 1 => row01
  | 2 => row02
  | 3 => row03
  | 4 => row04
  | 5 => row05
  | 6 => row06
  | 7 => row07
  | 8 => row08
  | 9 => row09
  | 10 => row10
  | 11 => row11
  | 12 => row12
  | 13 => row13
  | 14 => row14
  | 15 => row15
  | 16 => row16
  | 17 => row17
  | 18 => row18
  | 19 => row19
  | 20 => row20
  | 21 => row21
  | 22 => row22
  | 23 => row23
  | 24 => row24
  | 25 => row25
  | 26 => row26
  | 27 => row27
  | 28 => row28
  | _ => row29

/-- Exactly the 30 distinct density corners, with duplicated endpoint
directions removed because the 15 cells do not use them twice. -/
def cornerRow (i : Fin 30) : CornerRow := rowAt i.val

set_option maxRecDepth 2200
set_option maxHeartbeats 600000

private theorem row00_verified : row00.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row01_verified : row01.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row02_verified : row02.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row03_verified : row03.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row04_verified : row04.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row05_verified : row05.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row06_verified : row06.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row07_verified : row07.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row08_verified : row08.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row09_verified : row09.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row10_verified : row10.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row11_verified : row11.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row12_verified : row12.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row13_verified : row13.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row14_verified : row14.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row15_verified : row15.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row16_verified : row16.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row17_verified : row17.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row18_verified : row18.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row19_verified : row19.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row20_verified : row20.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row21_verified : row21.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row22_verified : row22.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row23_verified : row23.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row24_verified : row24.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row25_verified : row25.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row26_verified : row26.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row27_verified : row27.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row28_verified : row28.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel

private theorem row29_verified : row29.Verified := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_,?_,?_,?_⟩
  all_goals
    intro j
    fin_cases j <;> decide +kernel


/-- Kernel-checkable receipts for every literal row; no native evaluator
or oracle is invoked for these integer identities. -/
theorem cornerRow_verified (i : Fin 30) : (cornerRow i).Verified := by
  fin_cases i
  · exact row00_verified
  · exact row01_verified
  · exact row02_verified
  · exact row03_verified
  · exact row04_verified
  · exact row05_verified
  · exact row06_verified
  · exact row07_verified
  · exact row08_verified
  · exact row09_verified
  · exact row10_verified
  · exact row11_verified
  · exact row12_verified
  · exact row13_verified
  · exact row14_verified
  · exact row15_verified
  · exact row16_verified
  · exact row17_verified
  · exact row18_verified
  · exact row19_verified
  · exact row20_verified
  · exact row21_verified
  · exact row22_verified
  · exact row23_verified
  · exact row24_verified
  · exact row25_verified
  · exact row26_verified
  · exact row27_verified
  · exact row28_verified
  · exact row29_verified

def cellBreaks : Fin 16 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 48, 64]

def lowRowIndex : Fin 15 → Fin 30 := ![0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27]
def highRowIndex : Fin 15 → Fin 30 := ![2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 29]

def lowCellCorner (i : Fin 15) : CornerRow := cornerRow (lowRowIndex i)
def highCellCorner (i : Fin 15) : CornerRow := cornerRow (highRowIndex i)

theorem lowCellCorner_label (i : Fin 15) :
    (lowCellCorner i).breakpoint = cellBreaks i.castSucc ∧ (lowCellCorner i).upper = false := by
  fin_cases i <;> decide +kernel

theorem highCellCorner_label (i : Fin 15) :
    (highCellCorner i).breakpoint = cellBreaks i.succ ∧ (highCellCorner i).upper = true := by
  fin_cases i <;> decide +kernel

end RKCert.ReviewedNative.WeakFiveSoleInnerUniform

module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Eleven rational stages of exact strict SDIRK order seven

An integer-scaled replay pays the reviewed order conditions. A single tall
condition at order eight fails. This is only an upper construction.
-/

namespace RKResearch.Certified.RationalStrictSDIRKElevenStageSevenUpper

open FiniteRootedTree
open scoped Matrix

/-- The chronological stage numerator matrix 11493557522580 A. -/
def AInt : Matrix (Fin 11) (Fin 11) ℤ :=
  !![1641936788940,0,0,0,0,0,0,0,0,0,0;
     1641936788940,1641936788940,0,0,0,0,0,0,0,0,0;
     -3283873577880,1641936788940,1641936788940,0,0,0,0,0,0,0,0;
     2189249051920,-1094624525960,547312262980,1641936788940,0,0,0,0,0,0,0;
     0,0,-1641936788940,0,1641936788940,0,0,0,0,0,0;
     -547312262980,273656131490,684140328725,-410484197235,0,1641936788940,0,0,0,0,0;
     4925810366820,-2462905183410,-410484197235,1231452591705,0,0,1641936788940,0,0,0,0;
     1786138822300,-893069411150,-398311298315,5174067276525,1095560902800,-1278154386600,1081515250200,1641936788940,0,0,0;
     -15806325962140,7903162981070,-4328534263795,-43999581060855,-406108256400,41366982979560,25122024316200,0,1641936788940,0,0;
     -10070287751440,5035143875720,-1133591617900,-12567451279320,1178276968032,16367617718550,7829012220750,-1919181853302,206272085730,1641936788940,0;
     6694350435360,-3347175217680,1804520027940,19636322590920,763840519896,-13679724868530,-8100406843410,2210991593874,-517093036830,2744058743160,1641936788940]

/-- The output numerator row 17280 b. -/
def bInt : Fin 11 → ℤ := ![0,0,0,1323,751,3577,2989,1323,751,2989,3577]

def A : Matrix (Fin 11) (Fin 11) ℚ := Matrix.of fun i j => (AInt i j : ℚ) / 11493557522580

def b : Fin 11 → ℚ := fun i => (bInt i : ℚ) / 17280

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 11, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1/7 := by
  intro i
  fin_cases i <;> decide +kernel

private theorem cast_AInt :
    AInt.map (Int.castRingHom ℚ) = (11493557522580 : ℚ) • A := by
  funext i j
  change (AInt i j : ℚ) = (11493557522580 : ℚ) * ((AInt i j : ℚ) / 11493557522580)
  exact (mul_div_cancel₀ (AInt i j : ℚ) (by decide +kernel : (11493557522580 : ℚ) ≠ 0)).symm

private theorem cast_bInt :
    (Int.castRingHom ℚ) ∘ bInt = (17280 : ℚ) • b := by
  funext i
  change (bInt i : ℚ) = (17280 : ℚ) * ((bInt i : ℚ) / 17280)
  exact (mul_div_cancel₀ (bInt i : ℚ) (by decide +kernel : (17280 : ℚ) ≠ 0)).symm

-- Same predicate as checkScaledOrder, split only at the outer lists.
private def paidTree (t : FiniteRootedTree) : Bool :=
  decide ((t.factorial : ℤ) * (bInt ⬝ᵥ replayStage (fun v => AInt *ᵥ v) t) =
    17280 * 11493557522580 ^ ((t.order : ℕ) - 1))

private theorem all_true_parts (k : ℕ) (trees : List FiniteRootedTree)
    (head : (trees.take k).all paidTree = true)
    (tail : (trees.drop k).all paidTree = true) : trees.all paidTree = true := by
  calc
    trees.all paidTree = (trees.take k ++ trees.drop k).all paidTree := by
      rw [List.take_append_drop]
    _ = true := by simp only [List.all_append, head, tail, Bool.true_and]

set_option maxHeartbeats 8000000 in
private theorem paidGroup0 : (treesOfOrderSucc 0).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup1 : (treesOfOrderSucc 1).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup2 : (treesOfOrderSucc 2).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup3 : (treesOfOrderSucc 3).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup4 : (treesOfOrderSucc 4).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup5_prefix0 : ((treesOfOrderSucc 5).take 22).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup5_tail1 : ((treesOfOrderSucc 5).drop 22).all paidTree = true := by
  decide +kernel

private theorem paidGroup5 : (treesOfOrderSucc 5).all paidTree = true :=
  all_true_parts 22 (treesOfOrderSucc 5) paidGroup5_prefix0 paidGroup5_tail1

set_option maxHeartbeats 8000000 in
private theorem paidGroup6_prefix0 : ((treesOfOrderSucc 6).take 22).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup6_prefix1 : (((treesOfOrderSucc 6).drop 22).take 22).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup6_prefix2 : ((((treesOfOrderSucc 6).drop 22).drop 22).take 22).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup6_prefix3 : (((((treesOfOrderSucc 6).drop 22).drop 22).drop 22).take 22).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup6_prefix4 : ((((((treesOfOrderSucc 6).drop 22).drop 22).drop 22).drop 22).take 22).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem paidGroup6_tail5 : ((((((treesOfOrderSucc 6).drop 22).drop 22).drop 22).drop 22).drop 22).all paidTree = true := by
  decide +kernel

private theorem paidGroup6_tail4 : (((((treesOfOrderSucc 6).drop 22).drop 22).drop 22).drop 22).all paidTree = true :=
  all_true_parts 22 (((((treesOfOrderSucc 6).drop 22).drop 22).drop 22).drop 22) paidGroup6_prefix4 paidGroup6_tail5

private theorem paidGroup6_tail3 : ((((treesOfOrderSucc 6).drop 22).drop 22).drop 22).all paidTree = true :=
  all_true_parts 22 ((((treesOfOrderSucc 6).drop 22).drop 22).drop 22) paidGroup6_prefix3 paidGroup6_tail4

private theorem paidGroup6_tail2 : (((treesOfOrderSucc 6).drop 22).drop 22).all paidTree = true :=
  all_true_parts 22 (((treesOfOrderSucc 6).drop 22).drop 22) paidGroup6_prefix2 paidGroup6_tail3

private theorem paidGroup6_tail1 : ((treesOfOrderSucc 6).drop 22).all paidTree = true :=
  all_true_parts 22 ((treesOfOrderSucc 6).drop 22) paidGroup6_prefix1 paidGroup6_tail2

private theorem paidGroup6 : (treesOfOrderSucc 6).all paidTree = true :=
  all_true_parts 22 (treesOfOrderSucc 6) paidGroup6_prefix0 paidGroup6_tail1

private theorem paidGroup (n : Fin 7) :
    (treesOfOrderSucc n.val).all paidTree = true := by
  fin_cases n
  · exact paidGroup0
  · exact paidGroup1
  · exact paidGroup2
  · exact paidGroup3
  · exact paidGroup4
  · exact paidGroup5
  · exact paidGroup6

private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 11493557522580 17280 7 = true := by
  change (List.range 7).all (fun n => (treesOfOrderSucc n).all paidTree) = true
  apply List.all_eq_true.mpr
  intro n hn
  exact paidGroup ⟨n, List.mem_range.mp hn⟩

theorem order_seven : HasOrder 7 A b :=
  hasOrder_of_scaled_check (A := AInt) (b := bInt) (d := 11493557522580) (e := 17280) (p := 7)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) cast_AInt cast_bInt
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) checked

private def eighthTallNumerator : ℤ :=
  11821098297671926567289161075055252877059980829324532259831724563599430359045580108800000000

-- Check the seven actual integer tall-stage matvecs separately.

private def tallVec2 : Fin 11 → ℤ := ![1641936788940,3283873577880,0,3283873577880,0,1641936788940,4925810366820,8209683944700,11493557522580,6567747155760,9851620733640]

private theorem tall_step2 : AInt *ᵥ (1 : Fin 11 → ℤ) = tallVec2 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec3 : Fin 11 → ℤ := ![2695956418874598106323600,8087869256623794318970800,0,5391912837749196212647200,0,1347978209437299053161800,12131803884935691478456200,33699455235932476329045000,66050932262427653604928200,21567651350996784850588800,48527215539742765913824800]

private theorem tall_step3 : AInt *ᵥ tallVec2 = tallVec3 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec4 : Fin 11 → ℤ := ![4426590025529139223229976492540984000,17706360102116556892919905970163936000,4426590025529139223229976492540984000,5902120034038852297639968656721312000,0,737765004254856537204996082090164000,19919655114881126504534894216434428000,92220625531857067150624510261270500000,253053396459415792261313656156926252000,47216960272310818381119749253770496000,159357240919049012036279153731475424000]

private theorem tall_step4 : AInt *ᵥ tallVec3 = tallVec4 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec5 : Fin 11 → ℤ := ![7268181012471147480592433457314427130307916960000,36340905062355737402962167286572135651539584800000,21804543037413442441777300371943281390923750880000,2422727004157049160197477819104809043435972320000,-7268181012471147480592433457314427130307916960000,4239772257274836030345586183433415826012951560000,16353407278060081831332975278957461043192813160000,192889171983878391938074941155062456020882768840000,737555523131627339152072520516641048160226464040000,86148127877599383037517991908158968012431965920000,387068433250944645523654642124939718985380801120000]

private theorem tall_step5 : AInt *ᵥ tallVec4 = tallVec5 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec6 : Fin 11 → ℤ := ![11933893793051553988681111159763473038273400126762566422400000,71603362758309323932086666958580838229640400760575398534400000,71603362758309323932086666958580838229640400760575398534400000,-7955929195367702659120740773175648692182266751175044281600000,-47735575172206215954724444639053892153093600507050265689600000,26851261034365996474532500109467814336115150285215774450400000,-32818207930891773468873055689349550855251850348597057661600000,305393854826848161214621565972723898039528086520217164386400000,1771532670230792857556849781163761971988661523599643716485600000,166883625184329725000113095934402719621224714706232459708800000,734945592570790832618931924416657589414995260944868170057600000]

private theorem tall_step6 : AInt *ᵥ tallVec5 = tallVec6 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec7 : Fin 11 → ℤ := ![19594699254114065440052112763293236250364892325952317269388919688256000000,137162894778798458080364789343052653752554246281666220885722437817792000000,195946992541140654400521127632932362503648923259523172693889196882560000000,-26126265672152087253402817017724315000486523101269756359185226251008000000,-195946992541140654400521127632932362503648923259523172693889196882560000000,109403737502136865373624296261720569064537315486567104754088134926096000000,-210643016981726203480560212205402289691422592503987410645930886648752000000,267010602788720714228198005080362031325812731149658911293843665740560000000,3631808288821641458938094987190792814269516515240875165115676186469200000000,438807324022333969584523054202218372986281823062378390382534905856384000000,1099114496626247070282742403218503067752426204996991596839103142338816000000]

private theorem tall_step7 : AInt *ᵥ tallVec6 = tallVec7 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec8 : Fin 11 → ℤ := ![32173257573545061693128194096824486628544937208982995644852551748950602468688640000000,257386060588360493545025552774595893028359497671863965158820413991604819749509120000000,482598863603175925396922911452367299428174058134744934672788276234259037030329600000000,-42897676764726748924170925462432648838059916278643994193136735665267469958251520000000,-643465151470901233862563881936489732570898744179659912897051034979012049373772800000000,351224728511200256816649452223667312361615564531397702456307023259377410283184320000000,-699768352224605091825538221605932584170852384295380155275543000539675603693977920000000,-444629924400863514766060546662452174240295427147097836519057595153286893897371200000000,6352380865788628674629500207444373760367683902552870378525749089642954652098993600000000,1467391978125235846084912273609518141492624162693264381559069921456743509900186880000000,1293805910220810884825536483135946152072961860435678531766601407715920581366122240000000]

private theorem tall_step8 : AInt *ᵥ tallVec7 = tallVec8 := by
  funext i
  fin_cases i <;> decide +kernel

private theorem eighth_tall_int :
    bInt ⬝ᵥ Φ (tallTree 8) AInt = eighthTallNumerator := by
  have h1 : Φ (tallTree 1) AInt = (1 : Fin 11 → ℤ) := rfl
  have h2 : Φ (tallTree 2) AInt = tallVec2 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 1) AInt) = tallVec2
    simpa only [one_mul, h1] using tall_step2
  have h3 : Φ (tallTree 3) AInt = tallVec3 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 2) AInt) = tallVec3
    simpa only [one_mul, h2] using tall_step3
  have h4 : Φ (tallTree 4) AInt = tallVec4 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 3) AInt) = tallVec4
    simpa only [one_mul, h3] using tall_step4
  have h5 : Φ (tallTree 5) AInt = tallVec5 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 4) AInt) = tallVec5
    simpa only [one_mul, h4] using tall_step5
  have h6 : Φ (tallTree 6) AInt = tallVec6 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 5) AInt) = tallVec6
    simpa only [one_mul, h5] using tall_step6
  have h7 : Φ (tallTree 7) AInt = tallVec7 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 6) AInt) = tallVec7
    simpa only [one_mul, h6] using tall_step7
  have h8 : Φ (tallTree 8) AInt = tallVec8 := by
    change (1 : Fin 11 → ℤ) * (AInt *ᵥ Φ (tallTree 7) AInt) = tallVec8
    simpa only [one_mul, h7] using tall_step8
  rw [h8] <;> decide +kernel

/-- Only this next-order tall tree is used to make the witness exact. -/
theorem eighth_tall_weight : b ⬝ᵥ Φ (tallTree 8) A = (18371 / 711541152 : ℚ) := by
  have h := congrArg (Int.castRingHom ℚ) eighth_tall_int
  simp only [RingHom.map_dotProduct, RKResearch.map_Φ, cast_AInt, cast_bInt,
    Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, order_tallTree] at h
  have scaled :
      (11493557522580 : ℚ) ^ (7 : ℕ) * ((17280 : ℚ) * (b ⬝ᵥ Φ (tallTree 8) A)) =
        (eighthTallNumerator : ℚ) := by
    first
    | exact h
    | simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have expected :
      (11493557522580 : ℚ) ^ (7 : ℕ) * ((17280 : ℚ) * (18371 / 711541152 : ℚ)) =
        (eighthTallNumerator : ℚ) := by
    decide +kernel
  have unscale := mul_left_cancel₀ (by decide +kernel : (11493557522580 : ℚ) ^ (7 : ℕ) ≠ 0)
    (scaled.trans expected.symm)
  exact mul_left_cancel₀ (by decide +kernel : (17280 : ℚ) ≠ 0) unscale

theorem not_order_eight : ¬ HasOrder 8 A b := by
  intro h
  have paid := h (tallTree 8) (by rw [order_tallTree] <;> decide)
  rw [eighth_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 8).factorial : ℚ) * (18371 / 711541152 : ℚ) ≠ 1) paid

end RKResearch.Certified.RationalStrictSDIRKElevenStageSevenUpper

namespace RKResearch.Certified

/-- Eleven rational stages suffice for exact order seven at fixed diagonal one seventh. -/
theorem exists_eleven_stage_rational_strictSDIRK_exact_seven :
    ∃ (A : Matrix (Fin 11) (Fin 11) ℚ) (b : Fin 11 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/7) ∧ (1/7 : ℚ) ≠ 0 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b :=
  ⟨RationalStrictSDIRKElevenStageSevenUpper.A, RationalStrictSDIRKElevenStageSevenUpper.b,
    RationalStrictSDIRKElevenStageSevenUpper.lowerTriangular,
    RationalStrictSDIRKElevenStageSevenUpper.common_diagonal, by decide +kernel,
    RationalStrictSDIRKElevenStageSevenUpper.order_seven,
    RationalStrictSDIRKElevenStageSevenUpper.not_order_eight⟩

end RKResearch.Certified

module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Ten strict SDIRK stages of exact order seven

All rooted conditions are replayed on integer numerators. The diagonal
is the inverse of five. The eighth bush and eighth tall discrepancies
cannot vanish simultaneously even after a coefficient specialization
in which the denominators remain units.
-/

namespace RKResearch.Certified.SDIRKTenStageOrderSevenRing
open FiniteRootedTree
open scoped Matrix

/-- The literal numerator matrix $13255661380500 A$. -/
def AInt : Matrix (Fin 10) (Fin 10) ℤ :=
  !![2651132276100,0,0,0,0,0,0,0,0,0;
     2651132276100,2651132276100,0,0,0,0,0,0,0,0;
     -5302264552200,2651132276100,2651132276100,0,0,0,0,0,0,0;
     3534843034800,-1767421517400,883710758700,2651132276100,0,0,0,0,0,0;
     -80417679041700,40208839520850,32918225761575,23197407415875,2651132276100,0,0,0,0,0;
     -117774001940000,58887000970000,47823439983900,11777400194000,-3364971484000,2651132276100,0,0,0,0;
     46609047742950,-23304523871475,-19402211515203,-5412058919190,1356935957190,152810605728,2651132276100,0,0,0;
     -2830700841588900,1415350420794450,1277219617546608,378157361795010,-86078435939460,-18740376526608,-143161142909400,2651132276100,0,0;
     -263805149300,131902574650,16573658890272,41764206386210,-302795667460,8671562764128,-52077797541000,-1241270877000,2651132276100,0;
     -5116415812200,2558207906100,-173741791212,3103673958000,0,1759960787112,6056067041640,31594285800,-265949546940,2651132276100]

/-- The literal numerator output $508032 b$. -/
def bInt : Fin 10 → ℤ := ![0,0,0,163296,-1376,43362,93408,-385,10017,199710]

private theorem numerator_triangular : AInt.IsLowerTriangular := by
  change ∀ i j : Fin 10, i < j → AInt i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem numerator_diagonal (i : Fin 10) : AInt i i = 2651132276100 :=
  (by decide +kernel : ∀ i : Fin 10, AInt i i = 2651132276100) i

private def paidTree (t : FiniteRootedTree) : Bool :=
  decide ((t.factorial : ℤ) * (bInt ⬝ᵥ replayStage (fun v => AInt *ᵥ v) t) =
    508032 * 13255661380500 ^ ((t.order : ℕ) - 1))

private theorem all_true_parts (k : ℕ) (trees : List FiniteRootedTree)
    (head : (trees.take k).all paidTree = true)
    (tail : (trees.drop k).all paidTree = true) : trees.all paidTree = true := by
  calc
    trees.all paidTree = (trees.take k ++ trees.drop k).all paidTree := by
      rw [List.take_append_drop]
    _ = true := by simp only [List.all_append, head, tail, Bool.true_and]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup0 : (treesOfOrderSucc 0).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup1 : (treesOfOrderSucc 1).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup2 : (treesOfOrderSucc 2).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup3 : (treesOfOrderSucc 3).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup4 : (treesOfOrderSucc 4).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup5_part0 : ((treesOfOrderSucc 5).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup5_part1 : (((treesOfOrderSucc 5).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup5_part2 : (((treesOfOrderSucc 5).drop 14).drop 14).all paidTree = true := by
  decide +kernel

private theorem paidGroup5 : (treesOfOrderSucc 5).all paidTree = true :=
  (all_true_parts 14 _ paidGroup5_part0 (all_true_parts 14 _ paidGroup5_part1 paidGroup5_part2))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part0 : ((treesOfOrderSucc 6).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part1 : (((treesOfOrderSucc 6).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part2 : ((((treesOfOrderSucc 6).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part3 : (((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part4 : ((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part5 : (((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part6 : ((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part7 : (((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part8 : ((((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part9 : ((((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).all paidTree = true := by
  decide +kernel

private theorem paidGroup6 : (treesOfOrderSucc 6).all paidTree = true :=
  (all_true_parts 14 _ paidGroup6_part0 (all_true_parts 14 _ paidGroup6_part1 (all_true_parts 14 _ paidGroup6_part2 (all_true_parts 14 _ paidGroup6_part3 (all_true_parts 14 _ paidGroup6_part4 (all_true_parts 14 _ paidGroup6_part5 (all_true_parts 14 _ paidGroup6_part6 (all_true_parts 14 _ paidGroup6_part7 (all_true_parts 14 _ paidGroup6_part8 paidGroup6_part9)))))))))

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
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 13255661380500 508032 7 = true := by
  change (List.range 7).all (fun n => (treesOfOrderSucc n).all paidTree) = true
  apply List.all_eq_true.mpr
  intro n hn
  exact paidGroup ⟨n, List.mem_range.mp hn⟩

private theorem numerator_bush_eight :
    109375 * (((bushyTree 8).factorial : ℤ) * (bInt ⬝ᵥ Φ (bushyTree 8) AInt)) =
      109436 * (508032 * (13255661380500 : ℤ)^7) := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

private def tallVec2 : Fin 10 → ℤ := ![2651132276100,5302264552200,0,5302264552200,18557925932700,0,2651132276100,-5302264552200,15906793656600,10604529104400]
private theorem tall_step2 : AInt *ᵥ (1 : Fin 10 → ℤ) = tallVec2 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec3 : Fin 10 → ℤ := ![7028502345379166631210000,21085507036137499893630000,0,14057004690758333262420000,172198307461789582464645000,0,3514251172689583315605000,14057004690758333262420000,126513042216824999361780000,56228018763033333049680000]
private theorem tall_step3 : AInt *ᵥ tallVec2 = tallVec3 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec4 : Fin 10 → ℤ := ![18633489420479258348520936597081000000,74533957681917033394083746388324000000,18633489420479258348520936597081000000,24844652560639011131361248796108000000,1065214478537397602257113542133130500000,0,3105581570079876391420156099513500000,-24844652560639011131361248796108000000,670805619137253300546753717494916000000,198757220485112089050889990368864000000]
private theorem tall_step4 : AInt *ᵥ tallVec3 = tallVec4 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec5 : Fin 10 → ℤ := ![49399845219000446138354237709123140146064100000000,246999226095002230691771188545615700730320500000000,148199535657001338415062713127369420438192300000000,16466615073000148712784745903041046715354700000000,5512199395686799781604693691042990387964985825000000,-206152746587321421028958950774497046741574100000000,89180311078999947130304509381320521302596732000000,-6262380637312999197139854264362206418376202002000000,2676317099471526121058641919433345586478496582000000,535762858206699750883468269203755817495569128000000]
private theorem tall_step5 : AInt *ᵥ tallVec4 = tallVec5 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec6 : Fin 10 → ℤ := ![130965524094436355737690525725868080270614203889498010000000000,785793144566618134426143154355208481623685223336988060000000000,785793144566618134426143154355208481623685223336988060000000000,-87310349396290903825127017150578720180409469259665340000000000,25832949627627571169259456199427478833378651717203482472500000000,-3086560266215311564966211001872223808471426723656576540000000000,1266391393517276873745936995578932159307778192098233219750000000,-94723076046206385273567104196572228848860545566988823834300000000,9931002150420128949268956628918377594713607235302021580500000000,1092502409945836831423516334991552790222187349335611993800000000]
private theorem tall_step6 : AInt *ᵥ tallVec5 = tallVec6 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec7 : Fin 10 → ℤ := ![347206927983112447133452778025026248296170938302554332137720561000000000000,2430448495881787129934169446175183738073196568117880324964043927000000000000,3472069279831124471334527780250262482961709383025543321377205610000000000000,-462942570644149929511270370700034997728227917736739109516960748000000000000,113391995897151473359666786423339822256057825600642535637310573213250000000000,-27710308247900253777395989949898559502065898341969291311238281810000000000000,10957417410352114701187588947385356396012062198291353518935981243550000000000,-886176234816702935073517677645130331845425318149085775172395931604330000000000,52813233956840540584297756545848210162855290686305444903251567447350000000000,432281276716077250604685316502719540373091411056530704949325069760000000000]
private theorem tall_step7 : AInt *ᵥ tallVec6 = tallVec7 := by
  funext i
  fin_cases i <;> decide +kernel

private def tallVec8 : Fin 10 → ℤ := ![920491493261557684331151583857355900407671406576723537004190489549698892100000000000000,7363931946092461474649212670858847203261371252613788296033523916397591136800000000000000,13807372398923365264967273757860338506115071098650853055062857343245483381500000000000000,-1227321991015410245774868778476474533876895208768964716005587319399598522800000000000000,473976411405263744290182136387883509051583468436464561262407752910632454523825000000000000,-192200614857155387639340045078722898633536098705955251175692859009159503287000000000000000,73362999659584786437299687757212030109481456306012270145742585611803736055157500000000000,-6442723648261066571642636784218362181534996798200879230771980041329042921533598000000000000,433174623840495892270074371091982705615055979538227017671478136338268009056760000000000000,-20906856300286379586041393609463086383346450273410153809605853737868893534505000000000000]
private theorem tall_step8 : AInt *ᵥ tallVec7 = tallVec8 := by
  funext i
  fin_cases i <;> decide +kernel

private theorem numerator_tall_eight :
    11207109375 * (((tallTree 8).factorial : ℤ) * (bInt ⬝ᵥ Φ (tallTree 8) AInt)) =
      3835812466 * (508032 * (13255661380500 : ℤ)^7) := by
  have h2 : Φ (tallTree 2) AInt = tallVec2 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ (1 : Fin 10 → ℤ)) = tallVec2
    simpa only [one_mul] using tall_step2
  have h3 : Φ (tallTree 3) AInt = tallVec3 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ Φ (tallTree 2) AInt) = tallVec3
    simpa only [one_mul, h2] using tall_step3
  have h4 : Φ (tallTree 4) AInt = tallVec4 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ Φ (tallTree 3) AInt) = tallVec4
    simpa only [one_mul, h3] using tall_step4
  have h5 : Φ (tallTree 5) AInt = tallVec5 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ Φ (tallTree 4) AInt) = tallVec5
    simpa only [one_mul, h4] using tall_step5
  have h6 : Φ (tallTree 6) AInt = tallVec6 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ Φ (tallTree 5) AInt) = tallVec6
    simpa only [one_mul, h5] using tall_step6
  have h7 : Φ (tallTree 7) AInt = tallVec7 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ Φ (tallTree 6) AInt) = tallVec7
    simpa only [one_mul, h6] using tall_step7
  have h8 : Φ (tallTree 8) AInt = tallVec8 := by
    change (1 : Fin 10 → ℤ) * (AInt *ᵥ Φ (tallTree 7) AInt) = tallVec8
    simpa only [one_mul, h7] using tall_step8
  rw [h8]
  decide +kernel

variable {R : Type*} [CommRing R]

private theorem unitOfNatDvd {d m : ℕ} (h : d ∣ m) (hm : IsUnit (m : R)) :
    IsUnit (d : R) := by
  obtain ⟨e,he⟩ := h
  apply isUnit_of_dvd_unit _ hm
  exact ⟨(e : R), by simpa only [Nat.cast_mul] using congrArg ((↑) : ℕ → R) he⟩

/-- The new rational tableau specializes whenever its stage denominator
is a unit. The weight denominator divides a power of the stage denominator. -/
theorem exists_exact_of_stageDen_unit [Nontrivial R] (h : IsUnit (13255661380500 : R)) :
    ∃ (A : Matrix (Fin 10) (Fin 10) R) (b : Fin 10 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ (5 : R) * γ = 1 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  have hpow : IsUnit (((13255661380500 : ℕ)^4 : ℕ) : R) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h.pow 4
  have he : IsUnit (508032 : R) := by
    simpa only [Nat.cast_ofNat] using unitOfNatDvd (R := R) (d := 508032) (by decide) hpow
  obtain ⟨d,hd'⟩ := h
  obtain ⟨e,he'⟩ := he
  let f := Int.castRingHom R
  let A : Matrix (Fin 10) (Fin 10) R := Matrix.of fun i j => (↑d⁻¹ : R) * f (AInt i j)
  let b : Fin 10 → R := fun i => (↑e⁻¹ : R) * f (bInt i)
  let γ : R := (↑d⁻¹ : R) * 2651132276100
  have hAu : AInt.map f = f 13255661380500 • A := by
    ext i j
    simp only [map_ofNat]
    change f (AInt i j) = (13255661380500 : R) * ((↑d⁻¹ : R) * f (AInt i j))
    rw [←hd', ←mul_assoc]; simp
  have hbu : f ∘ bInt = f 508032 • b := by
    funext i
    simp only [map_ofNat]
    change f (bInt i) = (508032 : R) * ((↑e⁻¹ : R) * f (bInt i))
    rw [←he', ←mul_assoc]; simp
  have hd : IsUnit (f 13255661380500) := by rw [map_ofNat, ←hd']; exact d.isUnit
  have he : IsUnit (f 508032) := by rw [map_ofNat, ←he']; exact e.isUnit
  have h5 : (5 : R) * γ = 1 := by
    have hdi : (13255661380500 : R) * (↑d⁻¹ : R) = 1 := by rw [←hd']; simp
    change (5 : R) * ((↑d⁻¹ : R) * 2651132276100) = 1
    linear_combination (norm := ring) hdi
  refine ⟨A,b,γ,?_,?_,IsUnit.of_mul_eq_one (5:R) ((mul_comm _ _).trans h5),h5,?_,?_⟩
  · intro i j hij
    change (↑d⁻¹:R) * f (AInt i j) = 0
    rw [numerator_triangular hij, map_zero, mul_zero]
  · intro i
    change (↑d⁻¹:R) * f (AInt i i) = γ
    rw [numerator_diagonal, map_ofNat]
  · exact hasOrder_of_scaled_check f (fun _ => rfl) (fun _ => rfl)
      hAu hbu hd he checked
  · intro h8
    let Ω : R := (508032 : R) * (13255661380500 : R)^7
    have hΩ : IsUnit Ω := by
      simpa only [Ω, map_ofNat] using he.mul (hd.pow 7)
    have hPaid (t : FiniteRootedTree) (ht : (t.order : ℕ) = 8) :
        f ((t.factorial : ℤ) * (bInt ⬝ᵥ Φ t AInt)) = Ω := by
      have hp : (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1 := h8 t (by rw [ht])
      simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ,
        hAu, hbu, Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ht, map_ofNat]
      change (t.factorial : R) * ((13255661380500 : R)^7 *
        ((508032 : R) * (b ⬝ᵥ Φ t A))) = Ω
      linear_combination (norm := ring) Ω * hp
    have hB := congrArg f numerator_bush_eight
    have hT := congrArg f numerator_tall_eight
    rw [map_mul, hPaid _ (by simp [order_bushyTree])] at hB
    rw [map_mul, hPaid _ (by simp [order_tallTree])] at hT
    simp only [map_mul, map_pow, map_ofNat] at hB hT
    change (109375 : R) * Ω = 109436 * Ω at hB
    change (11207109375 : R) * Ω = 3835812466 * Ω at hT
    exact hΩ.ne_zero (by linear_combination (norm := ring) 1812613994*hB + 15*hT)

/-- A convenient sufficient unit premise: the paid factorial and the
four explicitly identified extra prime factors. -/
theorem exists_exact_of_paid_and_extra [Nontrivial R]
    (h : IsUnit (5040 : R)) (he : IsUnit ((11 * 23 * 53 * 317) : R)) :
    ∃ (A : Matrix (Fin 10) (Fin 10) R) (b : Fin 10 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ (5 : R) * γ = 1 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  have hu : IsUnit ((((5040 * 11 * 23 * 53 * 317)^3 : ℕ)) : R) := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (5040 : R)*11*23*53*317 = 5040*(11*23*53*317) by ring]
    exact (h.mul he).pow 3
  exact exists_exact_of_stageDen_unit (unitOfNatDvd (d := 13255661380500) (by decide) hu)

/-- Ten rational stages at diagonal one fifth, improving the previously
certified eleven-stage rational upper endpoint. -/
theorem exists_exact_rational :
    ∃ (A : Matrix (Fin 10) (Fin 10) ℚ) (b : Fin 10 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/5) ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  obtain ⟨A,b,γ,ha,hdiag,_,h5,ho,he⟩ :=
    exists_exact_of_stageDen_unit (R := ℚ) (isUnit_iff_ne_zero.mpr (by decide +kernel))
  have hγ : γ = (1/5 : ℚ) := mul_left_cancel₀ (by decide : (5:ℚ) ≠ 0)
    (h5.trans (by decide +kernel))
  exact ⟨A,b,ha,fun i => (hdiag i).trans hγ,ho,he⟩

end RKResearch.Certified.SDIRKTenStageOrderSevenRing


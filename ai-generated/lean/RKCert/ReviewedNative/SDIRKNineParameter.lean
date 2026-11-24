module

public import RKCert.ReviewedNative.PolynomialBracket
public import Mathlib.FieldTheory.AlgebraicClosure

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Real parameters of the archived exact strict SDIRK(9,7) construction

The polynomial and the reduced auxiliary coordinates are exact rational
data. This module proves the required real and algebraic parameter
existence. It does not assert a Lean order theorem for the tableau. -/

namespace RKResearch.Certified.SDIRKNineParameter

open Polynomial
open RKCert.ReviewedNative.PolynomialBracket

noncomputable section

/-- The negative of the archived monic polynomial in `t = 4 z`.
This sign places the two rational bracket values in ascending order. -/
def pCoeffs : List ℚ := [
  -4110417920000, 6165626880000, -3982884864000,
  1463418880000, -339942604800, 52502937600,
  -5527904000, 400934400, -19990080,
  671520, -14460, 180,
  -1]

def rhoCoeffs : List ℚ := [
  852455271544/41305249, -8726570025867/330441992, 1967457925361771/138785636640,
  -3125212545966201/740190062080, 2296935743042977/2960760248320, -313059311993419/3383725998080,
  31080824036959/4229657497600, -1061323652531/2706980798464, 616092337363/44411403724800,
  -2356843919433/7579546235699200, 151311550613/37897731178496000, -10347454441/454772774141952000]

def uCoeffs : List ℚ := [
  3178910469515/289136743, -4632290995215/330441992, 9714460308543897/1295332608640,
  -4615399895413473/2072532173824, 236861175084565401/580309008670720, -225534047513181159/4642472069365760,
  22357132725757061/5803090086707200, -19063338831020277/92849441387315200, 673882407516777/92849441387315200,
  -241502802171499/1485591062197043200, 15495810329451/7427955310985216000, -353059051857/29711821243940864000]

def vCoeffs : List ℚ := [
  429090181490/289136743, -312618752385/165220996, 131107398198879/129533260864,
  -1557067606260599/5181330434560, 7989798585790407/145077252167680, -7606724975550207/1160618017341440,
  75396443174103/145077252167680, -642820350382347/23212360346828800, 11360726062257/11606180173414400,
  -8142173816307/371397765549260800, 104480136819/371397765549260800, -11901752673/7427955310985216000]

def discCoeffs : List ℚ := [
  -941719717004069/99173902849, 171915687017484/14167700407, -2890667975096648379/444299084763520,
  430064775836801817/222149542381760, -70750776304144000317/199045989974056960, 33731881571161940199/796183959896227840,
  -13390472702437731409/3980919799481139200, 2856981641896498083/15923679197924556800, -404263610209778619/63694716791698227200,
  36240415714175431/254778867166792908800, -145399931098071/79618395989622784000, 53025512467161/5095577343335858176000]

def discQuot : List ℚ := [
  -247591348984627564884509243/8418963638609844503534632960000, 2079872577752072007960126747/67351709108878756028277063680000, -28260412632314072040387458283/2155254691484120192904866037760000,
  25916337053705190659091720157/8621018765936480771619464151040000, -286395926473537325500349755971/689681501274918461729557132083200000, 71900344597126510717793943/1970518575071195604941591805952000,
  -5773370773947953582067171569/2758726005099673846918228528332800000, 61592822815215475152054849/788207430028478241976636722380800000, -402649420688451053254293279/220698080407973907753458282266624000000,
  5332590970926382045000809/220698080407973907753458282266624000000, -124650694098163815148449/882792321631895631013833129066496000000]

def rhoQuot : List ℚ := [
  -363339993285453793119967/3506440499212763225128960000, 769732675405684767897261/7012880998425526450257920000, -1976843734941719188318691/42077285990553158701547520000,
  2432685490282862591713431/224412191949616846408253440000, -34730046592671125889583093/23082396886246304201991782400000, 510398408975026498947673/3847066147707717366998630400000,
  -547871545837968953370877/71811901423877390850641100800000, 368967281221798656128483/1292614225629793035311539814400000, -115036770550117105197973/17234856341730573804153864192000000,
  1525331551601606907451/17234856341730573804153864192000000, -107069813408570622481/206818276100766885649846370304000000]

def bushCoeffs : List ℚ := [
  -8480/49, 220, -482557/4116,
  380349/10976, -19421383/3073280, 18400969/24586240,
  -36321/614656, 617091/196689920, -163097/1475174400,
  19437/7867596800, -249/7867596800, 17/94411161600]

def lo : ℚ := 59483987/4000000
def hi : ℚ := 14870997/1000000

def value (cs : List ℚ) (x : ℝ) : ℝ := horner (cs.map (Rat.castHom ℝ)) x

def rho : ℝ → ℝ := value rhoCoeffs
def U : ℝ → ℝ := value uCoeffs
def V : ℝ → ℝ := value vCoeffs

/-- Both rational endpoint signs and the positive-root interval are exact. -/
theorem exists_root : ∃ x ∈ Set.Ioo (lo:ℝ) (hi:ℝ), value pCoeffs x = 0 := by
  have ha : horner pCoeffs lo < 0 := by decide +kernel
  have hb : 0 < horner pCoeffs hi := by decide +kernel
  have ha' : value pCoeffs (lo:ℝ) < 0 := by
    change horner (pCoeffs.map (Rat.castHom ℝ)) ((Rat.castHom ℝ) lo) < 0
    rw [← map_horner]
    change ((↑(horner pCoeffs lo:ℚ)):ℝ) < 0
    exact_mod_cast ha
  have hb' : 0 < value pCoeffs (hi:ℝ) := by
    change 0 < horner (pCoeffs.map (Rat.castHom ℝ)) ((Rat.castHom ℝ) hi)
    rw [← map_horner]
    change 0 < ((↑(horner pCoeffs hi:ℚ)):ℝ)
    exact_mod_cast hb
  exact exists_real_horner_root (B:=15)
    (by norm_num [lo,hi]) (by norm_num [lo]) (by norm_num [hi]) _ ha' hb'

theorem root_is_algebraic {x : ℝ} (hx : value pCoeffs x = 0) : IsAlgebraic ℚ x := by
  refine ⟨ofCoeffs pCoeffs, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : ℚ[X] => p.coeff 12) h
    rw [coeff_ofCoeffs] at hc
    norm_num [pCoeffs] at hc
  · rw [aeval_def, eval₂_ofCoeffs]
    exact hx

set_option maxHeartbeats 4000000 in
private theorem disc_factor (x : ℝ) :
    U x ^ 2 - 4 * V x - value discCoeffs x =
      value pCoeffs x * value discQuot x := by
  norm_num [U,V,value,horner,uCoeffs,vCoeffs,discCoeffs,pCoeffs,discQuot]
  ring

set_option maxHeartbeats 4000000 in
private theorem rho_factor (x : ℝ) :
    rho x ^ 2 - 2 = value pCoeffs x * value rhoQuot x := by
  norm_num [rho,value,horner,rhoCoeffs,pCoeffs,rhoQuot]
  ring

theorem rho_squared {x : ℝ} (hx : value pCoeffs x = 0) : rho x ^ 2 = 2 := by
  have h := rho_factor x
  rwa [hx,zero_mul,sub_eq_zero] at h

theorem rho_positive {x : ℝ} (hx : x ∈ Set.Ioo (lo:ℝ) (hi:ℝ)) : 0 < rho x :=
  horner_pos_of_box (by norm_num [lo]) hx.1.le hx.2.le rhoCoeffs (by decide +kernel)

theorem discriminant_positive {x : ℝ} (hx : x ∈ Set.Ioo (lo:ℝ) (hi:ℝ))
    (hp : value pCoeffs x = 0) : 0 < U x^2 - 4*V x := by
  have hh := disc_factor x
  rw [hp,zero_mul,sub_eq_zero] at hh
  rw [hh]
  exact horner_pos_of_box (by norm_num [lo]) hx.1.le hx.2.le discCoeffs (by decide +kernel)

/-- The rational normal-form polynomial for the eighth-bush discrepancy is
positive on the selected bracket. The statement only concerns the scalar
polynomial, not its yet-unformalized identification with a tableau's weight. -/
theorem reduced_bush_positive {x : ℝ} (hx : x ∈ Set.Ioo (lo:ℝ) (hi:ℝ)) :
    0 < value bushCoeffs x :=
  horner_pos_of_box (by norm_num [lo]) hx.1.le hx.2.le bushCoeffs (by decide +kernel)

private theorem positive_sqrt {d : ℝ} (hd : 0 < d) : ∃ r : ℝ, 0 < r ∧ r^2 = d := by
  have hlo : (0 : ℝ) < d+1 := by linarith only [hd]
  have he0 : horner [-d, 0, 1] (0:ℝ) < 0 := by simpa [horner]
  have he1 : 0 < horner [-d, 0, 1] (d+1) := by
    simp only [horner,mul_zero,add_zero,zero_add,mul_one]
    nlinarith only [hd,sq_nonneg d]
  obtain ⟨y,hy,he⟩ := exists_real_horner_root (B:=d+1) hlo (by linarith only [hd])
      le_rfl [-d,0,1] he0 he1
  refine ⟨y,hy.1,?_⟩
  simp only [horner,mul_zero,add_zero,zero_add,mul_one] at he
  nlinarith only [he]

/-- The physical normalization uses `z=x/4`. The two distinct real roots
of the node quadratic are given in the same order as the archived replay. -/
theorem exists_real_parameters :
    ∃ x v w : ℝ, x ∈ Set.Ioo (lo:ℝ) (hi:ℝ) ∧ 0 < x ∧ value pCoeffs x = 0 ∧
      IsAlgebraic ℚ x ∧ 0 < rho x ∧ rho x ^ 2 = 2 ∧
      v < w ∧ v+w = U x ∧ v*w = V x := by
  obtain ⟨x,hx,hp⟩ := exists_root
  obtain ⟨d,hd,hds⟩ := positive_sqrt (discriminant_positive hx hp)
  refine ⟨x,(U x - d)/2,(U x+d)/2,hx,?_,hp,root_is_algebraic hp,rho_positive hx,rho_squared hp,?_,?_,?_⟩
  · exact (show (0:ℝ) < (lo:ℝ) by norm_num [lo]).trans hx.1
  · linarith only [hd]
  · ring
  · nlinarith only [hds]

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

private theorem horner_mem {x : ℝ} (hx : x ∈ algebraicClosure ℚ ℝ) (cs : List ℚ) :
    value cs x ∈ algebraicClosure ℚ ℝ := by
  let E := algebraicClosure ℚ ℝ
  induction cs with
  | nil => exact E.zero_mem
  | cons c cs ih =>
    exact E.add_mem (E.algebraMap_mem c) (E.mul_mem hx ih)

private theorem algebraic_quadratic_root {x y : ℝ} (hx : IsAlgebraic ℚ x)
    (hy : y^2 - U x*y + V x = 0) : IsAlgebraic ℚ y := by
  have hx' := (mem_algebraicClosure_iff (F:=ℚ) (E:=ℝ)).2 hx
  let a : ℝₐ := ⟨U x,horner_mem hx' uCoeffs⟩
  let b : ℝₐ := ⟨V x,horner_mem hx' vCoeffs⟩
  let p : ℝₐ[X] := X^2 - C a * X + C b
  have hne : p ≠ 0 := by
    intro hn
    have h := congrArg (fun q : ℝₐ[X] => q.coeff 2) hn
    norm_num [p,coeff_sub,coeff_C_mul,coeff_X,coeff_X_pow,coeff_C] at h
  have zero : aeval y p = 0 := by
    simp only [p,map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C]
    exact hy
  have hm : y ∈ algebraicClosure ℝₐ ℝ :=
    mem_algebraicClosure_iff.2 ⟨p,hne,zero⟩
  exact mem_algebraicClosure_iff.1
    (mem_algebraicClosure_iff'.2 (isIntegral_trans y (mem_algebraicClosure_iff'.1 hm)))

/-- The two selected auxiliary nodes are genuine real algebraic numbers, not numerical fits. -/
theorem exists_algebraic_parameters :
    ∃ x v w : ℝ, x ∈ Set.Ioo (lo:ℝ) (hi:ℝ) ∧ 0 < x ∧ value pCoeffs x = 0 ∧
      IsAlgebraic ℚ x ∧ IsAlgebraic ℚ v ∧ IsAlgebraic ℚ w ∧
      0 < rho x ∧ rho x ^ 2 = 2 ∧ v < w ∧ v+w = U x ∧ v*w = V x := by
  obtain ⟨x,v,w,hI,hxp,hp,halg,hr,hrs,hlt,hs,hm⟩ := exists_real_parameters
  refine ⟨x,v,w,hI,hxp,hp,halg,?_,?_,hr,hrs,hlt,hs,hm⟩
  · apply algebraic_quadratic_root halg
    rw [←hs,←hm]
    ring
  · apply algebraic_quadratic_root halg
    rw [←hs,←hm]
    ring

end

end RKResearch.Certified.SDIRKNineParameter

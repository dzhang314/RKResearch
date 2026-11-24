module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveAdmission
public import RKCert.ReviewedNative.ERKOrder16EightSites
public import RKCert.ReviewedNative.NativeFlatClockHead
public import RKCert.ReviewedNative.PhysicalRestrictionDual
public import RKCert.ReviewedNative.QuadraticSeedCensus

@[expose] public section

/-! # Exact original width-24 weak-five site census

Small numerical seed support would pay at least sixteen physical
seed rows by signed cancellation. These rows then pay the entire
terminal-deleted E7 complement, so the cheaper native reverse window
gives a contradiction. No scalar gate other than the existing
ordered quartic physical 3+2 lemma is consumed. -/
namespace RKResearch.Certified.ERK16
open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
variable {Q P : K[X]} {U : Submodule K (Fin 24→K)}

/-- Every original grade-seven tree column restricts to an ordinary
degree-seven polynomial on the actual nonzero quadratic seed rows. -/
theorem weak_seven_tree_restriction (ho : HasOrder 16 A b)
    (dt : quadraticSeed A b (Fin.last 23)=0)
    (strip : zeroSpace A 7=chain (diag (nodes A)) U w 4)
    (core : U≤width24WeakFiveCarrier A b) (qd : Q.natDegree≤4)
    (qFit : ∀ i,quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    {v : Fin 24→K} (hv : v∈treeSpace A 7) :
    ∃ F : K[X], F.natDegree≤7 ∧ ∀ i,quadraticSeed A b i≠0 → v i=F.eval (nodes A i) := by
  rw [treeSpace_coeff_sup ho (by decide)] at hv
  obtain ⟨_,⟨a,rfl⟩,x,hx,rfl⟩ := Submodule.mem_sup.mp hv
  let B := ofFn 8 a
  have db : B.natDegree≤7 := by
    change (ofFn 8 a).natDegree≤7
    exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide : 0<8) a)
  have be : evalNodes A B=coeffEval A 7 a := by
    rw [evalNodes_eq_coeffEval A B db]
    congr 1
    exact toFn_comp_ofFn_eq_id _ _
  obtain ⟨u,hu,R,rd,rep⟩ := HeadFiber.exists_poly (strip.le hx)
  have dR : R.natDegree≤3 := by
    by_cases z : R=0
    · simp [z]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr rd)
  let q := Q.comp (1-X)
  have affine : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  have dq : q.natDegree≤4 := natDegree_comp_le.trans
    (by simpa only [mul_one] using Nat.mul_le_mul qd affine)
  refine ⟨B+R*q,natDegree_add_le_of_degree_le db (natDegree_mul_le_of_le dR dq),?_⟩
  intro i hi
  have u0 := Hidden.carrier_zero_on_active dt (core hu) hi
  have eq := qFit i
  rw [mul_comm (Q.eval (reflectedClock A i))] at eq
  have wi := mul_left_cancel₀ hi eq
  rw [←be,rep,Pi.add_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply,u0,zero_add,wi,
    eval_add,eval_mul]
  simp [q,eval_comp,reflectedClock]

/-- Sixteen actual seed rows force the stronger native E7 support
cover on the weaker F7=7 branch. -/
theorem weak_seven_support_switch (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (C : Width24QuadraticCover A b) (seven : finrank K (zeroSpace A 7)=7)
    (strip : zeroSpace A 7=chain (diag (nodes A)) U w 4)
    (core : U≤width24WeakFiveCarrier A b) (qd : Q.natDegree≤4)
    (qFit : ∀ i,quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (rows : 16≤(Hidden.activeRows (quadraticSeed A b)).card) :
    SupportsComplement A b 7 (Fin.last 23) := by
  let d := quadraticSeed A b
  let T := Hidden.activeRows d
  let R := restrictStageColumns (K:=K) T
  let E := treeSpace A 7
  let L := R.comp (coeffEval A 7)
  have out : Fin.last 23∉T := fun e => (Hidden.mem_activeRows _).mp e C.lastSeed
  have restrict : E.map R≤L.range := by
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨F,deg,fit⟩ := weak_seven_tree_restriction ho C.lastSeed strip core qd qFit hv
    refine ⟨fun j : Fin 8 => F.coeff j.val,?_⟩
    rw [show L=R.comp (coeffEval A 7) from rfl,LinearMap.comp_apply,←evalNodes_eq_coeffEval A F deg]
    ext i
    rw [show R=restrictStageColumns T from rfl,restrictStageColumns_apply,restrictStageColumns_apply,
      evalNodes_apply]
    exact (fit _ ((Hidden.mem_activeRows _).mp i.property)).symm
  have r8 : finrank K (E.map R)≤8 := by
    have low := Submodule.finrank_mono restrict
    have high := LinearMap.finrank_range_le L
    rw [Module.finrank_fin_fun] at high
    exact low.trans high
  have e7 : finrank K E=15 := (erk_midpoint_tree_rank ha ho (q:=7) (by decide) (by decide)).trans (by rw [seven])
  have c1 := finrank_annih E
  have c2 := finrank_zeroAt_annih E (Fin.last 23) C.frame.lastOut
  rw [Fintype.card_fin,e7] at c1
  have n := complement_supported_of_stage_restriction E T out (by
    change finrank K (zeroAt (annih E) (Fin.last 23))+finrank K (E.map R)≤T.card
    change 16≤T.card at rows
    omega)
  intro v hv i di
  exact n v hv i (fun e=>(Hidden.mem_activeRows i).mp e di)

/-- The actual weak trace requires fifteen distinct reverse sites, not
fifteen nominal stage clocks or merely fifteen nonzero coordinates. -/
theorem weak_fifteen_quadratic_sites [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7)=7)
    (strip : zeroSpace A 7=chain (diag (nodes A)) U w 4)
    (core : U≤width24WeakFiveCarrier A b)
    (qn : Q≠0) (qd : Q.natDegree≤4) (pd : P.natDegree≤3)
    (qFit : ∀ i,quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pFit : ∀ i,reflectedClock A i*b i*w i=P.eval (reflectedClock A i)*quadraticSeed A b i) :
    15≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card := by
  let S := weightedSites (reflectedClock A) (quadraticSeed A b)
  have C := width24_quadratic_cover ha ho
  have low : 8≤S.card := width24_quadratic_eight_sites ha ho
  by_contra! small
  change S.card<15 at small
  have twice := quadratic_seed_double_rows ho (by change S.card+2≤16;omega)
  change 2*S.card≤_ at twice
  have supp := weak_seven_support_switch ha ho C seven strip core qd qFit (by omega)
  let t := Fin.last 23
  have y0 : reflectedClock A t=0 := by change 1-nodes A (Fin.last 23)=0;rw [C.frame.lastClock,sub_self]
  have col (i : Fin 24) : A i t=0 := ha _ _ (Fin.le_last i)
  have invisible := ordered_thin_invisible_given_reps ha ho y0 col supp Q P qd
    (by omega) (by omega) (by omega) (by omega) qFit pFit
  apply qn
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero S
    (degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<S.card by omega)))
  intro a h
  obtain ⟨i,di,rfl⟩ := mem_weightedSites.mp h
  exact (mul_eq_zero.mp ((qFit i).symm.trans (invisible i).1)).resolve_right di

/-- The paid five-contrast branch exactly saturates the original
physical census, so the three-dimensional core equals the genuine
terminal-compensated carrier. No degree-four source is hypothesized. -/
theorem width24_weak_five_census [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7)=7)
    (H : FlatClockHead A 5 2 2 U w) (core : U≤width24WeakFiveCarrier A b)
    (five : 5≤(weightedSites (reflectedClock A) (reverseContrast A b Q P)).card)
    (qd : Q.natDegree≤4) (pd : P.natDegree≤3)
    (qFit : ∀ i,quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pFit : ∀ i,reflectedClock A i*b i*w i=P.eval (reflectedClock A i)*quadraticSeed A b i) :
    (weightedSites (reflectedClock A) (quadraticSeed A b)).card=15 ∧
    (Hidden.activeRows (quadraticSeed A b)).card=15 ∧
    (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=5 ∧
    (weakFiveRows A b Q P).card=5 ∧ U=width24WeakFiveCarrier A b ∧
    Width24WeakFiveChart A b w Q P := by
  classical
  let : DecidableEq K := fun a b=>Classical.propDecidable (a=b)
  let d := quadraticSeed A b
  let y := reflectedClock A
  let v := reverseContrast A b Q P
  let T := Hidden.activeRows d
  let V := Hidden.activeRows v
  let S := weightedSites y d
  let M := weightedSites y v
  let t := Fin.last 23
  have C := width24_quadratic_cover ha ho
  have strip : zeroSpace A 7=chain (diag (nodes A)) U w 4 := H.flags 2 le_rfl
  have un : (diag (nodes A)^4) w∉zeroSpace A 7 := H.unpaid
  have udim : finrank K U=3 := by
    have f := H.ranks 2 le_rfl
    change finrank K (zeroSpace A 7)=finrank K (zeroSpace A 5)+2 at f
    have g := H.baseRank
    omega
  have live : ∃ i, v i≠0 := by
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by change 5≤M.card at five; omega : 0<M.card)
    obtain ⟨i,vi,_⟩ := mem_weightedSites.mp ha
    exact ⟨i,vi⟩
  have qn : Q≠0 := by
    obtain ⟨i,vi⟩ := live
    intro z
    exact (reverse_contrast_true_support qFit pFit i vi).2.2.2.1 (by rw [z,eval_zero])
  have seed : 15≤S.card := weak_fifteen_quadratic_sites ha ho seven strip core qn qd pd qFit pFit
  have y0 : y t=0 := by change 1-nodes A (Fin.last 23)=0;rw [C.frame.lastClock,sub_self]
  have dt : d t=0 := C.lastSeed
  have vt : v t=0 := by
    change weightedEval y b (X*Q) t-weightedEval y d P t=0
    simp only [weightedEval_apply,eval_mul,eval_X,dt,y0,zero_mul,mul_zero,sub_self]
  have dSupp (i : Fin 24) (di : d i≠0) : v i=0 := by
    by_contra vi
    exact di (reverse_contrast_true_support qFit pFit i vi).1
  have gSupp (i : Fin 24) (gi : i∈Hidden.blindRows (nodes A) b d 0 t) : v i=0 := by
    by_contra vi
    have a := reverse_contrast_true_support qFit pFit i vi
    exact mul_ne_zero a.2.1 a.2.2.1 ((Hidden.mem_blindRows i).mp gi).2.2.2
  have census := Hidden.carrier_contrast_budget C.frame.lastLive.live C.lastSeed vt dSupp gSupp
  change finrank K (width24WeakFiveCarrier A b)+T.card+V.card+1≤24 at census
  have tc : S.card≤T.card := Finset.card_image_le (f:=y) (s:=T)
  have vc : M.card≤V.card := Finset.card_image_le (f:=y) (s:=V)
  have inc := Submodule.finrank_mono core
  change 5≤M.card at five
  have rk : finrank K (width24WeakFiveCarrier A b)=3 := by omega
  have eq : U=width24WeakFiveCarrier A b := Submodule.eq_of_le_of_finrank_le core (by omega)
  refine ⟨by change S.card=15;omega,by change T.card=15;omega,by change M.card=5;omega,
    by change V.card=5;omega,eq,?_⟩
  exact width24_weak_five_chart_of_strip ha ho rk (eq ▸ strip) un
    seed five qd pd qFit pFit

end
end RKResearch.Certified.ERK16

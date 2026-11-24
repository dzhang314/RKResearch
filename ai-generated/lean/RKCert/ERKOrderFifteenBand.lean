module
public import RKCert.ERKOrderFifteenChart
public import RKCert.ERKFiniteLeakage

@[expose] public section

/-! # Rank-paid order-fifteen one-head bands, without positivity -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K : Type*} [Field K] [CharZero K] {s d a r : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

omit [CharZero K] in
theorem OddSevenChart.aLe (C : OddSevenChart A d a r U w G) : a≤7 := by
  rcases C.chartType with h|h <;> omega

omit [CharZero K] in
theorem OddSevenChart.aLo (C : OddSevenChart A d a r U w G) : 6≤a := by
  rcases C.chartType with h|h <;> omega

omit [CharZero K] in
theorem OddSevenChart.band_paid {G:K[X]} (C:OddSevenChart A d a r U w G)
    {j:ℕ} (hj:a+1≤j) : forwardBand A 7 a r U w j≤defectPlus A d (j+(7-a)) := by
  have base : ∀k,chain (diag (nodes A)) U w (r+(7-4)+k)≤defectPlus A d (7+1+k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero,←C.marked.edge]
      exact firstEscape_defect
    | succ k ih =>
      rw [show r+(7-4)+(k+1)=r+(7-4)+k+1 by omega,←chain_sup_map (w:=w) C.marked.stable
        (by have := C.marked.rTwo;omega)]
      exact sup_le (ih.trans (Fplus_mono A d (by omega)))
        (((Submodule.map_mono ih).trans (Fplus_clock A d (7+1+k))).trans (Fplus_mono A d (by omega)))
  unfold forwardBand headLen
  exact (base (j-(a+1))).trans (Fplus_mono A d (by have := C.aLe;omega))

omit [CharZero K] in
theorem OddSevenChart.band_sep {G:K[X]} (S:Saturated A b 7 1) (M:Margin A b 7 1 d)
    (C:OddSevenChart A d a r U w G) {j:ℕ} (hj:a+1≤j) (hmax:j≤12)
    (P:K[X]) (hd:P.natDegree≤a) (hP:evalNodes A P∈forwardBand A 7 a r U w j) :
    P=0 := by
  classical
  have aLe := C.aLe
  have hEval : Function.Injective (polyEval A a) := (injective_iff_map_eq_zero _).mpr fun t ht=>by
    have h := evalNodes_ofFn A a t
    have hd : (ofFn (a+1) t).natDegree≤7 := by have := ofFn_natDegree_lt (show 1≤a+1 by omega) t;omega
    have he : ofFn (a+1) t=0 :=
      separated_plus S M _ hd (by rw [h,ht];exact (defectPlus A d 7).zero_mem)
    ext i
    have hz:=congrArg (fun P:K[X]=>P.coeff i.val) he
    rwa [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] at hz
  have pRank : finrank K (polyBand A a)=a+1 := by
    unfold polyBand
    rw [LinearMap.finrank_range_of_inj hEval]
    simp
  let B := forwardBand A 7 a r U w j
  have cap : finrank K B≤finrank K U+headLen 7 a r j :=
    RKCert.Paired.OrderTwelve.chain_rank_cap _
  have hr := Submodule.finrank_sup_add_finrank_inf_eq (polyBand A a) B
  have he := C.chart j hj hmax
  change treePlus A d j=polyBand A a⊔B at he
  rw [←he,C.rich j hj hmax,pRank] at hr
  have zero : finrank K ↥(polyBand A a⊓B)=0 := by
    have := C.marked.rank
    unfold headLen at cap
    omega
  have hbot := Submodule.finrank_eq_zero.mp zero
  have h := Submodule.mem_inf.mpr ⟨eval_polyBand (A:=A) hd,hP⟩
  have vh : evalNodes A P=0 := (Submodule.mem_bot K).mp (hbot ▸ h)
  apply separated_plus S M P (by omega)
  rw [vh]
  exact (defectPlus A d 7).zero_mem

omit [CharZero K] in
theorem OddSevenChart.sites {G:K[X]} (C:OddSevenChart A d a r U w G) :
    headLen 7 a r (12)≤(headSites (nodes A) w).card := by
  let j := 11
  let n := headLen 7 a r j
  have aLe := C.aLe
  have i1 : a+1≤j := by dsimp [j];omega
  have i2 : j≤12 := by dsimp [j];omega
  have i3 : j+1=12 := rfl
  have eOld := C.chart j i1 i2
  have eNew := C.chart (j+1) (by omega) (by omega)
  have hr1 := C.rich j i1 i2
  have hr2 := C.rich (j+1) (by omega) (by omega)
  have len : headLen 7 a r (j+1)=n+1 := by unfold n headLen;omega
  let D := diag (nodes A)
  have base : chain D U w n≤treePlus A d j := le_sup_right.trans (le_of_eq eOld.symm)
  have old := (chain_le_iff n).mp base
  have hnot : (D^n) w∉treePlus A d j := by
    intro hp
    have hc : forwardBand A 7 a r U w (j+1)≤treePlus A d j := by
      unfold forwardBand
      rw [len]
      exact (chain_le_iff _).mpr ⟨old.1, fun k hk => by
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with e|e
        · exact e ▸ hp
        · exact old.2 _ e⟩
    have hh : treePlus A d (j+1)≤treePlus A d j := by
      rw [eNew]
      exact sup_le (le_sup_left.trans (le_of_eq eOld.symm)) hc
    have rr := Submodule.finrank_mono hh
    omega
  have cnt := more_sites_than_paid old.2 hnot
  rw [←i3,len]
  omega

omit [CharZero K] in
theorem OddSevenChart.band_next (C:OddSevenChart A d a r U w G) {j:ℕ} (hj:a+1≤j) :
    forwardBand A 7 a r U w j ⊔ (forwardBand A 7 a r U w j).map (diag (nodes A))=
      forwardBand A 7 a r U w (j+1) := by
  have hlen:headLen 7 a r (j+1)=headLen 7 a r j+1 := by unfold headLen;omega
  unfold forwardBand
  rw [hlen]
  exact chain_sup_map C.marked.stable (by unfold headLen;have:=C.marked.rTwo;omega)

omit [CharZero K] in
theorem OddSevenChart.band_first (C:OddSevenChart A d a r U w G) {j:ℕ} (_hj:a+1≤j) :
    firstEscape A d 7≤forwardBand A 7 a r U w j := by
  rw [C.marked.edge]
  unfold forwardBand headLen
  have old := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+(7-4)+(j-(a+1)))).mp le_rfl
  exact (chain_le_iff _).mpr ⟨old.1,fun k hk=>old.2 k (by omega)⟩

end RKCert.Paired.FiniteMidpoint

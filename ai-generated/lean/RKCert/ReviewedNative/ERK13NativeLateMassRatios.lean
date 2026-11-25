module

public import RKCert.ReviewedNative.ERK13NativeLateMassSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Uniform marked late ratio obstruction

The clock-one twin correction converts the paid literal row b*w to the
marked reverse flag. The two ratios comparison is then independent of
purity of the square, nonzero constant terms, or an origin normalization. -/

namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Reverse Polynomial Module PhysicalCensus ERK13OrdinarySquare NativeFinalThree
open scoped Classical Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
variable {P R Q G : K[X]}
variable {e : Fin 18 → Fin 19} {r : Fin 19 → Fin 18} {m : Fin 19}
set_option maxHeartbeats 1800000

private def terminalContrast (K : Type*) [Field K] (j : Fin 19) : Fin 19 → K :=
  coordinate (Fin.last 18)-coordinate j

private theorem coordinate_point (i j : Fin 19) :
    coordinate (K:=K) j i = (if i=j then 1 else 0) := by
  classical
  by_cases h : i=j
  · subst i
    simp [coordinate]
  · simp [coordinate,h,Ne.symm h]

private theorem row_coordinate_left (i : Fin 19) (v : Fin 19 → K) :
    row (coordinate i) v=v i := by
  rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]

private theorem reflected_last_zero (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b=0) :
    reflectedClock A (Fin.last 18)=0 := by
  change (1:K)-nodes A (Fin.last 18)=0
  rw [(ERK13NativeFirst.last_original_active ha ho).node_eq_one ha seed,sub_self]

private theorem weighted_head_annih_eight (ho : HasOrder 13 A b) (pay : w∈zeroSpace A 4) :
    (fun i=>b i*w i) ∈ annih (treeSpace A 8) := by
  apply mem_annih.mpr
  intro v hv
  have product : w*v∈zeroSpace A (4+8) :=
    zeroSpace_mul_treeSpace ho (by decide : 8+1≤13) pay hv
  have test := probe_zeroSpace (k:=0) ho (by decide : 0+(4+8)+1≤13) product
  calc
    _ = probe A b 0 (w*v) := by
      simp only [probe,pow_zero,mul_one,row_apply,dotProduct,Pi.mul_apply,mul_assoc]
    _ = 0 := test

/-- Subtract only the actual terminal contrast of the old unmarked
fiber. Both of its stages have reflected clock zero. -/
private theorem corrected_head_paid (S : MassClassChart A U w P R Q G)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    {rad : ℕ} {V : Submodule K (Fin 19→K)} {v : Fin 19→K}
    (head : ERK13NativeFirst.NativePaidHead A b rad V v) :
    ∃ j : Fin 19, reflectedClock A j=0 ∧
      ((fun i=>b i*w i)-(b (Fin.last 18)*w (Fin.last 18)) • terminalContrast K j)
        ∈ primitiveBack A b 3 := by
  let L := Fin.last 18
  obtain ⟨j,jL,pair⟩ := exists_terminal_twin S
  have lastY : reflectedClock A L=0 := reflected_last_zero ha ho seed
  have twinY : reflectedClock A j=0 := by
    have same := (phase_clock_head S pair).1
    simpa only [reflectedClock,Pi.sub_apply,Pi.one_apply,same] using lastY
  let tau : Fin 19 → K := fun i=>b i*w i
  let delta := terminalContrast K j
  have deltaL : delta L=1 := by
    change coordinate (K:=K) L L-coordinate j L=1
    have a : coordinate (K:=K) L L=1 := by rw [coordinate_point]; simp
    have d : coordinate (K:=K) j L=0 := by
      rw [coordinate_point]
      exact if_neg (Ne.symm jL)
    rw [a,d,sub_zero]
  have deltaPaid : delta ∈ annih (treeSpace A 8) := by
    apply mem_annih.mpr
    intro f hf
    have same := phase_const_of_mem (S.eightInside hf) pair
    calc
      _ = f L-f j := by
        change dotProduct (coordinate (K:=K) L-coordinate j) f=f L-f j
        rw [sub_dotProduct]
        change row (coordinate L) f-row (coordinate j) f=f L-f j
        rw [row_coordinate_left,row_coordinate_left]
      _ = 0 := sub_eq_zero.mpr same.symm
  have corrected : tau-tau L • delta ∈ annih (treeSpace A 8) :=
    (annih (treeSpace A 8)).sub_mem (weighted_head_annih_eight ho S.headFour)
      ((annih (treeSpace A 8)).smul_mem _ deltaPaid)
  have correctedL : (tau-tau L • delta) L=0 := by
    change tau L-tau L*delta L=0
    rw [deltaL,mul_one,sub_self]
  have marked : tau-tau L • delta ∈ annih (markedTreeSpace A b 8) := by
    change _ ∈ annih (treeSpace A 8⊔terminalMark A b)
    rw [terminalMark,if_pos seed,annih_sup_coordinate,mem_zeroAt]
    exact ⟨corrected,correctedL⟩
  have rk := (ERK13NativeFirst.marked_staircase_ranks13 ha ho head seed).1 8 (by decide) (by decide)
  have eq := (ERK13NativeFirst.exact_marked_reverse13 ha ho
    (ERK13NativeFirst.last_original_active ha ho) seed (by decide : 8≤11) rk).1
  change primitiveBack A b 3=annih (markedTreeSpace A b 8) at eq
  refine ⟨j,twinY,?_⟩
  rw [eq]
  exact marked

private theorem fold_fibre_multiplier (u : Fin 19 → K) (x : Fin 18 → K) (t : Fin 18) :
    foldLinear r (fun i=>u i*x (r i)) t=foldLinear r u t*x t := by
  change (∑ i ∈ Finset.univ.filter (fun i=>r i=t),u i*x (r i))=
    (∑ i ∈ Finset.univ.filter (fun i=>r i=t),u i)*x t
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- One original paid affine law suffices for both P=0 and P≠0. The
singleton at stage L is not treated as its old twin in the marked fold. -/
theorem folded_head_affine_off_one (S : MassClassChart A U w P R Q G)
    (fibres : LateFibres A U w e r)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    {rad : ℕ} {V : Submodule K (Fin 19→K)} {v : Fin 19→K}
    (head : ERK13NativeFirst.NativePaidHead A b rad V v)
    (cy : ∀ i, reflectedClock A (e (r i))=reflectedClock A i)
    (lifts : ∀ t : Fin 18, (fun i=>coordinate (K:=K) t (r i)) ∈
      treeSpace A 10⊔K∙coordinate (Fin.last 18))
    (covers : ReverseCover A b (rowDelta A e r m)) :
    ∃ a d : K, ∀ t, reflectedClock A (e t)≠0 →
      foldLinear r b t*w (e t)=foldLinear r (rowDelta A e r m) t*(a+d*reflectedClock A (e t)) := by
  let L := Fin.last 18
  let D := rowDelta A e r m
  let tau : Fin 19 → K := fun i=>b i*w i
  let rho := reflectedStageRow A b 1
  let y : Fin 18 → K := fun t=>reflectedClock A (e t)
  obtain ⟨j,jY,paid⟩ := corrected_head_paid S ha ho seed head
  let delta := terminalContrast K j
  let z := tau-tau L • delta
  have mz : z∈primitiveBack A b 3 := paid
  obtain ⟨h,a,d,fit⟩ := covers.third z mz
  have Fρ : ∀ t, foldLinear r rho t=0 := fold_first_paid ha ho seed lifts
  have amp (i : Fin 19) : w i=w (e (r i)) :=
    (phase_clock_head S (congrArg Prod.fst ((fibres i (r i)).mp rfl))).2
  have ftau (t : Fin 18) : foldLinear r tau t=foldLinear r b t*w (e t) := by
    have eq : tau=(fun i=>b i*w (e (r i))) := by
      funext i
      exact congrArg (fun c=>b i*c) (amp i)
    rw [eq]
    exact fold_fibre_multiplier b (fun k=>w (e k)) t
  have fdelta (t : Fin 18) (off : y t≠0) : foldLinear r delta t=0 := by
    have lastY : reflectedClock A L=0 := reflected_last_zero ha ho seed
    change (∑ i ∈ Finset.univ.filter (fun i=>r i=t),delta i)=0
    apply Finset.sum_eq_zero
    intro i hi
    have iy : reflectedClock A i=y t := by
      have cls := (Finset.mem_filter.mp hi).2
      have ci := cy i
      rw [cls] at ci
      exact ci.symm
    have iL : i≠L := by
      intro atL
      rw [atL,lastY] at iy
      exact off iy.symm
    have ij : i≠j := by
      intro atJ
      rw [atJ,jY] at iy
      exact off iy.symm
    change coordinate (K:=K) L i-coordinate j i=0
    rw [coordinate_point i L,coordinate_point i j,if_neg iL,if_neg ij,sub_self]
  have fz (t : Fin 18) : foldLinear r z t=foldLinear r D t*(a+d*y t) := by
    have eq : z=h • rho+(fun i=>D i*(a+d*y (r i))) := by
      funext i
      change z i=h*rho i+D i*(a+d*y (r i))
      exact (fit i).trans (by rw [show y (r i)=reflectedClock A i from cy i])
    rw [eq,map_add,map_smul]
    change h*foldLinear r rho t+foldLinear r (fun i=>D i*(a+d*y (r i))) t=_
    rw [Fρ,mul_zero,zero_add,fold_fibre_multiplier D (fun k=>a+d*y k) t]
  refine ⟨a,d,fun t off=>?_⟩
  have hz := fz t
  change foldLinear r (tau-tau L • delta) t=_ at hz
  rw [map_sub,map_smul] at hz
  change foldLinear r tau t-tau L*foldLinear r delta t=_ at hz
  rw [fdelta t off,mul_zero,sub_zero,ftau] at hz
  exact hz

/-- At a repeated nonterminal clock the common nonzero normalized mass
determines the actual head amplitude. There is no nonzero-slope premise. -/
theorem distinguished_from_head_affine (S : MassClassChart A U w P R Q G)
    (fibres : LateFibres A U w e r)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (offCore : ∀ t, reflectedClock A (e t)≠0 → foldLinear r (rowDelta A e r m) t≠0 →
      ¬LiveCore.live U (e t))
    (law : ∃ a d : K, ∀ t, reflectedClock A (e t)≠0 →
      foldLinear r b t*w (e t)=foldLinear r (rowDelta A e r m) t*(a+d*reflectedClock A (e t))) :
    DistinguishedRatios (foldLinear r b) (fun t=>reflectedClock A (e t))
      (foldLinear r (rowDelta A e r m)) := by
  let beta := foldLinear r b
  let lam := foldLinear r (rowDelta A e r m)
  let y : Fin 18 → K := fun t=>reflectedClock A (e t)
  change DistinguishedRatios beta y lam
  intro i j distinct li lj clock yi ratioNe ratioEq
  have yj : y j≠0 := by rwa [←clock]
  have lastY := reflected_last_zero ha ho seed
  have iL : e i ≠ Fin.last 18 := by
    intro ij
    apply yi
    change reflectedClock A (e i) = 0
    rw [ij]
    exact lastY
  have jL : e j ≠ Fin.last 18 := by
    intro ij
    apply yj
    change reflectedClock A (e j) = 0
    rw [ij]
    exact lastY
  obtain ⟨a,d,law⟩ := law
  have rel (t : Fin 18) (lt : lam t≠0) (yt : y t≠0) :
      (beta t*y t/lam t)*w (e t)=(a+d*y t)*y t := by
    have h : beta t*w (e t)=lam t*(a+d*y t) := law t yt
    calc
      _ = (beta t*w (e t))/lam t*y t := by ring
      _ = (lam t*(a+d*y t))/lam t*y t := by rw [h]
      _ = _ := by field_simp [lt] <;> ring
  have eqAmp : w (e i)=w (e j) := by
    apply mul_left_cancel₀ ratioNe
    calc
      _ = (a+d*y i)*y i := rel i li yi
      _ = (a+d*y j)*y j := by rw [clock]
      _ = (beta j*y j/lam j)*w (e j) := (rel j lj yj).symm
      _ = (beta i*y i/lam i)*w (e j) := by rw [ratioEq]
  have eqClock : nodes A (e i)=nodes A (e j) := by
    change (1:K)-nodes A (e i)=1-nodes A (e j) at clock
    linear_combination -clock
  have pair : headPair A w (e i)=headPair A w (e j) := Prod.ext eqClock eqAmp
  have phase := (dead_pair_label_iff (A:=A) (w:=w) (offCore i yi li) (offCore j yj lj)).mpr pair
  have marked := (late_label_off_last (A:=A) (U:=U) (w:=w) iL jL).mpr phase
  exact distinct (((fibres (e i) i).mpr rfl).symm.trans ((fibres (e i) j).mpr marked))

/-- End of the genuine leading-mismatch residual. The only remaining
producer boundary is the native `MassClassChart` itself. -/
theorem leading_class_chart_impossible (S : MassClassChart A U w P R Q G)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    {rad : ℕ} {V : Submodule K (Fin 19→K)} {v : Fin 19→K}
    (head : ERK13NativeFirst.NativePaidHead A b rad V v) : False := by
  classical
  obtain ⟨size,masks⟩ := marked_label_card_and_masks S ha ho seed head
  have clock (i j : Fin 19) (eq : lateLabel A U w i=lateLabel A U w j) :
      reflectedClock A i=reflectedClock A j := by
    have read := (phase_clock_head S (congrArg Prod.fst eq)).1
    simp only [reflectedClock,Pi.sub_apply,Pi.one_apply,read]
  obtain ⟨e,r,m,chart,fibres,cy,live,off,tail,lifts⟩ :=
    actual_pair_of_marked_labels ha ho seed (lateLabel A U w) size clock masks
  obtain ⟨inTwo,covers⟩ :=
    covers_of_marked_staircase chart ha ho seed head cy live off tail lifts
  have split := observer_annihilator_split S chart ha ho seed head live off tail inTwo
  obtain ⟨mass,offCore⟩ := mass_support_and_offcore S fibres ha ho seed inTwo split
  have supp := fourteen_carrier_sites (b:=b) S fibres chart ha split
  have law := folded_head_affine_off_one S fibres ha ho seed head cy lifts covers
  have ratios := distinguished_from_head_affine S fibres ha ho seed offCore law
  exact impossible_of_original chart ha ho seed cy live off tail lifts inTwo covers
    (by omega) mass ratios

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

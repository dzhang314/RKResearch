module

public import RKCert.ReviewedNative.NativeSilentStage
public import RKCert.ReviewedNative.NativeConstantProbeDefect
public import RKCert.ReviewedNative.ERK13NativeWidth19EndpointOrder
public import RKCert.ReviewedNative.ClockOneLiveSuffix
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The literal penultimate is active, off clock one, and supplies the endpoint

The row indices below are the original physical Fin 19 indices. No
hypothesis about a compressed label, a folded row, or the field order
is used. In particular the stage immediately preceding the endpoint
must enter the actual endpoint quadrature row with nonzero coefficient. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst
open RKResearch Reverse Module
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

abbrev penultimate19 : Fin 19 := 17

private theorem le_penultimate_of_ne_last {j : Fin 19} (h : j≠Fin.last 18) : j≤penultimate19 := by
  have nz : j.val≠18 := fun e=>h (Fin.ext e)
  change j.val≤17
  have := j.isLt
  omega

private theorem no_ordinary (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    firstSeed A b=0 := by
  by_contra nz
  exact ordinary_width19_impossible ha ho nz

/-- The literal last reflected equation at the immediately previous row. -/
theorem penultimate_flux13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    A (Fin.last 18) penultimate19*b (Fin.last 18)=b penultimate19*(1-nodes A penultimate19) := by
  have b0 : reflectedStageWeight A b 0=b := by funext i; simp [reflectedStageWeight]
  have m : (A.transpose*ᵥb) penultimate19=A (Fin.last 18) penultimate19*b (Fin.last 18) := by
    change (∑ j : Fin 19,A j penultimate19*b j)=_
    exact Finset.sum_eq_single (Fin.last 18)
      (fun j _ hj=>by rw [ha _ _ (le_penultimate_of_ne_last hj),zero_mul]) (by simp)
  have h := congrFun (no_ordinary ha ho) penultimate19
  change reflectedStageRow A b 0 penultimate19=0 at h
  rw [reflectedStageRow,b0] at h
  simpa only [Nat.zero_add,Nat.cast_one,one_smul,Pi.sub_apply,reflectedStageWeight,pow_one,
    m,Pi.one_apply,sub_eq_zero] using h

theorem penultimate_live13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    b penultimate19≠0 := by
  intro dead
  have flux := penultimate_flux13 ha ho
  rw [dead,zero_mul] at flux
  have silent := (mul_eq_zero.mp flux).resolve_right (last_original_active ha ho).live
  have all (j : Fin 19) : A j penultimate19=0 := by
    by_cases h : j=Fin.last 18
    · simpa only [h] using silent
    · exact ha _ _ (le_penultimate_of_ne_last h)
  obtain ⟨strict,small⟩ := delete_silent_stage ha ho penultimate19 dead all
  exact (by decide : ¬(19≤18)) (stage_floor19 strict small)

/-- Any suffix with all its live clocks at one has no second live stage.
The underlying primitive reverse rows vanish there for their actual
chronology; the compensated midpoint calculation then reads the last row. -/
theorem only_terminal_live_on_clock_one_suffix13
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) {u i : Fin 19}
    (hOne : ∀ (j : Fin 19), u ≤ j → b j ≠ 0 → nodes A j = 1)
    (ui : u ≤ i) (nl : i ≠ Fin.last 18) : b i = 0 := by
  by_contra bi
  have ci := hOne i ui bi
  have seed := no_ordinary ha ho
  have L := last_original_active ha ho
  have cl := L.node_eq_one ha seed
  have cz : nodes A (0:Fin 19)=0 := by
    change (∑ j,A 0 j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have ni : (0:Fin 19)≠i := by
    intro eq
    exact zero_ne_one (cz.symm.trans (eq.symm ▸ ci))
  obtain ⟨r,U,w,H⟩ := paid_head_of_order ha ho
  have rk := (marked_staircase_ranks13 ha ho H seed).1 6 (by decide) (by decide)
  have full := (exact_marked_reverse13 ha ho L seed (by decide : 6≤11) rk).1
  have atI : coordinate (K:=K) i∈markedTreeSpace A b 6 := by
    rw [←annih_annih (markedTreeSpace A b 6)]
    apply mem_annih.mpr
    intro y hy
    have inBack := full.symm ▸ hy
    have v := mem_tailZero.mp (primitiveBack_tail_of_live_clock_one ha seed hOne (11-6) inBack) i ui
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate,v]
  have mark : terminalMark A b=K∙coordinate (K:=K) (Fin.last 18) := by
    unfold terminalMark
    split
    · rfl
    · exact False.elim (‹firstSeed A b≠0› seed)
  change coordinate (K:=K) i∈treeSpace A 6⊔terminalMark A b at atI
  rw [mark] at atI
  obtain ⟨x,hx,v,hv,e⟩ := Submodule.mem_sup.mp atI
  obtain ⟨k,rfl⟩ := Submodule.mem_span_singleton.mp hv
  have x0 : x 0=0 := by
    have h := congrFun e 0
    have zl : (0:Fin 19)≠Fin.last 18 := by decide
    simpa [coordinate,ni,zl] using h
  have pi (t : ℕ) : probe A b t (coordinate i)=b i := by
    change row _ (coordinate i)=_
    rw [row_coordinate,ci,one_pow,mul_one]
  have pl (t : ℕ) : probe A b t (coordinate (Fin.last 18))=b (Fin.last 18) := by
    change row _ (coordinate (Fin.last 18))=_
    rw [row_coordinate,cl,one_pow,mul_one]
  have tests (j : Fin (6+1)) : probe A b j.val x=b i-k*b (Fin.last 18) := by
    have h := congrArg (probe A b j.val) e
    rw [map_add,map_smul,smul_eq_mul,pi,pl] at h
    exact eq_sub_iff_add_eq.mpr h
  obtain ⟨df,bal⟩ := defect_of_constant_probe_at_origin_zero ha ho (by decide : 2*6+1≤13) hx x0 tests
  have xL := (width19_last_node_clean_six ha ho).2 x df
  have k0 : k=0 := by
    have h := congrFun e (Fin.last 18)
    change x (Fin.last 18) + k * coordinate (K:=K) (Fin.last 18) (Fin.last 18) =
      coordinate (K:=K) i (Fin.last 18) at h
    have self : coordinate (K:=K) (Fin.last 18) (Fin.last 18) = 1 :=
      @Pi.single_eq_same (Fin 19) (fun _ => K) _ (Classical.decEq _) (Fin.last 18) 1
    have off : coordinate (K:=K) i (Fin.last 18) = 0 :=
      @Pi.single_eq_of_ne (Fin 19) (fun _ => K) _ (Classical.decEq _) i (Fin.last 18) (Ne.symm nl) 1
    rwa [xL, self, off, mul_one, zero_add] at h
  exact bi (by simpa only [k0,zero_mul,sub_zero] using bal)

theorem penultimate_clock_ne_one13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    nodes A penultimate19≠1 := by
  intro atOne
  have one (j : Fin 19) (hj : penultimate19≤j) (_ : b j≠0) : nodes A j=1 := by
    by_cases h : j=Fin.last 18
    · simpa only [h] using (last_original_active ha ho).node_eq_one ha (no_ordinary ha ho)
    · simpa only [le_antisymm (le_penultimate_of_ne_last h) hj] using atOne
  exact penultimate_live13 ha ho
    (only_terminal_live_on_clock_one_suffix13 ha ho one le_rfl (by decide))

theorem penultimate_feeds_terminal13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    A (Fin.last 18) penultimate19≠0 := by
  intro cut
  have h := penultimate_flux13 ha ho
  rw [cut,zero_mul] at h
  exact (mul_ne_zero (penultimate_live13 ha ho) (sub_ne_zero.mpr (Ne.symm (penultimate_clock_ne_one13 ha ho)))) h.symm

end
end RKResearch.Certified.Graded.ERK13NativeFirst

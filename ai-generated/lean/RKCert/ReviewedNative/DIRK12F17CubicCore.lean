module

public import RKCert.ReviewedNative.DIRK12F17CubicData
public import RKCert.ReviewedNative.DualSupport12
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Literal low-grade receipts for the characteristic-17 midpoint tableau.
These checks use six small bases and the complementary support criterion;
they do not enumerate the rooted trees. -/
namespace RKResearch.Certified.DIRK12F17Cubic

open RKResearch Graded
open scoped Matrix BigOperators

set_option linter.unusedSectionVars false

abbrev V := Fin 15 → Raw
abbrev VecEq (u v : V) : Prop := ∀ i, u i = v i

abbrev ghost (i : Fin 15) : Prop := 1 ≤ i.val ∧ i.val ≤ 4
def rawA (i j : Fin 15) : Raw := if i < j then num 0 else (aData[i.val]!)[j.val]!
def rawB : V := fun i => bData[i.val]!
def rawC : V := fun i => cData[i.val]!
def rawY : V := fun i => sub (num 1) (rawC i)
def rawOne : V := fun _ => num 1

def width (d : Nat) : Nat := min 3 (d-2)
def genF (i : Nat) : V := fun j => (gData[i]!)[j.val]!
def genB (i : Nat) : V := fun j => (hData[i]!)[j.val]!
def coef (op d i j : Nat) : Raw := (((coefData[op]!)[d]!)[i]!)[j]!

def act (M : Fin 15 → Fin 15 → Raw) (v : V) : V :=
  fun i => csum fun j => mul (M i j) (v j)

def rdot (u v : V) : Raw := csum fun j => mul (u j) (v j)
def mulV (u v : V) : V := fun j => mul (u j) (v j)
def subV (u v : V) : V := fun j => sub (u j) (v j)
def powV (u : V) (k : Nat) : V := fun j => power (u j) k
def scale (n : Nat) (u : V) : V := fun j => mul (num n) (u j)
def powC (k : Nat) : V := powV rawC k
def rW (k : Nat) : V := mulV rawB (powV rawY k)

def combo (g : Nat → V) (d op i : Nat) : V :=
  fun j => csum fun s : Fin (width (d+1)) => mul (coef op d i s.val) (g s.val j)

def A0 := act rawA
def N0 := act (fun i j => rawA j i)
def fprim (d : Nat) : V := subV (scale (d+1) (A0 (powC d))) (powC (d+1))
def bprim (d : Nat) : V := subV (scale (d+1) (N0 (rW d))) (rW (d+1))

def nextDefect : Raw := sub (mul (num 13) (rdot rawB (powC 12))) (num 1)

structure Receipts : Prop where
  nodes : VecEq (A0 rawOne) rawC
  ghosts : ∀ i, ghost i → rawB i = num 0
  fSupport : ∀ k : Fin 3, ∀ i, ¬ ghost i → genF k.val i = num 0
  bSupport : ∀ k : Fin 3, ∀ i, ghost i → genB k.val i = num 0
  fA : ∀ d < 5, ∀ k : Fin (width d), VecEq (A0 (genF k.val)) (combo genF d 0 k.val)
  fC : ∀ d < 5, ∀ k : Fin (width d), VecEq (mulV rawC (genF k.val)) (combo genF d 1 k.val)
  fP : ∀ d < 5, VecEq (fprim d) (combo genF d 2 0)
  bA : ∀ d < 5, ∀ k : Fin (width d), VecEq (N0 (genB k.val)) (combo genB d 3 k.val)
  bY : ∀ d < 5, ∀ k : Fin (width d), VecEq (mulV rawY (genB k.val)) (combo genB d 4 k.val)
  bP : ∀ d < 5, VecEq (bprim d) (combo genB d 5 0)
  bSilent : ∀ d ≤ 5, ∀ j, d+j < 12 → ∀ k : Fin (width d), rdot (genB k.val) (powC j) = num 0
  fASilent : ∀ k i : Fin 3, rdot (genB i.val) (A0 (genF k.val)) = num 0
  fAMoment : ∀ k : Fin 3, ∀ j : Fin 6, rdot (rW j.val) (A0 (genF k.val)) = num 0
  fPSilent : ∀ i : Fin 3, rdot (genB i.val) (fprim 5) = num 0
  fPMoment : ∀ j : Fin 6, rdot (rW j.val) (fprim 5) = num 0
  scalar : ∀ j < 12, mul (num (j+1)) (rdot rawB (powC j)) = num 1
  witness : nextDefect = ⟨11,7,12⟩
  nextUnit : mul nextDefect starInverse = num 1
  diagUnit : mul (rawA 1 1) diagInverse = num 1
  firstDiag : rawA 0 0 = num 0

section
variable {K : Type*} [CommRing K] [CharP K 17]
variable {z : K} (h : IsCubic z) (cert : Receipts)

def ev (z : K) (v : V) : Fin 15 → K := fun j => val z (v j)
def A (z : K) : Matrix (Fin 15) (Fin 15) K := fun i j => val z (rawA i j)
def b (z : K) : Fin 15 → K := ev z rawB

theorem lower (z : K) : Matrix.IsLowerTriangular (A z) := by
  intro i j hij
  change i < j at hij
  simp [A, rawA, hij]

theorem ev_eq {u v : V} (e : VecEq u v) : ev z u = ev z v :=
  funext fun i => congrArg (val z) (e i)

theorem ev_one : ev z rawOne = (1 : Fin 15 → K) := by
  ext i
  simp [ev, rawOne]

include h in
theorem ev_A (v : V) : ev z (A0 v) = mat (A z) (ev z v) := by
  ext i
  simp only [ev, A0, act, val_csum, val_mul h, mat_apply, Matrix.mulVec_apply_eq_sum, A]

include h in
theorem ev_N (v : V) : ev z (N0 v) = mat (A z).transpose (ev z v) := by
  ext i
  simp only [ev, N0, act, val_csum, val_mul h, mat_apply, Matrix.mulVec_apply_eq_sum,
    Matrix.transpose_apply, A]

include h in
theorem ev_dot (u v : V) : val z (rdot u v) = row (ev z u) (ev z v) := by
  simp only [rdot, val_csum, val_mul h, row_apply, dotProduct, ev]

theorem ev_comm (u v : V) :
    row (ev z u) (ev z v) = row (ev z v) (ev z u) := by
  simp only [row_apply, dotProduct_comm]

include h in
theorem ev_mulV (u v : V) : ev z (mulV u v) = ev z u * ev z v := by
  ext i
  simp only [ev, mulV, val_mul h, Pi.mul_apply]

include h in
theorem ev_powV (u : V) (k : Nat) : ev z (powV u k) = (ev z u)^k := by
  ext i
  simp only [ev, powV, val_power h, Pi.pow_apply]

include h in
theorem ev_subV (u v : V) : ev z (subV u v) = ev z u - ev z v := by
  ext i
  simp only [ev, subV, val_sub h, Pi.sub_apply]

include h in
theorem ev_scale (n : Nat) (u : V) : ev z (scale n u) = (n:K) • ev z u := by
  ext i
  simp only [ev, scale, val_mul h, val_num, Pi.smul_apply, smul_eq_mul]

include h cert in
theorem ev_C : ev z rawC = nodes (A z) := by
  have e := ev_eq (z:=z) cert.nodes
  rw [ev_A h, ev_one] at e
  exact e.symm

include h cert in
theorem ev_Y : ev z rawY = DualSupport12.reflected (A z) := by
  change ev z (subV rawOne rawC) = _
  rw [ev_subV h, ev_one, ev_C h cert, DualSupport12.reflected]

include h cert in
theorem ev_X (k : Nat) : ev z (powC k) = (nodes (A z))^k := by
  rw [powC, ev_powV h, ev_C h cert]

include h cert in
theorem ev_W (k : Nat) : ev z (rW k) = DualSupport12.moment (A z) (b z) k := by
  rw [rW, ev_mulV h, ev_powV h, ev_Y h cert, DualSupport12.moment, b]

include h cert in
theorem ev_F (d : Nat) : ev z (fprim d) = DualSupport12.forward (A z) d := by
  rw [fprim, ev_subV h, ev_scale h, ev_A h, ev_X h cert, ev_X h cert]
  rfl

include h cert in
theorem ev_B (d : Nat) : ev z (bprim d) = DualSupport12.reverse (A z) (b z) d := by
  rw [bprim, ev_subV h, ev_scale h, ev_N h, ev_W h cert, ev_W h cert]
  rfl

def band (z : K) (gen : Nat → V) (d : Nat) : Submodule K (Fin 15 → K) :=
  Submodule.span K (Set.range (fun j : Fin (width d) => ev z (gen j.val)))

theorem span_gen {gen : Nat → V} {d : Nat} (i : Fin (width d)) :
    ev z (gen i.val) ∈ band z gen d := Submodule.subset_span ⟨i,rfl⟩

theorem band_mono (gen : Nat → V) (d : Nat) :
    band z gen d ≤ band z gen (d+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have e : width d ≤ width (d+1) := by unfold width; omega
  exact span_gen (⟨i.val, i.isLt.trans_le e⟩ : Fin (width (d+1)))

include h in
theorem combo_mem (gen : Nat → V) (d op i : Nat) :
    ev z (combo gen d op i) ∈ band z gen (d+1) := by
  have e : ev z (combo gen d op i) =
      ∑ j : Fin (width (d+1)), val z (coef op d i j.val) • ev z (gen j.val) := by
    ext k
    simp only [ev, combo, val_csum, val_mul h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact Submodule.sum_mem _ fun j _ => (band z gen (d+1)).smul_mem _ (span_gen j)

theorem span_by_linear (gen : Nat → V) (d : Nat) {M : (Fin 15 → K) →ₗ[K] (Fin 15 → K)}
    {S : Submodule K (Fin 15 → K)} (hs : ∀ j : Fin (width d), M (ev z (gen j.val)) ∈ S) :
    ∀ v ∈ band z gen d, M v ∈ S := by
  have a : band z gen d ≤ S.comap M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hs i
  intro v hv
  exact a hv

theorem span_by_zero (gen : Nat → V) (d : Nat) {M : (Fin 15 → K) →ₗ[K] K}
    (hs : ∀ j : Fin (width d), M (ev z (gen j.val)) = 0) :
    ∀ v ∈ band z gen d, M v = 0 := by
  have a : band z gen d ≤ LinearMap.ker M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hs i
  intro v hv
  exact a hv

include cert in
theorem f_supported {d : Nat} (_hd : d ≤ 5) :
    ∀ v ∈ band z genF d, DualSupport12.supported ghost v := by
  intro v hv i hi
  exact span_by_zero genF d (M:=LinearMap.proj i) (fun j => by
    have bnd : j.val < 3 := j.isLt.trans_le (Nat.min_le_left ..)
    simp [LinearMap.proj_apply, ev, cert.fSupport ⟨j.val,bnd⟩ i hi] ) v hv

include cert in
theorem b_supported {d : Nat} (_hd : d ≤ 5) :
    ∀ v ∈ band z genB d, DualSupport12.zeroAt ghost v := by
  intro v hv i hi
  exact span_by_zero genB d (M:=LinearMap.proj i) (fun j => by
    have bnd : j.val < 3 := j.isLt.trans_le (Nat.min_le_left ..)
    simp [LinearMap.proj_apply, ev, cert.bSupport ⟨j.val,bnd⟩ i hi] ) v hv

include h cert in
theorem checked_high (v : V)
    (bSilent : ∀ i : Fin 3, rdot (genB i.val) v = num 0)
    (bMoment : ∀ j : Fin 6, rdot (rW j.val) v = num 0) :
    ev z v ∈ DualSupport12.high (A z) (b z) (band z genB) 5 := by
  apply DualSupport12.mem_high.mpr
  refine ⟨fun w hw => ?_, fun j hj => ?_⟩
  · rw [row_apply, dotProduct_comm, ← row_apply]
    exact span_by_zero genB 5 (M:=row (ev z v)) (fun i => by
      rw [ev_comm, ← ev_dot h]
      have e : i.val < 3 := i.isLt.trans_le (Nat.min_le_left ..)
      rw [bSilent ⟨i.val,e⟩, val_num, Nat.cast_zero]) w hw
  · rw [← ev_W h cert, ← ev_dot h, bMoment ⟨j,by omega⟩, val_num, Nat.cast_zero]

noncomputable def lowChecks
    (units : ∀ j < 5, IsUnit (((j+1 : Nat) : K))) : DualSupport12.LowChecks (A z) (b z) where
  ghost := ghost
  fw := band z genF
  bw := band z genB
  weight_zero := by
    intro i hi
    simp [b, ev, cert.ghosts i hi]
  fw_zero := by
    intro d hd
    have e : width d = 0 := by unfold width; omega
    simp [band, e]
  fw_support := fun _ hd => f_supported cert hd
  bw_support := fun _ hd => b_supported cert hd
  bw_mono := fun d _ => band_mono genB d
  fw_A := by
    intro d hd
    apply span_by_linear (M:=mat (A z))
    intro j
    have e := ev_eq (z:=z) (cert.fA d hd j)
    rw [ev_A h] at e
    rw [e]
    exact combo_mem h genF d 0 j.val
  fw_C := by
    intro d hd
    apply span_by_linear (M:=diag (nodes (A z)))
    intro j
    have e := ev_eq (z:=z) (cert.fC d hd j)
    rw [ev_mulV h, ev_C h cert] at e
    change nodes (A z) * ev z (genF j.val) ∈ _
    rw [e]
    exact combo_mem h genF d 1 j.val
  fw_primitive := by
    intro d hd
    rw [← ev_F h cert, ev_eq (cert.fP d hd)]
    exact combo_mem h genF d 2 0
  bw_A := by
    intro d hd
    apply span_by_linear (M:=mat (A z).transpose)
    intro j
    have e := ev_eq (z:=z) (cert.bA d hd j)
    rw [ev_N h] at e
    rw [e]
    exact combo_mem h genB d 3 j.val
  bw_Y := by
    intro d hd
    apply span_by_linear (M:=diag (DualSupport12.reflected (A z)))
    intro j
    have e := ev_eq (z:=z) (cert.bY d hd j)
    rw [ev_mulV h, ev_Y h cert] at e
    change DualSupport12.reflected (A z) * ev z (genB j.val) ∈ _
    rw [e]
    exact combo_mem h genB d 4 j.val
  bw_primitive := by
    intro d hd
    rw [← ev_B h cert, ev_eq (cert.bP d hd)]
    exact combo_mem h genB d 5 0
  bw_scalar_zero := by
    intro d hd j hj w hw
    rw [row_apply, dotProduct_comm, ← row_apply, ← ev_X h cert]
    exact span_by_zero genB d (M:=row (ev z (powC j))) (fun i => by
      rw [ev_comm, ← ev_dot h, cert.bSilent d hd j hj i, val_num, Nat.cast_zero]) w hw
  bridge_A := by
    apply span_by_linear (M:=mat (A z))
    intro i
    have hi : i.val < 3 := i.isLt.trans_le (Nat.min_le_left ..)
    rw [← ev_A h]
    exact checked_high h cert _ (cert.fASilent ⟨i.val,hi⟩) (cert.fAMoment ⟨i.val,hi⟩)
  bridge_primitive := by
    rw [← ev_F h cert]
    exact checked_high h cert _ cert.fPSilent cert.fPMoment
  scalar := by
    intro j hj
    have e := congrArg (val z) (cert.scalar j hj)
    rw [val_mul h, val_num, ev_dot h, ev_X h cert, val_num, Nat.cast_one] at e
    exact e
  units := units

end

end RKResearch.Certified.DIRK12F17Cubic

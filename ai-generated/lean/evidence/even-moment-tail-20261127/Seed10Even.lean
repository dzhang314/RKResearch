module

public import Certificate10
import all Certificate10
public import RKCert.ReviewedNative.GramLocalPurity

@[expose] public section

namespace RKResearch.Certified.Seed10Even
open RootedTreeGram TwoDonorDense StrictSDIRKGram22Order10
open scoped Matrix

set_option maxHeartbeats 7000000
set_option maxRecDepth 16000

def donor (i : Fin 5) : Fin 22 := ⟨13+i.val, by have := i.isLt; omega⟩
def num (i : Fin 5) : ℤ := #[-3,-5,-7,-9,8915889][i.val]!
def den (i : Fin 5) : ℤ := #[1,1,1,1,8549164][i.val]!
def donorTime (i : Fin 5) : ℚ := (num i : ℚ)/(den i : ℚ)

theorem clocks_eq : TwoDonorDense.clocks A = StrictSDIRKGram22Order10.clocks := clocksEq

private theorem check2 {m n : ℕ} (f : Fin m → Fin n → Bool)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (f i)) = true) :
    ∀ i j, f i j = true := by
  intro i j
  exact List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)

theorem donor_clock (i : Fin 5) : TwoDonorDense.clocks A (donor i) = donorTime i := by
  rw [clocks_eq]
  exact of_decide_eq_true (List.all_eq_true.mp (show (List.finRange 5).all
    (fun j => decide (StrictSDIRKGram22Order10.clocks (donor j) = donorTime j)) = true by decide +kernel)
      i (List.mem_finRange i))

private theorem den_ne (i : Fin 5) : (den i : ℚ) ≠ 0 :=
  of_decide_eq_true (List.all_eq_true.mp (show (List.finRange 5).all
    (fun j => decide ((den j : ℚ) ≠ 0)) = true by decide +kernel) i (List.mem_finRange i))

private theorem sample_energies (i : Fin 5) (g : Fin 6) :
    energy (cov g.val) (localForm (donor i) (num i) (den i) g.val) = 0 :=
  of_decide_eq_true (check2 (fun (i : Fin 5) (g : Fin 6) =>
    decide (energy (cov g.val) (localForm (donor i) (num i) (den i) g.val) = 0)) (by decide +kernel) i g)

theorem donor_pure (i : Fin 5) : PureAt A (donor i) 6 :=
  trace.pureAt_of_local castA (by decide +kernel) (donor i) (num i) (den i)
    (den_ne i) (donor_clock i) (by decide) (fun g hg => sample_energies i ⟨g,hg⟩)

#print axioms donor_pure
end RKResearch.Certified.Seed10Even

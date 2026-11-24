module

public import RKCert.BackwardTerminal
public import RKCert.EndpointMoments
public import RKCert.ResidueTransfer

@[expose] public section

/-! # Uniform explicit Runge–Kutta stage bound over every nonzero commutative ring

The order hypothesis is the actual family of denominator-cleared rooted-tree
equations, not a profile or independence assumption. The parity correction is
proved at the last *active* output stage; zero and signed weights, repeated
nodes, and trailing unused stages are allowed. Fields in positive
characteristic are included wherever the order itself is possible.
-/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p : ℕ}

theorem terminal_single_not_mem {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {q : ℕ} (hp : 2*q+1≤p)
    (i : Fin (s+1)) (hb : b i ≠ 0) (hc : nodes A i = 1) :
    Pi.single i 1 ∉ treeSpace A q := by
  have hc0 : nodes A 0=0 := by
    unfold nodes
    exact Finset.sum_eq_zero fun j _ => ha 0 j (Nat.zero_le _)
  have hi0 : (0 : Fin (s+1)) ≠ i := by
    rintro rfl
    exact zero_ne_one (hc0.symm.trans hc)
  intro hz
  obtain ⟨a,ha'⟩ := exists_poly_zeroSpace ho (by omega) hz
  have hzero : (Pi.single i (1:K) : Vec K (s+1)) 0 - polyEval A q a 0 = 0 := origin_zeroSpace A ha q ha'
  have ha0 : a 0 = 0 := by
    simpa [polyEval_first ha, Pi.single_apply, hi0] using hzero
  have he (k : Fin (q+1)) : (∑ j : Fin q, a j.succ / ((k.val+j.val+2:ℕ):K)) = b i := by
    have hh : probe A b k.val (Pi.single i 1 - polyEval A q a) = 0 :=
      probe_zeroSpace ho (by omega) ha'
    have hsingle : probe A b k.val (Pi.single i 1) = b i := by
      simp [probe,row_apply,Pi.single_apply,hc]
    rw [map_sub,sub_eq_zero,hsingle,probe_polyEval ho (by omega),Fin.sum_univ_succ,
      ha0,zero_div,zero_add] at hh
    simpa only [Fin.val_succ, Nat.add_assoc] using hh.symm
  exact hb (constant_mixed_moments ho hp (fun j : Fin q => a j.succ) _ he).2

/-- When q+1 full monomial tests are available, either the first backward
residual pays the dimension or the last-active coordinate pays it. -/
theorem backward_endpoint_count {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (q n : ℕ)
    (hq : 2*q+1≤p) (hn : q+n+2≤p) :
    finrank K (treeSpace A q) + n + 1 ≤ s := by
  by_cases hd : backSeed1 A b = 0
  · cases s with
    | zero =>
      have hl := explicit_order_le_stages ha ho
      omega
    | succ s =>
      obtain ⟨i,hi,hfr⟩ := exists_last_weight ho (by omega)
      have hy := last_mirror_zero ha hi hfr hd
      have hc : nodes A i = 1 := (sub_eq_zero.mp hy).symm
      apply back_count_extra ha ho q n hn (Pi.single i 1)
        (terminal_single_not_mem ha ho hq i hi hc)
      intro w hw
      have hz := back_vanish ha hi hfr hd n hw i le_rfl
      simpa [row_apply,Pi.single_apply] using hz
  · have hrk : finrank K (back A b 0)=1 := finrank_span_singleton hd
    have h := backward_count ha ho q n hn
    omega

/-- Field-level numerical lower bound at arbitrary order, without a
characteristic-zero or ordering assumption. -/
theorem uniform_erk_field {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) :
    max p ((3*p+1)/2-2) ≤ s := by
  have hchain := explicit_order_le_stages ha ho
  refine max_le hchain ?_
  by_cases hsmall : p ≤ 4
  · omega
  let q := p/2
  have hq : 2≤q := by dsimp [q]; omega
  have hq1 : q-1+1=q := by omega
  have hf := zeroSpace_finrank ha ho (n:=q-1) (by dsimp [q]; omega)
  rw [hq1] at hf
  have he := explicit_treeSpace_rank ha ho (q:=q) (by dsimp [q]; omega) (by omega)
  by_cases ho' : p % 2 = 0
  · have h1 := backward_count ha ho q (q-2) (by dsimp [q]; omega)
    dsimp [q] at *
    omega
  · have h1 := backward_endpoint_count ha ho q (q-1) (by dsimp [q]; omega) (by dsimp [q]; omega)
    dsimp [q] at *
    omega

end RKCert.Paired

namespace RKCert

/-- Elementary uniform floor, in particular the certified ring column at
every p=1,...,20. There is no invertibility hypothesis on weights or nodes. -/
theorem uniform_erk_ring {R : Type*} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) :
    max p ((3*p+1)/2-2) ≤ s :=
  explicit_of_all_fields (fun _ _ _ _ hs ht => Paired.uniform_erk_field hs ht) ha ho

end RKCert

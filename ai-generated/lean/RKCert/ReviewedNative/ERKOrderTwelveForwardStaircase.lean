module

public import RKCert.ReviewedNative.ERKOrderTwelveAppendixA
public import RKCert.ReviewedNative.ClockBufferAdvance
public import RKCert.ReviewedNative.NativeHeadMultiplier

public section

/-! # The exact native order-twelve forward head staircase

The reviewed T7 decomposition, its next two measured reverse escapes,
and Appendix A pay three genuine clock extensions. Escape sites are
counted modulo the core, so no special representative is selected.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Module Polynomial Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

structure ForwardStaircase (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (r : ℕ) (U : Submodule K (Fin (s+1) → K)) (w : Fin (s+1) → K) : Prop where
  length : 2≤r
  initial : FlatClockHead A 5 1 r U w
  cut : escape7 A=chain (diag (nodes A)) U w (r+2)
  bands : ∀ k≤3, treeSpace A (7+k)=clockBand6 A ⊔ chain (diag (nodes A)) U w (r+2+k) ∧
    finrank K (treeSpace A (7+k))=14+k
  top : treeSpace A 10=⊤
  unpaid : (diag (nodes A)^(r+4)) w∉treeSpace A 9
  many : r+4 < (HeadFiber.escapeSites (nodes A) w U).card

private theorem buffered_tree_next (S : Saturation A b) {j n : ℕ}
    {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (jlo : 7≤j) (jhi : j≤9) (npos : 0<n) (stable : U.map (diag (nodes A))≤U)
    (shape : treeSpace A j=clockBand6 A ⊔ chain (diag (nodes A)) U w n)
    (dim : finrank K (treeSpace A j)=j+7)
    (esc : ¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j) :
    treeSpace A (j+1)=clockBand6 A ⊔ chain (diag (nodes A)) U w (n+1) ∧
      finrank K (treeSpace A (j+1))=(j+1)+7 := by
  have buffer : (clockBand6 A).map (diag (nodes A))≤treeSpace A j := by
    rintro _ ⟨v,⟨a,rfl⟩,rfl⟩
    exact treeSpace_mono A jlo (diag_treeSpace A 6 (coeffEval_mem_treeSpace A 6 a))
  have cap := S.caps (j+1) (by omega)
  have h := paid_buffered_clock_step (Y:=treeSpace A (j+1)) stable npos shape buffer
    (treeSpace_mono A (by omega : j≤j+1))
    (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)) esc (by omega)
  exact ⟨h.1,by omega⟩

section CharacteristicZero
variable [CharZero K]

/-- An order-12 tableau at the physical cap has one exact forward chart
from the original fifth defect grade through the whole stage space. -/
theorem forward_staircase (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 12)
    (S : Saturation A b) : ∃ r U w, ForwardStaircase A r U w := by
  let D := diag (nodes A)
  have T := terminal_band ha ho S
  have R := reverse_seven_nine ha ho S T
  obtain ⟨r,U,w,r2,H,cut,start⟩ := exists_order_twelve_head_at_seven ha ho S T
  have out (j : ℕ) (lo : 7≤j) (hi : j≤9) :
      ¬(treeSpace A j).map D≤treeSpace A j := by
    rcases (show j=7 ∨ j=8 ∨ j=9 by omega) with rfl|rfl|rfl
    · exact R.treeEscape7
    · exact R.treeEscape8
    · exact saturated_e9_escape ha ho S
  have bands (k : ℕ) (hk : k≤3) :
      treeSpace A (7+k)=clockBand6 A ⊔ chain D U w (r+2+k) ∧
        finrank K (treeSpace A (7+k))=14+k := by
    induction k with
    | zero => simpa only [Nat.add_zero] using And.intro start T.e7Rank
    | succ k ih =>
      obtain ⟨sh,dim⟩ := ih (by omega)
      have dim' : finrank K (treeSpace A (7+k))=(7+k)+7 := by omega
      obtain ⟨e,rank⟩ := buffered_tree_next S (j:=7+k) (n:=r+2+k)
        (by omega) (by omega) (by omega) H.coreStable sh dim' (out _ (by omega) (by omega))
      rw [show 7+(k+1)=7+k+1 by omega,show r+2+(k+1)=r+2+k+1 by omega]
      exact ⟨e,by omega⟩
  have e9 : treeSpace A 9=clockBand6 A ⊔ chain D U w (r+4) := by
    simpa only [Nat.reduceAdd,show r+2+2=r+4 by omega] using (bands 2 (by decide)).1
  have e10 : treeSpace A 10=clockBand6 A ⊔ chain D U w (r+5) := by
    simpa only [Nat.reduceAdd,show r+2+3=r+5 by omega] using (bands 3 (by decide)).1
  have base : chain D U w (r+4)≤treeSpace A 9 := by rw [e9]; exact le_sup_right
  have unpaid : (D^(r+4)) w∉treeSpace A 9 := by
    intro h
    have poly : clockBand6 A≤treeSpace A 9 := by rw [e9]; exact le_sup_left
    have next : chain D U w (r+5)≤treeSpace A 9 := by
      rw [show r+5=(r+4)+1 by omega,chain]
      exact sup_le base ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have inc : treeSpace A 10≤treeSpace A 9 := e10 ▸ sup_le poly next
    have rank := Submodule.finrank_mono inc
    have t : finrank K (treeSpace A 10)=17 := (bands 3 (by decide)).2
    rw [t,R.e9Rank] at rank
    omega
  have escape : ¬(chain D U w (r+4)).map D≤chain D U w (r+4) := by
    intro inv
    have p := ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) (r+4)).mp le_rfl).2 (r+3) (by omega)
    apply unpaid
    rw [show r+4=r+3+1 by omega,pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact base (inv (Submodule.mem_map_of_mem p))
  exact ⟨r,U,w,r2,H,cut,bands,saturated_e10_top ha ho S,unpaid,
    HeadFiber.more_escape_sites H.coreStable (by omega) escape⟩

end CharacteristicZero

/-- Every physical grade-two multiplier preserves the invariant core,
even before proving that the multiplier itself belongs to the core. -/
theorem grade_two_multiplier_stable (ho : HasOrder A b 12) (S : Saturation A b)
    (T : TerminalBand A b) {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (hv : v∈zeroSpace A 2) :
    U.map (diag v)≤U := by
  rintro _ ⟨u,hu,rfl⟩
  have mask := clock_mask_invariant
    (fun x (hx : x∈U) => H.initial.coreStable (Submodule.mem_map_of_mem hx))
  have slices (a : K) :
      blockMask (nodes A) a u*v∈chain (diag (nodes A)) U w (r+2) := by
    have m : blockMask (nodes A) a u∈zeroSpace A 5 := H.initial.coreInside (mask a _ hu)
    have x := zeroSpace_mul m hv
    have cut : blockMask (nodes A) a u*v∈zeroAt (zeroSpace A 7) (Fin.last s) := by
      apply mem_zeroAt.mpr
      exact ⟨x,by rw [Pi.mul_apply,grade_five_zero_at_terminal ho S m,zero_mul]⟩
    rwa [←T.cut,H.cut] at cut
  have many := H.many
  have product := HeadFiber.core_product_of_clock_slices H.initial.coreStable (by omega) slices
  have eq : diag v u=u*v := by ext i; simp [mul_comm]
  exact eq ▸ product

/-- Any grade-two vector outside the core has a nonzero polynomial
multiplier of degree at most two on the genuine head modulo the core. -/
theorem grade_two_multiplier_profile (ho : HasOrder A b 12) (S : Saturation A b)
    (T : TerminalBand A b) {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (hv : v∈zeroSpace A 2) (out : v∉U) :
    ∃ P : K[X], P≠0 ∧ P.natDegree≤2 ∧ v*w-weightedEval (nodes A) w P∈U := by
  let D := diag (nodes A)
  have first : zeroSpace A 5=chain D U w r := by
    simpa only [Nat.add_zero] using H.initial.flags 0 (by decide)
  have paid := ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp first.ge).2
  have band (k : ℕ) (hk : k<r) : v*((D^k) w)∈chain D U w (r+2) := by
    have p := paid k hk
    have t := grade_five_zero_at_terminal ho S p
    have cut : v*((D^k) w)∈zeroAt (zeroSpace A 7) (Fin.last s) :=
      mem_zeroAt.mpr ⟨zeroSpace_mul hv p,by rw [Pi.mul_apply,t,mul_zero]⟩
    rwa [←T.cut,H.cut] at cut
  have many := H.many
  obtain ⟨P,pnz,deg,fit⟩ := HeadFiber.multiplier_profile_of_chart H.initial.coreStable
    (grade_two_multiplier_stable ho S T H hv) (by omega) H.initial.positive band
    (first ▸ zeroSpace_mono A (by decide : 2≤5) hv) out
  exact ⟨P,pnz,by omega,fit⟩

end RKResearch.Certified.Graded.ERK12

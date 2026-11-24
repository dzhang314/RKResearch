module

public import RKCert.ReviewedNative.ClockHeadFibers

public section

/-! # A polynomial buffer on a paid one-head clock staircase -/
namespace RKResearch.Certified.Graded

open Module RKCert.OneEscape

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {D : V →ₗ[K] V} {P U X Y : Submodule K V} {w : V} {n : ℕ}

/-- A buffer whose clock image stays in the present subspace costs no new
direction. One merely appends the new power of the actual head. -/
theorem buffered_clock_sup (core : U.map D≤U) (pos : 0<n)
    (shape : X=P⊔chain D U w n) (buffer : P.map D≤X) :
    X⊔X.map D=P⊔chain D U w (n+1) := by
  let H := chain D U w n
  change X=P⊔H at shape
  rw [shape] at buffer
  rw [shape,Submodule.map_sup,←clock_chain_next core pos]
  change (P⊔H)⊔(P.map D⊔H.map D)=P⊔(H⊔H.map D)
  calc
    _ = ((P⊔H)⊔P.map D)⊔H.map D := by ac_rfl
    _ = _ := by rw [sup_eq_left.mpr buffer,sup_assoc]

/-- An actual clock escape and a unit rank cap make the buffered next
subspace exact. No tree structure, parity or mark premise is used. -/
theorem paid_buffered_clock_step [FiniteDimensional K V]
    (core : U.map D≤U) (pos : 0<n) (shape : X=P⊔chain D U w n)
    (buffer : P.map D≤X) (mono : X≤Y) (image : X.map D≤Y)
    (escape : ¬X.map D≤X) (cap : finrank K Y≤finrank K X+1) :
    Y=P⊔chain D U w (n+1) ∧ finrank K Y=finrank K X+1 := by
  let Z := X⊔X.map D
  have inc : Z≤Y := sup_le mono image
  have lt : X<Z := lt_of_le_of_ne le_sup_left
    (fun eq => escape (le_sup_right.trans eq.ge))
  have lo := Submodule.finrank_lt_finrank_of_lt lt
  have hi := Submodule.finrank_mono inc
  have eq : Z=Y := Submodule.eq_of_le_of_finrank_le inc (by omega)
  exact ⟨eq.symm.trans (buffered_clock_sup core pos shape buffer),by omega⟩

end RKResearch.Certified.Graded

namespace RKResearch.Certified.Graded.HeadFiber
open RKCert.Endpoint RKCert.OneEscape

variable {K : Type*} [Field K] {s n : ℕ} {c u v w : Fin s → K}
variable {U : Submodule K (Fin s → K)}

/-- When each physical clock slice of a product lies in a paid head
chart, the whole product is already in its invariant core. Applicable
even when the entire target defect space is larger than the chart. -/
theorem core_product_of_clock_slices (stable : U.map (diag c)≤U)
    (many : n<(escapeSites c w U).card)
    (each : ∀ a, blockMask c a u*v∈chain (diag c) U w n) :
    u*v∈U := by
  let g (a : K) := blockMask c a u*v
  have slicesIn (a : K) : g a∈U := by
    apply localized_mem stable many (each a) (z:=a)
    intro i h
    simp [blockMask,h]
  have mask := clock_mask_invariant (fun x (hx : x∈U) => stable (Submodule.mem_map_of_mem hx))
  have eq : assembleBlocks c g=u*v := by ext i; simp [g,blockMask]
  exact eq ▸ assembleBlocks_mem c mask g slicesIn

end RKResearch.Certified.Graded.HeadFiber

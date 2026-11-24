module

public import RKCert.ReviewedNative.ERKHeadContrast

public section

/-! # An actual doubling head cannot stay flat

The chart is expressed in the genuine reviewed defect spaces. One extra
clock escape at its top makes single-clock pieces exact, so the core is
closed under multiplication and the head can be made physically
disjoint. Squaring all paid powers then forces the short polynomial
excluded by the chronological two-knot argument.
-/
namespace RKResearch.Certified.Graded

open RKResearch Polynomial Module RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The real doubling-band obstruction with the rank extraction factored
out. No clock ordering, node distinctness, normalization, or condition
on b occurs. -/
theorem no_explicit_doubling_head (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder p A b)
    {j r : ℕ} (j5 : 5≤j) (pay : j+j+1≤p) (sep : PolySeparated A (j+j)) (r2 : 2≤r)
    {U : Submodule K (Fin s → K)} {w : Fin s → K} (stable : U.map (diag (nodes A)) ≤ U)
    (core : U ≤ zeroSpace A j) (first : zeroSpace A j = chain (diag (nodes A)) U w r)
    (last : zeroSpace A (j+j) = chain (diag (nodes A)) U w (r+j))
    (escape : ¬ (zeroSpace A (j+j)).map (diag (nodes A)) ≤ zeroSpace A (j+j)) : False := by
  classical
  let D := diag (nodes A)
  have many : r+j < (HeadFiber.escapeSites (nodes A) w U).card := by
    apply HeadFiber.more_escape_sites stable (by omega)
    simpa only [←last] using escape
  have mult (u) (hu : u∈U) (t) (ht : t∈zeroSpace A j) : u*t∈U :=
    HeadFiber.core_mul stable core many last.le hu ht
  have wIn : w∈zeroSpace A j := by
    have h := ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp first.ge).2 0 (by omega)
    simpa using h
  obtain ⟨v,off,shift⟩ := HeadFiber.disjoint_rep stable
    (fun u hu t ht => mult u hu t (core ht)) (fun u hu => mult u hu w wIn)
  have firstV := first.trans (shift r).symm
  have lastV := last.trans (shift (r+j)).symm
  have escV : r+j < (HeadFiber.escapeSites (nodes A) v U).card := by
    apply HeadFiber.more_escape_sites stable (by omega)
    simpa only [←lastV] using escape
  have knots : r+j < (HeadFiber.physicalSites (nodes A) v).card :=
    escV.trans_le (Finset.card_le_card HeadFiber.escape_le_physical)
  have paid := ((clock_chain_le_iff (T:=D) (U:=U) (w:=v) r).mp firstV.ge).2
  have vIn : v∈zeroSpace A j := by simpa using paid 0 (by omega)
  have live : ∃ i, v i≠0 := by
    by_contra! zero
    have empty : HeadFiber.physicalSites (nodes A) v=∅ := by simp [HeadFiber.physicalSites,zero]
    rw [empty,Finset.card_empty] at knots
    omega
  have band (k : ℕ) (hk : k≤(r-1)+(r-1)) : (D^k) (v*v)∈chain D U v (r+j) := by
    let a := min k (r-1)
    let c := k-a
    have ha' : a<r := by dsimp [a]; omega
    have hc' : c<r := by dsimp [a,c]; omega
    have eq : a+c=k := by dsimp [a,c]; omega
    have e : (D^k) (v*v)=(D^a) v * (D^c) v := by
      ext i
      simp only [D,HeadFiber.clock_power_value,Pi.mul_apply]
      rw [←eq,pow_add]
      ring
    rw [e,←lastV]
    exact zeroSpace_mul (paid _ ha') (paid _ hc')
  obtain ⟨P,hdeg,values⟩ := HeadFiber.multiplier_polynomial (a:=v) off knots band
  have hP : P≠0 := by
    obtain ⟨i,nz⟩ := live
    rintro rfl
    exact nz (by simpa using values i nz)
  have d := hdeg.resolve_left hP
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have eq : 2*(m+1)=(m+1)+(m+1) := by omega
  refine HeadContrast.no_disjoint_polynomial_head_doubling ha ho (m:=m) (by omega) (by omega)
    (eq.symm ▸ sep) U core (fun _ h => stable (Submodule.mem_map_of_mem h))
    v vIn (eq.symm ▸ lastV.le) ?_ P hP (by omega) values
  intro u hu i vi
  by_contra nz
  exact vi (off i ⟨u,hu,nz⟩)

end RKResearch.Certified.Graded

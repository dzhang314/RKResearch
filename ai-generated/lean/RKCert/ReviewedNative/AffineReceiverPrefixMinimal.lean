module

public import RKCert.ReviewedNative.AffineReceiverPrefix
public import RKCert.ReviewedNative.ERKUniform
public import RKCert.OneEscape
import RKCert.ReviewedNative.MinimalDefectTwoSeedTail
import RKCert.ReviewedNative.MinimalDefectClean
import RKCert.ReviewedNative.QuadraticClockEscape

@[expose] public section

/-! # Typed minimal-midpoint client of the affine prefix theorem

No paid endpoint is imported. A normalized same-clock row annihilates
the entire paid minimal flag exactly when it kills the two actual seeds.
-/
namespace RKResearch.Certified.Graded

open RKResearch Module RKCert.OneEscape
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {l : Fin s→K}
variable {x : K} {cut : Fin s}

theorem ClockAffineProbe.kills_clock_chain (P : ClockAffineProbe A l x cut)
    {U : Submodule K (Fin s→K)} {w : Fin s→K} {n : ℕ}
    (base : U≤(row l).ker) (head : row l w=0) :
    chain (diag (nodes A)) U w n≤(row l).ker := by
  have zeros (k : ℕ) : row l (((diag (nodes A))^k) w)=0 := by
    induction k with
    | zero => simpa only [pow_zero,one_apply_eq_self] using head
    | succ k ih =>
      rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply,P.diag_pairing,ih,mul_zero]
  exact (clock_chain_le_iff n).mpr ⟨base,fun k _=>zeros k⟩

section Minimal
variable [CharZero K] {p q : ℕ} {b : Fin s→K}

/-- The fibre version of the actual two-seed clean criterion. The proof
uses the two checked shapes, not the pointwise criterion alone. -/
theorem ClockAffineProbe.kills_minimal_defects_iff (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    {j : ℕ} (j₃ : 3≤j) (jq : j≤q) :
    zeroSpace A j≤(row l).ker ↔
      row l (monomialStageDefect A 1)=0 ∧ row l (mat A (monomialStageDefect A 1))=0 := by
  classical
  constructor
  · intro clean
    have g₂ := monomialStageDefect_mem A 1
    have paidThree : 2+1≤p := by omega
    have h₃ : mat A (monomialStageDefect A 1)∈zeroSpace A 3 :=
      mat_zeroSpace ho 2 paidThree g₂
    exact ⟨clean (zeroSpace_mono A (by omega : 2≤j) g₂),
      clean (zeroSpace_mono A j₃ h₃)⟩
  · rintro ⟨gz,hz⟩
    by_cases unequal : ∃ r t : Fin s, monomialStageDefect A 1 r≠0 ∧
        monomialStageDefect A 1 t≠0 ∧ nodes A r≠nodes A t
    · obtain ⟨r,t,hr,ht,diff⟩ := unequal
      have base := minimal_defect_baseF3_of_two_quadratic_live_clocks strict ho pay minimal
        hr ht diff
      rw [minimal_defect_clock_chain (j:=j) strict ho pay minimal base (by omega) jq]
      exact P.kills_clock_chain bot_le gz
    · have oneClock : ∃ a : K, ∀ k, monomialStageDefect A 1 k≠0 → nodes A k=a := by
        by_cases live : ∃ r : Fin s, monomialStageDefect A 1 r≠0
        · obtain ⟨r,hr⟩ := live
          refine ⟨nodes A r,fun k hk=>?_⟩
          by_contra different
          exact unequal ⟨k,r,hk,hr,different⟩
        · exact ⟨0,fun k hk=>(live ⟨k,hk⟩).elim⟩
      obtain ⟨a,single⟩ := oneClock
      have line : (K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K))≤(row l).ker := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact gz
      rw [minimal_defect_clock_tail_of_single_quadratic_live_clock strict ho pay minimal
        a single j₃ jq]
      exact P.kills_clock_chain line hz

theorem ClockAffineProbe.prefix_hasOrder_of_seed_zeros (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (ho : HasOrder p A b)
    (q₃ : 3≤q) (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (nz : x≠0) (gz : row l (monomialStageDefect A 1)=0)
    (hz : row l (mat A (monomialStageDefect A 1))=0) :
    HasOrder q (x⁻¹ • prefixMatrix A cut.isLt.le)
      (fun j : Fin cut.val=>x⁻¹*affineReceiverRow A l (Fin.castLE cut.isLt.le j)) := by
  have clean := (P.kills_minimal_defects_iff strict ho pay minimal q₃ le_rfl).mpr ⟨gz,hz⟩
  exact P.prefix_hasOrder strict nz q (fun v hv=>clean hv)

theorem ClockAffineProbe.prefix_floor_of_seed_zeros (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (ho : HasOrder p A b)
    (q₃ : 3≤q) (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (nz : x≠0) (gz : row l (monomialStageDefect A 1)=0)
    (hz : row l (mat A (monomialStageDefect A 1))=0) :
    erkUniformFloor q≤cut.val := by
  have pref := P.prefix_hasOrder_of_seed_zeros strict ho q₃ pay minimal nz gz hz
  apply pref.erk_uniform_floor_le_stages
  intro i j ij
  change x⁻¹*(prefixMatrix A cut.isLt.le) i j=0
  rw [prefix_strict_lower strict cut.isLt.le i j ij,mul_zero]

end Minimal
end
end RKResearch.Certified.Graded

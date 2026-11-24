module

public import RKCert.ReviewedNative.ERK17TinyHiddenRank
public import RKCert.ReviewedNative.LocalLinearSevenRefund

@[expose] public section

/-! # The genuine rank-four, reverse-core-two refinement at width 26

The exact h=7 refund can be used through grade six only when r=1.
With r=2 it is used at grade five; the result is a paid F6 axis,
not a claim of F6 or full-midpoint invisibility. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

theorem reflected_invariant_of_ordinary {T : Submodule K (Fin s→K)}
    (stable : T.map (diag (nodes A))≤T) : T.map (diag (reflectedClock A))≤T := by
  rintro _ ⟨u,hu,rfl⟩
  have e : diag (reflectedClock A) u=u-diag (nodes A) u := by
    ext i
    simp only [diag_apply,Pi.sub_apply,reflectedClock,Pi.one_apply]
    ring
  rw [e]
  exact T.sub_mem hu (stable (Submodule.mem_map_of_mem hu))

/-- Genuine one-clock representative of a codimension-one quotient of a
clock invariant space, without choosing a dot-product complement. -/
theorem invariant_codim_one_clock_line {T J : Submodule K (Fin s→K)} {y : Fin s→K}
    (inc : J≤T) (stable : T.map (diag y)≤T) (dim : finrank K T=finrank K J+1) :
    ∃ a : K, ∃ ξ : Fin s→K, ξ∈T ∧ ξ∉J ∧
      T=J⊔K∙ξ ∧ ∀ i,y i≠a → ξ i=0 := by
  have out : ¬T≤J := by
    intro hit
    have d := Submodule.finrank_mono hit
    omega
  obtain ⟨v,hv,hout⟩ := Set.not_subset.mp out
  have proj := clock_mask_invariant (fun _ h=>stable (Submodule.mem_map_of_mem h))
  let S : Finset K := Finset.univ.image y
  have sum : (∑ a∈S,blockMask y a v)=v := by
    funext i
    rw [Finset.sum_apply,Finset.sum_eq_single_of_mem (y i) (Finset.mem_image_of_mem y (Finset.mem_univ i))]
    · simp [blockMask]
    · intro z _ ne; simp [blockMask,Ne.symm ne]
  have existsMask : ∃ a∈S,blockMask y a v∉J := by
    by_contra! h
    exact hout (sum ▸ J.sum_mem h)
  obtain ⟨a,_,bad⟩ := existsMask
  let ξ := blockMask y a v
  have inT : ξ∈T := proj a v hv
  have inS : K∙ξ≤T := (Submodule.span_singleton_le_iff_mem ..).mpr inT
  have eq : J⊔K∙ξ=T := by
    apply Submodule.eq_of_le_of_finrank_le (sup_le inc inS)
    rw [Submodule.finrank_sup_span_singleton bad,dim]
  exact ⟨a,ξ,inT,bad,eq.symm,fun i other=>by simp [ξ,blockMask,other]⟩

end
end RKResearch.Certified.Graded.Reverse.LocalLinear

namespace RKResearch.Certified.ERK17
open RKResearch Module Graded Graded.Reverse Graded.Reverse.LocalLinear RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26→K}
variable {r : ℕ} {U : Submodule K (Fin 26→K)}

set_option maxRecDepth 3500
set_option maxHeartbeats 1300000

/-- Maximal clock core inside the actual midpoint, not the necessarily
smaller product-closed hidden kernel. -/
theorem width26_largest_midpoint_core :
    ∃ T : Submodule K (Fin 26→K), T≤zeroSpace A 8 ∧ T.map (diag (nodes A))≤T ∧
      ∀ W : Submodule K (Fin 26→K), W≤zeroSpace A 8 → W.map (diag (nodes A))≤W → W≤T := by
  let C := diag (nodes A)
  obtain ⟨n,_,plateau⟩ := exists_plateau C (zeroSpace A 8)
  refine ⟨core C (zeroSpace A 8) n,?_,invariant_of_plateau plateau,fun W hw hi=>invariant_le_core hw hi n⟩
  intro x hx
  simpa only [pow_zero,one_apply_eq_self] using mem_core.mp hx 0 (Nat.zero_le _)

/-- What the actual four-dimensional hidden kernel earns in the small
order-17 reverse branch. In particular this does not rule out r=2. -/
theorem width26_tiny_rank_four_refinement
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8))
    (four : finrank K (hiddenKernel b τ U)=4) :
    r=2 ∧ hiddenKernel b τ U≤zeroSpace A 5 ∧ finrank K (zeroSpace A 6)=7 := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  let G := zeroSpace A
  change finrank K J=4 at four
  have jr : r≤7 := by rcases F.coreRank with e|e <;> omega
  have j8 : J≤G 8 := hiddenKernel_le_paid_defect ho F jr full (by decide)
  have jc : J.map C≤J := hiddenKernel_forward_clock_of_band F
  have S := (ordered_width26_full_frame ha ho).1
  have sep := PolySeparated.of_coeff S.separated
  have f8 : finrank K (G 8)=9 := S.middleDefects
  have f9 : finrank K (zeroSpace A 9)≤11 := by rw [(width26_nonzero_forward_nine ha ho nz).2]; decide
  obtain ⟨T,t8,tc,maximal⟩ := width26_largest_midpoint_core (A:=A)
  have ht : finrank K T≤5 := invariant_core_cap_of_rank (q:=8) ha (by decide)
    S.separated S.middleDefects f9 T t8 tc
  have jt : J≤T := maximal _ j8 jc
  have jtR := Submodule.finrank_mono jt
  have mono : Monotone G := fun _ _ bc=>zeroSpace_mono A bc
  have rise (n : ℕ) : (G n).map C≤G (n+1) := Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A n)
  have f5 : 5≤finrank K (G 5) := grade_five_surplus ha (sep.mono (by decide : 5≤8))
  have f6 : finrank K (G 6)≤7 := by
    have e := zeroSpace_rank_interval_of_separation ha S.separated (j:=6) (d:=2) (by decide) (by decide)
    change finrank K (G 6)+2≤finrank K (G 8) at e
    omega
  have out5 : ¬G 5≤T := by
    intro le
    have d : finrank K T≤finrank K (G 5) := by omega
    have eq : G 5=T := Submodule.eq_of_le_of_finrank_le le d
    have e := clock_invariant_outgoing ha (sep.mono (by decide : 5≤8)) eq.ge tc
    change finrank K T+3≤finrank K (G 6) at e
    have k := Submodule.finrank_mono le
    omega
  let W (j : ℕ) := G j⊔T
  have cap (j : ℕ) (lo : 5≤j) (hi : j≤8) : finrank K (W j)≤j+1 := by
    have d := terminal_quotient_growth C G mono rise t8 tc maximal hi
      (fun e=>out5 ((mono lo).trans e))
    change finrank K (W j)+(8-j)≤finrank K (G 8) at d
    omega
  have step (j : ℕ) : W j⊔(W j).map C≤W (j+1) := by
    refine sup_le (sup_le_sup_right (mono (Nat.le_succ _)) T) ?_
    change ((G j⊔T).map C)≤G (j+1)⊔T
    rw [Submodule.map_sup]
    exact sup_le ((rise j).trans le_sup_left) (tc.trans le_sup_right)
  have cost (j5 : J≤G 5) : 7≤finrank K (G 6) := by
    have e := clock_invariant_outgoing ha (sep.mono (by decide : 5≤8)) j5 jc
    change finrank K J+3≤finrank K (G 6) at e
    omega
  by_cases t5 : finrank K T=5
  · obtain ⟨a,ξ,inT,_,split,off⟩ := invariant_codim_one_clock_line jt
      (reflected_invariant_of_ordinary tc) (by omega : finrank K T=finrank K J+1)
    have locate (x : Fin 26→K) (hx : x∈T) (i : Fin 26) (ne : reflectedClock A i≠a) : τ i*x i=0 := by
      rw [split] at hx
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨z,rfl⟩ := Submodule.mem_span_singleton.mp hw
      have kill : τ i*u i=0 := congrFun (mem_hiddenKernel.mp hu).1 i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,off i ne,mul_zero,add_zero,kill]
    have narrow (n : ℕ) (pay : n+r≤7) : G n⊓T≤J :=
      fun _ hx=>hiddenKernel_of_one_paid_head_clock ho F full (by decide) pay hx.1 a (locate _ hx.2)
    have budget : 5+r≤7 := by rcases F.coreRank with e|e <;> omega
    have d := Submodule.finrank_sup_add_finrank_inf_eq (G 5) T
    have room := cap 5 (by decide) (by decide)
    change finrank K (W 5)+finrank K (G 5⊓T : Submodule K (Fin 26→K))=finrank K (G 5)+finrank K T at d
    have meet : G 5⊓T=J := Submodule.eq_of_le_of_finrank_le (narrow 5 budget) (by omega)
    have j5 : J≤G 5 := meet.symm.le.trans inf_le_left
    have up := cap 6 (by decide) (by decide)
    have lo := cost j5
    have six : G 6=W 6 := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have t6 : T≤G 6 := le_sup_right.trans six.ge
    have two : r=2 := by
      rcases F.coreRank with e|e
      · have sub := (le_inf t6 le_rfl).trans (narrow 6 (by omega))
        have d := Submodule.finrank_mono sub
        omega
      · exact e
    exact ⟨two,j5,by change finrank K (G 6) = 7; omega⟩
  have equal : T=J := (Submodule.eq_of_le_of_finrank_le jt (by omega)).symm
  have bad (j : ℕ) (lo : 5≤j) (jp : j+r≤7) (eq : finrank K (W j)=j+1) : False := by
    have rpos : 1≤r := by rcases F.coreRank with e|e <;> omega
    have u := Submodule.finrank_mono (step j)
    have cap1 := cap (j+1) (by omega) (by omega)
    have unit : finrank K (W j⊔(W j).map C : Submodule K (Fin 26→K))≤finrank K (W j)+1 := by omega
    have floor (l : ℕ) : finrank K (W j)≤finrank K (core C (W j) l)+l := by
      induction l with
      | zero => rw [core_zero,add_zero]
      | succ l ih =>
        have e := core_rank_step C (W j) l
        omega
    let l := j-4
    have cover : core C (W j) l≤J := by
      change core C (G j⊔T) l≤J
      rw [equal]
      exact paid_core_le_hidden_at_seven ha ho F full (by decide) jp (by dsimp [l];omega)
    have d := Submodule.finrank_mono cover
    have e := floor l
    change finrank K (core C (W j) (j-4)) ≤ finrank K J at d
    change finrank K (W j) ≤ finrank K (core C (W j) (j-4)) + (j-4) at e
    omega
  have wf5 : finrank K (G 5)≤finrank K (W 5) := Submodule.finrank_mono le_sup_left
  have room := cap 5 (by decide) (by decide)
  have j5pay : 5+r≤7 := by rcases F.coreRank with e|e <;> omega
  have n6 : finrank K (W 5)≠6 := fun e=>bad 5 (by decide) j5pay e
  have q5 : G 5=W 5 := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  have j5 : J≤G 5 := jt.trans (le_sup_right.trans q5.ge)
  have lo := cost j5
  have two : r=2 := by
    rcases F.coreRank with e|e
    · have u := cap 6 (by decide) (by decide)
      have v : finrank K (G 6)≤finrank K (W 6) := Submodule.finrank_mono le_sup_left
      exact False.elim (bad 6 (by decide) (by omega) (by omega))
    · exact e
  exact ⟨two,j5,by change finrank K (G 6) = 7; omega⟩

end
end RKResearch.Certified.ERK17

module
public import RKCert.CodimensionOneStateRank

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial Module RKCert.Paired RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K]

/-- When only one ambient dimension is left at a paid grade, the first
backward gain already forces D(1), the terminal clock, and the physical
terminal coordinate. Unlike a state-contrast argument, no pair of duplicate
rows needs to be selected or merged. -/
theorem one_slot_terminal {s p j:ℕ} {A : Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (pay:j+3≤p)
    (cap:s+1≤finrank K (treeSpace A j)+1) (hb:b (Fin.last s)≠0) :
    backSeed1 A b=0 ∧ nodes A (Fin.last s)=1 ∧ Pi.single (Fin.last s) 1∈treeSpace A j ∧
      back A b 1=annih (treeSpace A j) := by
  have count:=backward_count ha ho j 1 (by omega)
  have h0 : backSeed1 A b=0 := by
    by_contra h
    have hr : finrank K (back A b 0)=1 := finrank_span_singleton h
    omega
  have d:=finrank_add_annih_eq (treeSpace A j)
  have g:=back_finrank ha ho 1 (by omega)
  have e : back A b 1=annih (treeSpace A j) :=
    Submodule.eq_of_le_of_finrank_le (back_annih ho j 1 (by omega)) (by omega)
  have sup (i:Fin (s+1)) (h : Fin.last s < i) : b i=0 := by
    have hi := i.isLt
    change s < i.val at h
    omega
  have hc : nodes A (Fin.last s)=1 := (sub_eq_zero.mp (last_mirror_zero ha hb sup h0)).symm
  refine ⟨h0,hc,?_,e⟩
  apply row_annih_test
  intro v hv
  rw [←e] at hv
  have vanish := back_vanish ha hb sup h0 1 hv (Fin.last s) le_rfl
  simpa [row_apply,Pi.single_apply] using vanish

variable [CharZero K]
/-- No strict twelve-stage order-nine tableau has exactly six off-defect
abscissas AND five on-defect abscissas. Arbitrary characteristic-zero field;
zero weights and repeated physical rows are allowed. -/
theorem order9_no_six_off_five_on {A : Fin 12→Fin 12→K} {b:Vec K 12}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 9) (N:(supportedNodes A (qdef A)).card=6) :
    (onNodes A).card≠5 := by
  intro M
  obtain ⟨hb,h3,h4,_,_,_,_,upper⟩:=order9_twelve_stage_chart ha ho
  obtain ⟨P,dP,_,_,hF,fit⟩:=two_curve_head h3 h4 (by omega)
  have hoff : ∀x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx=>offWeight_eq_zero_from_head ho P fit (by omega) x hx
  have nd:=order9_five_on_head_not_dvd (s:=11) ha ho M hoff hF P dP fit
  have leS:=five_on_state_le (q:=4) (by decide) M N P dP fit nd
  have eqS : onOffSpace A=treeSpace A 6 :=
    Submodule.eq_of_le_of_finrank_le leS (by rw [onOffSpace_rank,M,N]; exact upper)
  have dr : finrank K (treeSpace A 6)=11 := by rw [←eqS,onOffSpace_rank,M,N]
  obtain ⟨_,hc,card,_⟩:=one_slot_terminal (s:=11) (j:=6) (A:=A) ha ho (by decide) (by rw [dr]) hb
  have clean:=on_of_state_single (eqS.symm ▸ card) hb hoff
  exact one_not_on_of_five (s:=11) ha ho M hoff (mem_onNodes.mpr ⟨Fin.last 11,clean,hc⟩)

/-- The numeric census for the remaining six-off-node case. -/
theorem order9_six_off_forces_six_on {A : Fin 12→Fin 12→K} {b:Vec K 12}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 9) (N:(supportedNodes A (qdef A)).card=6) :
    (onNodes A).card=6 := by
  obtain ⟨_,h3,h4,_,_,_,_,_⟩:=order9_twelve_stage_chart ha ho
  obtain ⟨P,_,_,_,_,fit⟩:=two_curve_head h3 h4 (by omega)
  have hoff : ∀x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx=>offWeight_eq_zero_from_head ho P fit (by omega) x hx
  have lower:=five_on_of_aggregate_zero (s:=11) ha ho (by decide) hoff
  have cap:=on_off_card_le A
  have not5:=order9_no_six_off_five_on ha ho N
  omega

end RKCert.FixedFactor

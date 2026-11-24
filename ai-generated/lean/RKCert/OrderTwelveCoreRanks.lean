module
public import RKCert.OrderTwelveLeakage
public import RKCert.OrderTwelveCoreRows

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {i:Fin (s+1)}
variable {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

omit [CharZero K] in
theorem head_succ_rank_cap (h n:ℕ) :
    finrank K (chain (diag (nodes A)) U w (n+h))≤finrank K (chain (diag (nodes A)) U w n)+h := by
  induction h with
  | zero => simp only [Nat.add_zero,le_refl]
  | succ h ih =>
    let z := (diag (nodes A)^(n+h)) w
    have hz : finrank K (Submodule.span K {z})≤1 :=
      (finrank_span_le_card ({z}:Set (Vec K (s+1)))).trans (by simp)
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (chain (diag (nodes A)) U w (n+h)) (Submodule.span K {z})
    change finrank K (chain (diag (nodes A)) U w (n+h+1))+
      finrank K ↥(chain (diag (nodes A)) U w (n+h) ⊓ Submodule.span K {z}) =
      finrank K (chain (diag (nodes A)) U w (n+h))+finrank K (Submodule.span K {z}) at hs
    rw [show n+(h+1)=n+h+1 by rfl]
    omega

omit [CharZero K] in
theorem rank_core_exact (hs:Saturation A b) (hh:HeadData A r U w)
    (d:ℕ) (hd:d≤r) :
    core (diag (nodes A)) (zeroSpace A 5) d=chain (diag (nodes A)) U w (r-d) := by
  let C := diag (nodes A)
  let F := zeroSpace A 5
  have steps : F ⊔ F.map C=zeroSpace A 6 := by
    change zeroSpace A 5 ⊔ (zeroSpace A 5).map C=zeroSpace A 6
    rw [hh.f5,hh.f6,chain_sup_map hh.inv (by have := hh.pos;omega)]
  have cost : finrank K ↥(F ⊔ F.map C)≤finrank K F+1 := by
    rw [steps];change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1;rw [hs.f6,hs.f5]
  have paid : ∀ k<r,(C^k) w∈F := by
    intro k hk
    change ((diag (nodes A))^k) w ∈zeroSpace A 5
    rw [hh.f5]
    exact ((chain_le_iff r).mp le_rfl).2 k hk
  have out : (C^r) w∉F := by
    intro H
    have h6F : zeroSpace A 6≤F := by
      rw [hh.f6]
      change chain C U w (r+1)≤F
      rw [chain]
      apply sup_le
      · exact le_of_eq hh.f5.symm
      · exact (Submodule.span_singleton_le_iff_mem ..).mpr H
    have hr:=Submodule.finrank_mono h6F
    change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5) at hr
    rw [hs.f5,hs.f6] at hr
    omega
  have step (k:ℕ) (hk:k<r) : core C F k≠core C F (k+1) := by
    intro e
    have l : (C^(r-1-k)) w∈core C F k := by
      apply mem_core.mpr
      intro j hj
      rw [← mul_apply_eq_comp,←pow_add]
      exact paid _ (by omega)
    have hx := mem_core.mp (e ▸ l) (k+1) le_rfl
    rw [← mul_apply_eq_comp,←pow_add,show k+1+(r-1-k)=r by omega] at hx
    exact out hx
  have rd (k:ℕ) (hk:k≤r) : finrank K (core C F k)+k=5 := by
    induction k with
    | zero =>
      change finrank K (zeroSpace A 5)+0=5
      rw [Nat.add_zero];exact hs.f5
    | succ k ih =>
      have h := ih (by omega)
      have he := unit_loss cost k (step k (by omega))
      omega
  have H : chain C U w (r-d)≤core C F d := by
    apply (chain_le_iff _).mpr
    refine ⟨invariant_le_core hh.low hh.inv d,fun k hk => ?_⟩
    apply mem_core.mpr
    intro j hj
    rw [← mul_apply_eq_comp,←pow_add]
    exact paid _ (by omega)
  have lower := head_succ_rank_cap (A:=A) (U:=U) (w:=w) d (r-d)
  change finrank K (chain C U w (r-d+d))≤finrank K (chain C U w (r-d))+d at lower
  rw [show r-d+d=r by omega,←hh.f5,hs.f5] at lower
  exact (Submodule.eq_of_le_of_finrank_le H (by have := rd d hd;omega)).symm

omit [CharZero K] in
theorem four_grade_exact (hs:Saturation A b) (hh:HeadData A r U w)
    (h4:finrank K (zeroSpace A 4)=4) :
    zeroSpace A 4=chain (diag (nodes A)) U w (r-1) := by
  have pos:=hh.pos
  have hh1 : zeroSpace A 4≤core (diag (nodes A)) (zeroSpace A 5) 1 := by
    intro v hv
    apply mem_core.mpr
    intro k hk
    interval_cases k
    · simpa only [pow_zero,one_apply_eq_self] using zeroSpace_mono A (by decide : 4≤5) hv
    · rw [pow_one];exact diag_zeroSpace A 4 hv
  rw [rank_core_exact hs hh 1 (by omega)] at hh1
  apply Submodule.eq_of_le_of_finrank_le hh1
  have hc:=chain_rank_cap (A:=A) (U:=U) (w:=w) (r-1)
  have hR:=hh.rank
  omega

omit [CharZero K] in
theorem f3_into_core_two (hs:Saturation A b) (hh:HeadData A 2 U w) :
    zeroSpace A 3≤U := by
  have hl : zeroSpace A 3≤core (diag (nodes A)) (zeroSpace A 5) 2 := by
    intro v hv
    apply mem_core.mpr
    intro k hk
    interval_cases k
    · simpa only [pow_zero,one_apply_eq_self] using zeroSpace_mono A (by decide : 3≤5) hv
    · simpa only [pow_one] using zeroSpace_mono A (by decide : 4≤5) (diag_zeroSpace A 3 hv)
    · rw [pow_two,mul_apply_eq_comp];exact diag_zeroSpace A 4 (diag_zeroSpace A 3 hv)
  rw [rank_core_exact hs hh 2 (by decide)] at hl
  exact hl

theorem four_grade_three_two (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hh:HeadData A 2 U w)
    (h4:finrank K (zeroSpace A 4)=3) : zeroSpace A 4=U := by
  have hsep := explicit_separated ha ho (q:=6) (by decide) (by omega)
  have h34:=Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha hsep
    (j:=3) (by decide) (by decide))
  have h3 := zeroSpace_finrank ha ho (n:=2) (by decide)
  change 2≤finrank K (zeroSpace A 3) at h3
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at h34
  have h3' : finrank K (zeroSpace A 3)=2 := by omega
  have hnv : ¬(zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3 := by
    intro h
    have H := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=3) (by decide) (zeroSpace A 3)
      le_rfl (fun _ hv=>h (Submodule.mem_map_of_mem hv))
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at H
    omega
  have leU := f3_into_core_two hs hh
  apply Submodule.eq_of_le_of_finrank_le ?_ (by have h := hh.rank;omega)
  rw [ordinary_step (by omega : finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1) hnv]
  exact sup_le leU ((Submodule.map_mono leU).trans hh.inv)

theorem core_grade8_multiplier (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    (hh:HeadData A r U w)
    (h8:treeSpace A 8=pBand A ⊔ chain (diag (nodes A)) U w (r+3))
    (h9:treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U w (r+4))
    (h9r:finrank K (treeSpace A 9)=16)
    (hn:r+3<(headSites (nodes A) w).card)
    {j k:ℕ} (hj:U≤zeroSpace A j) (hb:j+k≤8)
    {u v:Vec K (s+1)} (hu:u∈U) (hv:v∈zeroSpace A k) : u*v∈U := by
  classical
  have eqn : u*v=∑ z ∈ sites (nodes A), fiber (nodes A) z u*v := by rw [←Finset.sum_mul,sum_fibers]
  rw [eqn]
  apply U.sum_mem
  intro z _
  have hfib := fiber_mem hh.inv z hu
  have hv7:=f5_vanish_at_last_active ha ho hs hi hl (hh.low hfib)
  have hfv: fiber (nodes A) z u*v∈endZero A 8 i :=
    ⟨zeroSpace_mono A hb (zeroSpace_mul (hj hfib) hv),by change _ * v i=0;rw [hv7,zero_mul]⟩
  have hz : diag (nodes A) (fiber (nodes A) z u*v) =
        (diag (nodes A) (fiber (nodes A) z u))*v := by ext l;simp [mul_assoc]
  have hY : diag (nodes A) (fiber (nodes A) z u)∈U := hh.inv (Submodule.mem_map_of_mem hfib)
  have hfvY : diag (nodes A) (fiber (nodes A) z u*v)∈endZero A 8 i := by
    rw [hz]
    refine ⟨zeroSpace_mono A hb (zeroSpace_mul (hj hY) hv),?_⟩
    have e := f5_vanish_at_last_active ha ho hs hi hl (hh.low hY)
    change diag (nodes A) (fiber (nodes A) z u) i * v i=0
    rw [e,zero_mul]
  have hB := no_double_leak ha ho hs hi hl hh h8 h9 h9r hfv hfvY
  apply localized_mem (z:=z) hh.inv hh.normalized hn hB
  intro l he
  simp [fiber,he]

end RKCert.Paired.OrderTwelve


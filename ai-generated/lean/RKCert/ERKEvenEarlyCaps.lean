module
public import RKCert.ERKFiniteMidpoint

@[expose] public section
/-! # An early invariant defect space already exceeds the even-order budget

There is no causal-completion assumption in this lemma.  A paid Hermite
jump at grade j+1 can be carried to the separated midpoint by strict ordinary
growth, and the reverse count then consumes the remaining stages.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired Module
variable {K:Type*} [Field K] [CharZero K]
variable {n p q j : ℕ} {A:Fin n→Fin n→K} {b:Vec K n}

/-- A numerical budget for a genuinely invariant ordinary grade. -/
theorem invariant_early_stage_budget (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hs:Separated A q) (pay:q+2≤p) (hj:j+1≤q)
    (hc:(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j) :
    p+finrank K (zeroSpace A j)+(j+1)/2+(q-j-1)≤n+1 := by
  have hermite:=RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=j)
    (by omega) (zeroSpace A j) le_rfl
    (fun _ hv=>hc (Submodule.mem_map_of_mem hv))
  have grow:=strict_rank_interval ha hs (j+1) (q-j-1) (by omega) (by omega)
  rw [show j+1+(q-j-1)=q by omega] at grow
  have hq:=tree_rank_eq ho hs (by omega)
  have back:=backward_count ha ho q (p-q-2) (by omega)
  omega

/-- Grade-eight noninvariance follows already at the target even-order
stage budget.  It needs neither the completion theorem nor distinct clocks. -/
theorem grade_eight_noninvariant_at_even_budget (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b (2*q)) (q9:9≤q) (small:n≤3*q+1) :
    ¬(zeroSpace A 8).map (diag (nodes A))≤zeroSpace A 8 := by
  intro hc
  have hs:Separated A q := explicit_separated ha ho (by omega) (by have h:=explicit_order_le_stages ha ho;omega)
  have five:=grade_five_surplus ha (hs.mono (show 5≤q by omega))
  have eight:=strict_rank_interval ha hs 5 3 (by omega) (by omega)
  change finrank K (zeroSpace A 5)+3≤finrank K (zeroSpace A 8) at eight
  have h:=invariant_early_stage_budget (j:=8) ha ho hs (by omega) (by omega) hc
  omega

/-- The grade-five through grade-eight staircase, together with the
four actual mask escapes needed by the one-escape head chart. -/
theorem early_thin_chart_at_even_budget (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b (2*q)) (q9:9≤q) (small:n≤3*q+1)
    (cap:finrank K (zeroSpace A 8)≤8) :
    (∀j,5≤j→j≤8→finrank K (zeroSpace A j)=j) ∧
    (∀j,5≤j→j≤8→¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j) := by
  have hs:Separated A q := explicit_separated ha ho (by omega) (by have h:=explicit_order_le_stages ha ho;omega)
  have five:=grade_five_surplus ha (hs.mono (show 5≤q by omega))
  have ranks (j:ℕ) (lo:5≤j) (hi:j≤8) : finrank K (zeroSpace A j)=j := by
    have low:=strict_rank_interval ha hs 5 (j-5) (by omega) (by omega)
    have high:=strict_rank_interval ha hs j (8-j) (by omega) (by omega)
    rw [show 5+(j-5)=j by omega] at low
    rw [show j+(8-j)=8 by omega] at high
    omega
  refine ⟨ranks,?_⟩
  intro j lo hi hc
  by_cases eq:j=8
  · subst j
    exact grade_eight_noninvariant_at_even_budget ha ho q9 small hc
  have G:=RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=j)
    (by omega) (zeroSpace A j) le_rfl
    (fun _ hv=>hc (Submodule.mem_map_of_mem hv))
  rw [ranks j lo hi,ranks (j+1) (by omega) (by omega)] at G
  omega

end RKCert.Paired.FiniteMidpoint

namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.OneEscape RKCert.Paired.Clock Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

/-- Under the contrary rank hypothesis, incoming (not outgoing) Hermite
rules out invariance at the last grade. No completion assumption is needed. -/
theorem thin_eight_ranks (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (pay:16≤p)
    (cap:finrank K (zeroSpace A 8)≤8) :
    (∀j,5≤j→j≤8→finrank K (zeroSpace A j)=j) ∧
    (∀j,5≤j→j≤8→¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j) := by
  have hs:Separated A 8:=explicit_separated ha ho (by omega) (by omega)
  have five:=grade_five_surplus ha (hs.mono (by decide : 5≤8))
  have rk (j:ℕ) (lo:5≤j) (hi:j≤8) : finrank K (zeroSpace A j)=j := by
    have low:=strict_rank_interval ha hs 5 (j-5) (by omega) (by omega)
    have high:=strict_rank_interval ha hs j (8-j) (by omega) (by omega)
    rw [show 5+(j-5)=j by omega] at low
    rw [show j+(8-j)=8 by omega] at high
    omega
  refine ⟨rk,fun j lo hi hc=>?_⟩
  rcases eq_or_lt_of_le hi with rfl|hi'
  · have G:=RKCert.Endpoint.forward_invariant_incoming_rank ha ho (j:=7) (by omega)
      (fun _ hv=>hc (Submodule.mem_map_of_mem hv))
    rw [rk 7 (by decide) (by decide),rk 8 (by decide) (by decide)] at G
    omega
  · have G:=RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=j)
      (by omega) (zeroSpace A j) le_rfl (fun _ hv=>hc (Submodule.mem_map_of_mem hv))
    rw [rk j lo hi,rk (j+1) (by omega) (by omega)] at G
    omega

structure OrdinaryEightHead (A:Fin (s+1)→Fin (s+1)→K) (r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) : Prop where
  two : 2≤r
  rank : finrank K U+r=5
  inv : U.map (diag (nodes A))≤U
  low : U≤zeroSpace A 5
  normalized : ∀ x,fiber (nodes A) x w∈U→fiber (nodes A) x w=0
  paid : ∀ k≤3,zeroSpace A (5+k)=chain (diag (nodes A)) U w (r+k)
  sites : r+3<(headSites (nodes A) w).card

theorem ordinary_eight_head (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (pay:16≤p)
    (cap:finrank K (zeroSpace A 8)≤8) : ∃ r U w,OrdinaryEightHead A r U w := by
  obtain ⟨rank,out⟩:=thin_eight_ranks ha ho pay cap
  have flat (j:ℕ) (h:5≤j) (hj:j<8) :
      finrank K (zeroSpace A (j+1))≤finrank K (zeroSpace A j)+1 := by
    rw [rank (j+1) (by omega) (by omega),rank j h hj.le]
  obtain ⟨r,U,w,rp,hU,he,_,h5,_,_,hr,hn,_⟩:=ordinary_normal_head A 5
    (flat 5 le_rfl (by decide)) (out 5 le_rfl (by decide))
  have H:=RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=5) (by omega) U he
    (fun _ hx=>hU (Submodule.mem_map_of_mem hx))
  change finrank K U+3≤finrank K (zeroSpace A 6) at H
  rw [rank 6 (by decide) (by decide)] at H
  rw [rank 5 le_rfl (by decide)] at hr
  have chart:=ordinary_staircase hU rp h5 (h:=3)
    (fun k hk=>flat _ (by omega) (by omega)) (fun k hk=>out _ (by omega) (by omega))
  have first : ∀j<r+3,(diag (nodes A)^j) w∈zeroSpace A 8 := by
    rw [show 8=5+3 by decide,chart 3 le_rfl]
    exact (chain_le_iff _).mp le_rfl |>.2
  have escape : (diag (nodes A)^(r+3)) w∉zeroSpace A 8 := by
    intro hh
    have e:=chain_sup_map (w:=w) (n:=r+3) hU (by omega)
    have heq:zeroSpace A 8=chain (diag (nodes A)) U w (r+3) := chart 3 le_rfl
    rw [←heq] at e
    apply out 8 (by decide) le_rfl
    calc
      _≤zeroSpace A 8⊔(zeroSpace A 8).map (diag (nodes A)):=le_sup_right
      _=chain (diag (nodes A)) U w (r+3+1):=e
      _≤zeroSpace A 8:=by
        change chain (diag (nodes A)) U w (r+3)⊔
          Submodule.span K {((diag (nodes A))^(r+3)) w}≤zeroSpace A 8
        rw [←heq]
        exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem ..).mpr hh)
  exact ⟨r,U,w,⟨by omega,hr.symm,hU,he,hn,chart,more_sites_than_paid first escape⟩⟩

end RKCert.Paired.FiniteMidpoint

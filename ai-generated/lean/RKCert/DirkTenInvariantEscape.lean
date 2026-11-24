module
public import RKCert.DirkEvenCore
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

/-- Native grade-six obstruction at the next-to-extremal terminal chart:
if F10 and F11 have ranks at most 10 and 12, an invariant summand inside
F10 cannot contain all of F6. This uses genuine original-stage Hermite
bounds; no saturation, fixed-grid or terminal-clean assumptions are imported. -/
theorem grade_six_escapes_ten (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (pay:11≤p) (ten:finrank K (zeroSpace A 10)≤10) (eleven:finrank K (zeroSpace A 11)≤12)
    {W:Submodule K (Vec K s)} (inside:W≤zeroSpace A 10) (inv:W.map (diag (nodes A))≤W) :
    ¬zeroSpace A 6≤W :=by
  intro cover
  let F:=zeroSpace A
  let T:=diag (nodes A)
  obtain ⟨U,ut,ui,largest⟩:=largest_invariant T (F 10)
  let k:=finrank K U
  have six:F 6≤U:=cover.trans (largest W inside inv)
  have sixmin:5≤finrank K (F 6):=by
    have low:=dirk_forward_rank_three ha ho (by omega)
    have gr:=dirk_grade_six_surplus ha ho (by omega)
    change 5≤finrank K (zeroSpace A 6)
    omega
  have floor:5≤k:=sixmin.trans (Submodule.finrank_mono six)
  have incoming:=dirk_forward_invariant_outgoing ha ho (j:=10) (by omega) U ut (fun v hv=>ui ⟨v,hv,rfl⟩)
  change k+10/2≤finrank K (zeroSpace A 11) at incoming
  have cap:k≤7:=by omega
  have ceilings (j:ℕ) (low:2≤j) (high:j≤10):finrank K (F j)≤j:=by
    have gr:=flag_gain ha ho low high (by omega)
    change finrank K (F j)+(10-j)≤finrank K (zeroSpace A 10) at gr
    omega
  have mono:Monotone F:=fun _ _ ij=>zeroSpace_mono A ij
  have step(j:ℕ):(F j).map T≤F (j+1):=Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)
  have next (j:ℕ) (jl:6≤j) (jh:j≤7) (small:k≤j) (enough:k≤finrank K (F j)+1) (fj:F j≤U) : False:=by
    have fjmin: j-1≤finrank K (F j):=by
      have gr:=flag_gain ha ho (a:=6) (n:=j) (by decide) jl (by omega)
      change finrank K (F 6)+(j-6)≤finrank K (F j) at gr
      omega
    by_cases ff:(F j).map T≤F j
    · have gr:=dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) (F j) le_rfl (fun v hv=>ff ⟨v,hv,rfl⟩)
      have bound:=ceilings (j+1) (by omega) (by omega)
      change finrank K (F j)+j/2≤finrank K (F (j+1)) at gr
      omega
    · let S:=F j ⊔ (F j).map T
      have inc:S≤U:=sup_le fj ((Submodule.map_mono fj).trans ui)
      have strict:F j<S:=lt_of_le_of_ne le_sup_left (fun e=>ff (le_sup_right.trans (le_of_eq e.symm)))
      have more:=Submodule.finrank_lt_finrank_of_lt strict
      have eq:S=U:=Submodule.eq_of_le_of_finrank_le inc (by change k≤_;omega)
      have lift:U≤F (j+1):=eq ▸ sup_le (mono (by omega)) (step j)
      have gr:=dirk_forward_invariant_outgoing ha ho (j:=j+1) (by omega) U lift (fun v hv=>ui ⟨v,hv,rfl⟩)
      have bound:=ceilings (j+2) (by omega) (by omega)
      change k+(j+1)/2≤finrank K (F (j+2)) at gr
      have ki:finrank K (F j)<k:=more.trans_le (Submodule.finrank_mono inc)
      omega
  by_cases small:k≤6
  · exact next 6 (by decide) (by decide) small (by omega) six
  have k7:k=7:=by omega
  have seven:F 7≤U:=by
    by_contra escape
    have paid:=terminal_quotient_growth T F mono step ut ui largest (by decide:7≤10) escape
    have lt:U<F 7 ⊔ U:=lt_of_le_of_ne le_sup_right (fun e=>escape (le_sup_left.trans (le_of_eq e.symm)))
    have rk:=Submodule.finrank_lt_finrank_of_lt lt
    change k<_ at rk
    change finrank K (F 7 ⊔ U:Submodule K (Vec K s))+(10-7)≤finrank K (zeroSpace A 10) at paid
    omega
  have fk:=flag_gain ha ho (a:=6) (n:=7) (by decide) (by decide) (by omega)
  change finrank K (F 6)+(7-6)≤finrank K (F 7) at fk
  exact next 7 (by decide) (by decide) (by omega) (by omega) seven
end RKCert.Paired.Terminal


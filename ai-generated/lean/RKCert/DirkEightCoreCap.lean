module
public import RKCert.Dirk17Ranks
public import RKCert.DirkEvenCore
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p ε:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- An invariant budget at genuine ordinary grade eight.  Unlike the full
one-escape normal form it needs no paid head products, scalar cardinal,
or assumptions about whether the initial row is explicit. -/
theorem eight_core_small (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (pay:10≤p)
    (f6:finrank K (zeroSpace A 6)=5+ε) (f7:finrank K (zeroSpace A 7)=6+ε)
    (f8:finrank K (zeroSpace A 8)=7+ε) (f9:finrank K (zeroSpace A 9)≤9+ε)
    {W:Submodule K (Vec K s)} (inside:W≤zeroSpace A 8) (inv:W.map (diag (nodes A))≤W):
    finrank K W≤3+ε:=by
  let F:=zeroSpace A;let C:=diag (nodes A)
  obtain ⟨U,um,ui,maximum⟩:=largest_invariant C (F 8)
  have wb:W≤U:=maximum W inside inv
  have quota(j:ℕ)(lo:j≤8)(out:¬F j≤U):
      finrank K (F j ⊔ U:Submodule K (Vec K s))+(8-j)≤finrank K (F 8):=
    terminal_quotient_growth C F (fun _ _ h=>zeroSpace_mono A h)
      (fun j=>Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)) um ui maximum lo out
  have grow(j:ℕ)(le:j≤8)(paid:U≤F j):finrank K U+j/2≤finrank K (F (j+1)):=
    dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) U paid (fun v hv=>ui ⟨v,hv,rfl⟩)
  change finrank K (F 6)=5+ε at f6;change finrank K (F 7)=6+ε at f7
  change finrank K (F 8)=7+ε at f8;change finrank K (F 9)≤9+ε at f9
  have e:=grow 8 (by decide) um
  change finrank K U+4≤finrank K (F 9) at e
  have es7:¬F 7≤U:=by intro inc;have z:=Submodule.finrank_mono inc;omega
  have le7:U≤F 7:=by
    have q:=quota 7 (by decide) es7
    have eq:F 7=F 7⊔U:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    exact le_sup_right.trans eq.ge
  have g7:=grow 7 (by decide) le7
  change finrank K U+3≤finrank K (F 8) at g7
  have es6:¬F 6≤U:=by intro inc;have z:=Submodule.finrank_mono inc;omega
  have le6:U≤F 6:=by
    have q:=quota 6 (by decide) es6
    have eq:F 6=F 6⊔U:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    exact le_sup_right.trans eq.ge
  have g6:=grow 6 (by decide) le6
  change finrank K U+3≤finrank K (F 7) at g6
  have lim:=Submodule.finrank_mono wb
  omega

/-- Grade five cannot be fully included in any true invariant part of F8
on the order-seventeen numerical fork. This works over all char-zero
fields, including the two exceptional complex quartic ratios. -/
theorem seventeen_five_visible {A:Fin 23→Fin 23→K} {b:Vec K 23}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) {W:Submodule K (Vec K 23)}
    (inside:W≤zeroSpace A 8) (inv:W.map (diag (nodes A))≤W):¬zeroSpace A 5≤W:=by
  intro five
  have R:=Seventeen.ranks ha ho
  have cap:=eight_core_small ha ho (by decide) R.six R.seven R.eight R.nine.2 inside inv
  have r5:=R.five.1
  have eq:=Submodule.eq_of_le_of_finrank_le five (by omega)
  have yi:(zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5:=eq ▸ inv
  have g:=dirk_forward_invariant_incoming ha ho (j:=5) (by decide) (fun v hv=>yi ⟨v,hv,rfl⟩)
  change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at g
  have z:=Submodule.finrank_mono five;have gr:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by decide)
  have low:=R.three
  omega
end RKCert.Paired.Terminal

module
public import RKCert.DirkNineProductObstruction
public import RKCert.FiveDebutObstruction
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.OneEscape
variable {K:Type*} [Field K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
variable {U:Submodule K (Vec K s)} {w:Vec K s}

/-- The product refund in the noninvariant raised-nine space already
makes the entire clock-invariant summand a physical coordinate algebra,
for any normalized or unnormalized head and any positive ending length. -/
theorem nine_core_closed {n:ℕ} (nn:0<n) (inv:U.map (diag (nodes A))≤U)
    (inc:U≤zeroSpace A 5) (ending:raisedNine A=chain (diag (nodes A)) U w n)
    (out:¬(raisedNine A).map (diag (nodes A))≤raisedNine A)
    (products:∀a∈zeroSpace A 5,∀v∈zeroSpace A 5,a*v∈raisedNine A) : Clock.MulClosed U :=by
  let c:=nodes A
  let w₀:=w-Clock.correction c U w
  have hn:raisedNine A=chain (diag c) U w₀ n:=
    ending.trans (chain_sub_head inv (Clock.correction_mem c U w) n).symm
  have count:=Clock.head_sites_of_noninvariant inv nn (hn ▸ out)
  intro a ha v hv
  exact core_mul_of_restricted_products inv (Clock.normalized c U w) count
    (fun x hx y hy=>hn ▸ products x (inc hx) y hy) ha (inc hv)

variable [CharZero K]
/-- Both terminal grade-nine short-head possibilities are impossible.
The r=1 branch calls the separate true fifth-debut theorem; the r=2 branch
uses only the two cheap heads and the refunded grade-nine primitive tests. -/
theorem no_nine_short_head {r:ℕ} (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:14≤p)
    (short:r=1 ∨ r=2) (inv:U.map (diag (nodes A))≤U)
    (band:∀k≤4,zeroSpace A (5+k)=chain (diag (nodes A)) U w (r+k))
    (out:¬(raisedNine A).map (diag (nodes A))≤raisedNine A)
    (products:∀a∈zeroSpace A 5,∀v∈zeroSpace A 5,a*v∈raisedNine A) : False :=by
  rcases short with rfl|rfl
  · have first:zeroSpace A 5=chain (diag (nodes A)) U w 1:=band 0 (by decide)
    have ninth:zeroSpace A 9=chain (diag (nodes A)) U w 5:=band 4 (by decide)
    have ending:raisedNine A=chain (diag (nodes A)) U w 6:=by
      rw [raisedNine,ninth,chain_sup_map inv (by decide:0<5)]
    have inc:=((chain_le_iff 1).mp first.ge).1
    have alg:=nine_core_closed (by decide) inv inc ending out products
    exact FiveDebut.no_grade5_head ha ho (by omega) inv alg inc (fun k hk=>band k (by omega))
  · exact no_nine_two_head ha ho hp inv (band 0 (by decide)) (band 4 (by decide)) out products
end RKCert.Paired.Terminal

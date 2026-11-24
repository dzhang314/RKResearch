module
public import RKCert.Dirk17EarlyFiveThree
public import RKCert.Dirk17EarlyFiveFour
public import RKCert.DirkDoublingTrace
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Terminal RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 23→Fin 23→K} {b:Vec K 23}

/-- The complete anchored early marked-surplus exclusion, assuming only
the actual grade-four rank. All algebra and the physical cuts are valid
over an arbitrary characteristic-zero field. -/
theorem no_early_with_quartic_rank (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anchor:q₂ (mat A) (nodes A) 1=0) (r4:finrank K (zeroSpace A 4)=2)
    (sur:4≤finrank K (marked A 17 5)):False:=by
  have R:=Early.budget ha ho anchor r4 sur
  rcases R.f5 with three|four
  · exact Early.no_five_three R ha ho three
  · exact Early.no_five_four R ha ho four

omit [CharZero K] in
/-- The early surplus earns the ninth ordinary pure cap before any
grade-four hypothesis. This allows a general grade-four-to-nine theorem
to supply the required exact grade-four rank without circularity. -/
theorem early_rank_nine_cap (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anchor:q₂ (mat A) (nodes A) 1=0) (sur:4≤finrank K (marked A 17 5)) :
    finrank K (zeroSpace A 9)≤8:=by
  have f56:=Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=5) (by decide) (by decide))
  have f67:=Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=6) (by decide) (by decide))
  change finrank K (marked A 17 5)<finrank K (marked A 17 6) at f56
  change finrank K (marked A 17 6)<finrank K (marked A 17 7) at f67
  have dm:=marked_rank A 17 7
  change finrank K (treeSpace A 9)+finrank K (marked A 17 7)=23 at dm
  have sep:=poly_separated_delayed_first (dirk_first_row ha anchor) ho (q:=8) (m:=9)
    (by decide) (by decide)
  have d:9+finrank K (zeroSpace A 9)≤finrank K (treeSpace A 9):=
    treeSpace_rank_of_delayed (by decide:8≤9) sep
  omega
/-- An actual order-17 lower-triangular 23-stage tableau with zero
ordinary quadratic seed cannot have an early marked surplus. This rules
out the whole anchored early case over every characteristic-zero field. -/
theorem no_early (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anchor:q₂ (mat A) (nodes A) 1=0) (sur:4≤finrank K (marked A 17 5)):False:=by
  have cap:=early_rank_nine_cap ha ho anchor sur
  have gain:=grade_four_nine_surplus ha ho (by decide:13≤17)
  have f3:finrank K (zeroSpace A 3)=1:=by
    have z:excess A=0:=by simp [excess,anchor]
    simpa only [z,add_zero] using (ranks ha ho).three
  have strict:=Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=3) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at strict
  exact no_early_with_quartic_rank ha ho anchor (by omega) sur

end RKCert.Paired.Seventeen

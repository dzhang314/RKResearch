module
public import RKCert.ERKOrderedQ7Terminal

@[expose] public section
namespace RKCert
open RKCert.Paired RKCert.Paired.FiniteMidpoint Polynomial
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 1600000

/-- Genuine explicit order 14 needs at least 21 stages over any
characteristic-zero field. No ordering, sign or simple-node condition. -/
theorem explicit_order14_ge21_field {s:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14) : 21≤s := by
  by_contra! small
  cases s with
  | zero =>
    have h := explicit_order_le_stages ha ho
    omega
  | succ s =>
    have S := saturated_short (q:=7) (ε:=0) ha ho (by decide) (by decide) (by omega)
    have M := even_seven_margin ha ho S
    obtain ⟨r,U,w,G,C⟩:=even_seven_chart ha ho S M
    obtain ⟨v,P,C,Pr⟩:=even_seven_profile ha ho S M C
    have r2:=C.marked.rTwo
    have pBound:=Pr.degree
    by_cases hr:3≤r
    · exact cubic_from_seven_masks ha S M C Pr P Pr.nonzero (by omega) 1 (by omega) (by rw [pow_one])
    have er:r=2 := by omega
    subst r
    obtain ⟨pd,pfactor,sites⟩:=seven_terminal_factors ha ho S C Pr
    by_cases p0:P.eval 0=0
    · have h : (X:K[X])∣P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
      obtain ⟨R,e⟩:=h
      have rn : R≠0 := fun hz=>Pr.nonzero (by rw [e,hz,mul_zero])
      have rd : R.natDegree≤3 := by rw [e,natDegree_X_mul rn] at pd;omega
      exact cubic_from_seven_masks ha S M C Pr R rn rd 0 (by decide) (by rwa [pow_zero,one_mul])
    · obtain ⟨i,hi,hv,nz,tests⟩:=physical_seven_knot ha S M C Pr (X:K[X]) X_ne_zero (by simp)
      let u:=nodes A i
      have nu : u*P.eval u≠0 := by simpa only [eval_mul,eval_X] using nz
      have inn : u≠0 := fun hz=>nu (by rw [hz,zero_mul])
      have hn : P.eval u≠0 := fun hz=>nu (by rw [hz,mul_zero])
      have prop : u=1∨dSixValue u=0∧P.eval u≠0 :=
        (sites i hi hv).imp id (fun e=>⟨e inn,hn⟩)
      apply fixed14_divisor_nonzero P pd (pfactor p0) u prop
      have eq := tests 1 (by simp)
      simpa only [one_mul] using eq

theorem explicit_order14_ge21_charZero {R:Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14) :
    21≤s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO=>explicit_order14_ge21_field hA hO) ha ho

theorem explicit_order14_ge21_orderedField {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {s:ℕ} {A:Fin s→Fin s→F} {b:Vec F s} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14) :
    21≤s := explicit_order14_ge21_field ha ho

end RKCert


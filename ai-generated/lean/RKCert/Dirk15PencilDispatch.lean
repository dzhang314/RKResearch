module

public import RKCert.Dirk15NativeSurvivor
public import RKCert.Dirk15HiddenPencilPorts
public import RKCert.Dirk15K1TrueTwoPivots
public import RKCert.Dirk15K2TruePivot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! # The remaining exact scalar obligations for the unrestricted floor

These are explicit premises, not new axioms. This module does not assert
that the fixed/free pencil nonvanishing checks have been kernel-proved.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def Order15PencilShape (D : K[X]) : Prop :=
  (∃ a : K,a≠0 ∧ D=C a*(X*jacobiTwo K 6)) ∨
  (∃ a t : K,a≠0 ∧ D=C a*(X*(jacobiTwo K 7+C t*jacobiTwo K 6)))

theorem Order15MinimalHead.DeletedPencil.shape {A : Fin 20→Fin 20→K} {b : Vec K 20}
    {h : Order15MinimalHead A b} (D : h.DeletedPencil) : Order15PencilShape D.D := by
  rcases D.jacobi_shape with ⟨_,s⟩|⟨_,s⟩
  · exact Or.inl s
  · exact Or.inr s

/-- The exact scalar certificate objectives, with no additional rank
or numerical hypothesis about the RK array. -/
structure Order15PencilCertificates (K : Type*) [Field K] [CharZero K] : Prop where
  forward : ∀ D : K[X],Order15PencilShape D → ∀ P : K[X],P≠0 → P.natDegree≤4 → P∣D →
    ∀ u : K,u≠0 → D.eval u=0 → P.eval u≠0 → paidMoment P u 1=0 → paidMoment P u 2=0 → False
  reverse : ∀ D : K[X],Order15PencilShape D → ∀ P : K[X],P≠0 → P.natDegree≤4 → P∣D →
    ∀ y : K,y≠0 → D.eval (1-y)=0 → P.eval (1-y)≠0 →
      paidMoment (reflectPolynomial P) y 1=0 → paidMoment (reflectPolynomial P) y 2=0 → False
  both : ∀ D : K[X],Order15PencilShape D → ∀ T : K[X],T≠0 → T.natDegree≤3 → T∣D →
    ∀ u y : K,u≠0 → y≠0 → D.eval u=0 → D.eval (1-y)=0 → T.eval u≠0 → T.eval (1-y)≠0 →
      paidMoment T u 1*paidMoment T u 3-(paidMoment T u 2)^2=0 →
      paidMoment (reflectPolynomial T) y 1*paidMoment (reflectPolynomial T) y 3-
        (paidMoment (reflectPolynomial T) y 2)^2=0 → False

variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

omit [CharZero K] in
private theorem mirror_to_nodes (i : Fin 20) : 1-mirror A i=nodes A i := by simp [mirror]

set_option maxHeartbeats 2200000 in
theorem order15_twenty_impossible_of_pencil_certificates [IsAlgClosed K]
    (cert : Order15PencilCertificates K) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) : False := by
  obtain ⟨_,hm,H⟩ := order15_twenty_minimal_chart ha ho
  by_cases hidden : zeroSpace A 4≤simultaneousGhosts A b
  · obtain ⟨h⟩ := order15_two_hidden_head ha ho H hidden
    obtain ⟨D⟩ := h.head.deleted_pencil ha ho H
    obtain ⟨S⟩ := h.actual_square_signatures D ha ho H
    obtain ⟨_,pn,_⟩ := S.factor ha ho H
    obtain ⟨u,un,du,dv,np,j1,j2⟩ := S.true_forward_pivot ha ho H
    exact cert.forward D.D D.shape S.T pn S.Tdegree dv u un du np j1 j2
  · change ¬∀ v : Vec K 20,v∈zeroSpace A 4→v∈simultaneousGhosts A b at hidden
    push Not at hidden
    obtain ⟨v,hv,vG⟩ := hidden
    obtain ⟨h⟩ := order15_minimal_head ha ho H
    have lo := h.low
    have hi := h.high
    rcases (show finrank K h.U=1 ∨ finrank K h.U=2 by omega) with r|r
    · obtain ⟨J⟩ := order15_k1_head H h r
      obtain ⟨D⟩ := J.head.deleted_pencil ha ho H
      obtain ⟨M⟩ := J.mixed_signature D v ha ho H hm hv vG
      obtain ⟨P⟩ := M.true_two_pivots ha ho H hm hv
      by_cases p : M.P∣D.D
      · exact cert.forward _ D.shape M.P M.P_ne M.P_degree p _ P.f_clock P.f_root
          P.f_omit P.f_one P.f_two
      · obtain ⟨T,tn,td,mt,dvd,u1,y1⟩ := P.affine_gram_gate p
        have veto {x : K} (ne : M.P.eval x≠0) : T.eval x≠0 := by
          intro e
          apply ne
          rw [mt,eval_mul,e,mul_zero]
        exact cert.both _ D.shape T tn td dvd _ _ P.f_clock P.r_clock P.f_root
          (by rw [mirror_to_nodes]; exact P.r_root) (veto P.f_omit) (by rw [mirror_to_nodes]; exact veto P.r_omit)
          u1 y1
    · have ⟨outside,_⟩ := order15_minimal_visible_quartic ha ho H hm h hv vG
      obtain ⟨J⟩ := order15_k2_head h r hv outside
      obtain ⟨D⟩ := J.head.deleted_pencil ha ho H
      obtain ⟨T⟩ := J.actual_visible_factor D ha ho H hm
      obtain ⟨i,_,hi,_,_,hOmit,root,_,p1,p2⟩ := T.true_reverse_pivot ha ho H hm
      exact cert.reverse _ D.shape T.P T.nonzero T.degree ⟨T.R,T.factor⟩ _
        hi (by rwa [mirror_to_nodes]) (by rwa [mirror_to_nodes]) p1 p2

/-- The scalar nonvanishing package, once checked, is the explicit
remaining input to the arbitrary-characteristic-zero 21-stage statement. -/
theorem dirk_order15_ge21_of_pencil_certificates
    (cert : Order15PencilCertificates (AlgebraicClosure K)) {s : ℕ}
    {A : Fin s→Fin s→K} {b : Vec K s}
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) : 21≤s := by
  have known := dirk_order15_native_rank ha ho
  by_contra bad
  have s20 : s=20 := by omega
  subst s
  let f := algebraMap K (AlgebraicClosure K)
  exact order15_twenty_impossible_of_pencil_certificates cert (lowerTriangular_map ha f) (ho.map f)

end
end RKCert.Paired

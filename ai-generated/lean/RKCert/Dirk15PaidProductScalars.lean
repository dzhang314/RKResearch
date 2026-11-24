module

public import RKCert.Dirk15DeletedPaidComparisons
public import RKCert.EndpointJacobiMomentShift

@[expose] public section

/-! # Exactly paid scalar components of grade-ten products

For three actual shifts the initial component lies in the top one or
two Jacobi directions; four shifts make it zero. Every assertion
retains the unknown original terminal via the factor 1-X probe.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace Order15MinimalHead.DeletedPencil
variable {h : Order15MinimalHead A b} {D : h.DeletedPencil}

omit [CharZero K] in
theorem clock_dvd_of_eval_origin {P : K[X]} (e : P.eval 0=0) : X∣P := by
  have z : X-C (0:K)∣P := dvd_iff_isRoot.mpr e
  simpa only [map_zero,sub_zero] using z

structure ShiftCofactors {v : Vec K 20} {m q n : ℕ} (S : D.PaidShiftProfiles v m q n) where
  G : K[X]
  H : Fin (m+1) → K[X]
  relation : D.D=X*G
  factors : ∀ i,S.poly i=X*H i
  G_degree : D.D.natDegree=G.natDegree+1
  degrees : ∀ i,(H i).natDegree≤q-1
  G_quiet : JacobiQuiet G 5
  quiet : ∀ i,JacobiQuiet (H i) 3
  adjacent : ∀ i : Fin m,∃ a : K,H i.succ=X*H i.castSucc+C a*G

theorem PaidShiftProfiles.choose_cofactors {v : Vec K 20} {m q n : ℕ}
    (S : D.PaidShiftProfiles v m q n) : Nonempty (ShiftCofactors S) := by
  obtain ⟨G,eG⟩ := clock_dvd_of_eval_origin D.origin
  have Gne : G≠0 := by
    intro z
    have t := D.dmin
    rw [eG,z,mul_zero,natDegree_zero] at t
    omega
  have dg : D.D.natDegree=G.natDegree+1 := by
    rw [eG,natDegree_mul X_ne_zero Gne,natDegree_X,add_comm]
  have p (i : Fin (m+1)) := clock_dvd_of_eval_origin (S.origin i)
  choose Q eqQ using p
  refine ⟨⟨G,Q,eG,eqQ,dg,?_,?_,?_,?_⟩⟩
  · intro i
    by_cases z : Q i=0
    · simp [z]
    · have d := S.degree i
      rw [eqQ,natDegree_mul X_ne_zero z,natDegree_X] at d
      omega
  · intro k hk
    have e := D.quiet (X^k) (by rw [natDegree_X_pow]; exact hk)
    rw [eG,show X*G*((1-X)*X^k)=X*(1-X)*G*X^k by ac_rfl] at e
    exact e
  · intro i k hk
    have e := S.quiet i (X^k) (by rw [natDegree_X_pow]; exact hk)
    rw [eqQ,show X*Q i*((1-X)*X^k)=X*(1-X)*Q i*X^k by ac_rfl] at e
    exact e
  · intro i
    obtain ⟨a,eq⟩ := S.adjacent i
    refine ⟨a,mul_left_cancel₀ X_ne_zero ?_⟩
    rw [eqQ,eqQ,eG] at eq
    linear_combination eq

theorem PaidShiftProfiles.unfolded_initial_three {v : Vec K 20} {n : ℕ}
    (S : D.PaidShiftProfiles v 2 7 n) :
    ∃ a : K,S.poly 0=C a*(X*jacobiTwo K 6) := by
  obtain ⟨C'⟩ := S.choose_cofactors
  obtain ⟨a,ea⟩ := C'.adjacent 0
  obtain ⟨b,eb⟩ := C'.adjacent 1
  have eq := jacobiQuiet_three a b ea eb (C'.degrees 0)
    (C'.quiet 0) (C'.quiet 1) (C'.quiet 2) C'.G_quiet
  refine ⟨(C'.H 0).coeff 6,?_⟩
  have q : C'.H 0=C ((C'.H 0).coeff 6)*jacobiTwo K 6 := eq
  rw [C'.factors]
  calc
    _ = X*(C ((C'.H 0).coeff 6)*jacobiTwo K 6) := congrArg (fun P : K[X] => X*P) q
    _ = _ := by ac_rfl

theorem PaidShiftProfiles.unfolded_four_zero {v : Vec K 20} {n : ℕ}
    (S : D.PaidShiftProfiles v 3 7 n) (d8 : D.D.natDegree=8) :
    ∀ i : Fin 4,S.poly i=0 := by
  obtain ⟨C'⟩ := S.choose_cofactors
  obtain ⟨a,ea⟩ := C'.adjacent 0
  obtain ⟨b,eb⟩ := C'.adjacent 1
  obtain ⟨c,ec⟩ := C'.adjacent 2
  have dG : C'.G.natDegree=7 := by have x := C'.G_degree; omega
  have es := jacobiQuiet_four a b c ea eb ec dG (C'.degrees 0) (C'.degrees 1)
    (C'.degrees 2) (C'.degrees 3) (C'.quiet 0) (C'.quiet 1) (C'.quiet 2)
    (C'.quiet 3) C'.G_quiet
  have q (i : Fin 4) : C'.H i=0 := by
    fin_cases i
    · exact es.1
    · exact es.2.1
    · exact es.2.2.1
    · exact es.2.2.2
  intro i
  rw [C'.factors,q,mul_zero]

omit [CharZero K] in
private theorem degree_le_after_shift {P H Q : K[X]} {n q : ℕ}
    (nq : n≤q) (deg : H.natDegree≤q) (dQ : Q.natDegree≤q) (eq : H=X^n*P+Q) :
    P.natDegree≤q-n := by
  by_contra! h
  have pn : P≠0 := by intro z; rw [z,natDegree_zero] at h; omega
  have da : (X^n*P).natDegree=n+P.natDegree := by
    rw [natDegree_mul (pow_ne_zero n X_ne_zero) pn,natDegree_X_pow]
  have e := natDegree_add_eq_left_of_natDegree_lt (p:=X^n*P) (q:=Q) (by omega)
  rw [eq,e,da] at deg
  omega

theorem PaidShiftProfiles.folded_initial_three {v : Vec K 20} {n : ℕ}
    (S : D.PaidShiftProfiles v 2 10 n) (d7 : D.D.natDegree=7) :
    ∃ a b : K,S.poly 0=X*(C a*jacobiTwo K 7+C b*jacobiTwo K 6) := by
  obtain ⟨C'⟩ := S.choose_cofactors
  obtain ⟨a,ea⟩ := C'.adjacent 0
  obtain ⟨b,eb⟩ := C'.adjacent 1
  let G := C'.G
  let J := C'.H
  change J 1=X*J 0+C a*G at ea
  change J 2=X*J 1+C b*G at eb
  have dG : G.natDegree=6 := by
    have x := C'.G_degree
    change D.D.natDegree=G.natDegree+1 at x
    omega
  let R := C a*X*G+C b*G
  have dR : R.natDegree≤9 := by
    have a1 := natDegree_C_mul_le a (X*G)
    have a2 := natDegree_C_mul_le b G
    have g := natDegree_mul_le (p:=(X:K[X])) (q:=G)
    rw [natDegree_X,dG] at g
    change ((C a*X)*G+C b*G).natDegree≤9
    rw [mul_assoc]
    exact (natDegree_add_le _ _).trans (max_le (by omega) (by omega))
  have eq : J 2=X^2*J 0+R := by rw [eb,ea]; dsimp only [R]; ring
  have d := degree_le_after_shift (by decide : 2≤9) (C'.degrees 2) dR eq
  have j0 : jacobiPair (J 0) 1=0 := by simpa only [pow_zero] using C'.quiet 0 0 (by decide)
  have j1 : jacobiPair (J 1) 1=0 := by simpa only [pow_zero] using C'.quiet 1 0 (by decide)
  have q1 := jacobiQuiet_step b eb j1 (C'.quiet 2) (fun k hk => C'.G_quiet k (hk.trans (by decide)))
  have q0 := jacobiQuiet_step a ea j0 q1 (fun k hk => C'.G_quiet k (hk.trans (by decide)))
  obtain ⟨c,d,hd⟩ := jacobiTwo_top_two (by decide : 2≤7) d (jacobiQuiet_extend q0)
  refine ⟨c,d,?_⟩
  rw [C'.factors]
  change X*J 0=X*(C c*jacobiTwo K 7+C d*jacobiTwo K 6)
  rw [hd]

theorem PaidShiftProfiles.folded_initial_four_zero {v : Vec K 20} {n : ℕ}
    (S : D.PaidShiftProfiles v 3 10 n) (d7 : D.D.natDegree=7) : S.poly 0=0 := by
  obtain ⟨C'⟩ := S.choose_cofactors
  obtain ⟨a,ea⟩ := C'.adjacent 0
  obtain ⟨b,eb⟩ := C'.adjacent 1
  obtain ⟨c,ec⟩ := C'.adjacent 2
  let G := C'.G
  let J := C'.H
  change J 1=X*J 0+C a*G at ea
  change J 2=X*J 1+C b*G at eb
  change J 3=X*J 2+C c*G at ec
  have dG : G.natDegree=6 := by
    have x := C'.G_degree
    change D.D.natDegree=G.natDegree+1 at x
    omega
  let R := (C a*X^2+C b*X+C c)*G
  have cdeg : (C a*X^2+C b*X+C c:K[X]).natDegree≤2 :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]))
        ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X]; decide)))) (by rw [natDegree_C]; decide))
  have dR : R.natDegree≤9 := natDegree_mul_le.trans (by omega)
  have eq : J 3=X^3*J 0+R := by rw [ec,eb,ea]; dsimp only [R]; ring
  have d := degree_le_after_shift (by decide : 3≤9) (C'.degrees 3) dR eq
  have j0 : jacobiPair (J 0) 1=0 := by simpa only [pow_zero] using C'.quiet 0 0 (by decide)
  have j1 : jacobiPair (J 1) 1=0 := by simpa only [pow_zero] using C'.quiet 1 0 (by decide)
  have j2 : jacobiPair (J 2) 1=0 := by simpa only [pow_zero] using C'.quiet 2 0 (by decide)
  have q2 := jacobiQuiet_step c ec j2 (C'.quiet 3) (fun k hk => C'.G_quiet k (hk.trans (by decide)))
  have q1 := jacobiQuiet_step b eb j1 q2 (fun k hk => C'.G_quiet k (hk.trans (by decide)))
  have q0 := jacobiQuiet_step a ea j0 q1 C'.G_quiet
  have z := jacobiPair_detect (J 0) d (jacobiQuiet_extend q0)
  rw [C'.factors]
  change X*J 0=0
  rw [z,mul_zero]

end Order15MinimalHead.DeletedPencil
end
end RKCert.Paired

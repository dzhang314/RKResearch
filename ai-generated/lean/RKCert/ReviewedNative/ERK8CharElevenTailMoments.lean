module

public import RKCert.ReviewedNative.ERK8CharElevenHighHull
public import RKCert.ReviewedNative.ERK8CharElevenReflectedTail

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Arithmetic of the actual late-three hull
A nonzero early four-clock residue \(6+2X\) suffices to pin both of the
paid reflected tail measurements. The proof uses polynomial division and
a Lagrange coefficient identity; no root of the quadratic is required. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem affine_degree_le (a d : K) : (C a+C d*X).natDegree≤1 :=
  natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))

private theorem cancel_quadratic_unit_left {M N W R : K[X]}
    (unit : M*N=1+exceptionalQuadratic*W) (dv : (exceptionalQuadratic : K[X])∣M*R) :
    (exceptionalQuadratic : K[X])∣R := by
  obtain ⟨G,hG⟩ := dv
  refine ⟨N*G-W*R,?_⟩
  linear_combination N*hG-R*unit

/-- The actual late-three hull is a nonzero multiple of \(1+7X\)
modulo the quadratic, assuming only the earned early hull residue. -/
theorem seven_off_paid_tail_hull_remainder
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    (early : ∃ beta : K, beta≠0 ∧ ∃ V : K[X],
      highPrefixHull A f u v=C beta*(C 6+C 2*X)+exceptionalQuadratic*V) :
    ∃ delta : K, delta≠0 ∧ ∃ Z : K[X],
      highTailHull A f u v=C delta*(1+C 7*X)+exceptionalQuadratic*Z := by
  obtain ⟨beta,bn,V,hN⟩ := early
  obtain ⟨gamma,gn,W,hD⟩ := seven_off_paid_hull_remainder ha ho p seven three
  let N := highPrefixHull A f u v
  let F := highTailHull A f u v
  let q : K[X] := exceptionalQuadratic
  let R_N : K[X] := C 6+C 2*X
  let R_D : K[X] := C 4+C 3*X
  let R_F : K[X] := 1+C 7*X
  let L : K[X] := C 10+C 3*X
  let delta := gamma/beta
  have bdelta : (C beta*C delta : K[X])=C gamma := by
    rw [←map_mul,mul_div_cancel₀ _ bn]
  have pP := polynomial_char11 p
  have recombine : R_N*R_F=R_D+C (14:K)*q := by
    simp only [R_N,R_D,R_F,q,exceptionalQuadratic,map_ofNat]
    linear_combination (5*(X:K[X])-10)*pP
  have inverseRN : R_N*L=1+q*C (6:K) := by
    simp only [R_N,L,q,exceptionalQuadratic,map_ofNat]
    linear_combination (1+4*(X:K[X]))*pP
  have factor : nodalHull (offKnots A)=N*F := highHull_factor T
  change N=C beta*R_N+q*V at hN
  change nodalHull (offKnots A)=C gamma*R_D+q*W at hD
  have multEq : C beta*(R_N*(F-C delta*R_F))=q*(W-V*F-C gamma*C 14) := by
    linear_combination hD-factor-F*hN-C gamma*recombine-R_N*R_F*bdelta
  have cb : (C beta⁻¹*C beta : K[X])=1 := by rw [←map_mul,inv_mul_cancel₀ bn,map_one]
  have dv : q∣R_N*(F-C delta*R_F) := by
    refine ⟨C beta⁻¹*(W-V*F-C gamma*C 14),?_⟩
    linear_combination C beta⁻¹*multEq-(R_N*(F-C delta*R_F))*cb
  obtain ⟨Z,hZ⟩ := cancel_quadratic_unit_left inverseRN dv
  refine ⟨delta,div_ne_zero gn bn,Z,?_⟩
  change F=_
  linear_combination hZ

noncomputable def highTailPolyMoment (A : Matrix (Fin 10) (Fin 10) K)
    (f u v : Fin 10) (G : K[X]) : K :=
  let term i := G.eval (nodes A i)/((exceptionalQuadratic : K[X]).eval (nodes A i)*
    highTailCofactor A f u v (nodes A i))
  term f+term u+term v

theorem highTailMoment_poly (A : Matrix (Fin 10) (Fin 10) K)
    (f u v : Fin 10) (k : ℕ) :
    highTailMoment A f u v k=highTailPolyMoment A f u v ((1-X)^k) := by
  simp only [highTailMoment,highTailPolyMoment,eval_pow,eval_sub,eval_one,eval_X]

/-- A polynomial numerator whose division by the quadratic equals
a degree-at-most-two profile on the three physical tail clocks. -/
theorem highTail_poly_moment_of_quotient
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    {theta : K} (H : ExceptionalHead A theta) {G V R : K[X]} (Rd : R.natDegree≤2)
    (idQ : G-highTailHull A f u v*V=exceptionalQuadratic*R) :
    highTailPolyMoment A f u v G=R.coeff 2 := by
  let S := highTailClocks A f u v
  let F := highTailHull A f u v
  let q : K[X] := exceptionalQuadratic
  have Sc : S.card=3 := highTailClocks_card seven three T
  obtain ⟨fu,fv,uv⟩ := highTailClocks_distinct seven three T
  have trip (i : Fin 10) (gi : g A i≠0) (hi : nodes A i∈S) :
      G.eval (nodes A i)/(q.eval (nodes A i)*highTailCofactor A f u v (nodes A i)) =
        R.eval (nodes A i)/highTailCofactor A f u v (nodes A i) := by
    have e := congrArg (fun P : K[X] => P.eval (nodes A i)) idQ
    have z : F.eval (nodes A i)=0 := nodalHull_eval_of_mem hi
    change (G-F*V).eval (nodes A i)=(q*R).eval (nodes A i) at e
    simp only [eval_sub,eval_mul,z,zero_mul,sub_zero] at e
    have qx : q.eval (nodes A i)≠0 := exceptional_quadratic_ne_off H gi
    rw [e,←div_div,mul_comm (q.eval (nodes A i)) (R.eval (nodes A i)),
      mul_div_cancel_right₀ _ qx]
  have lt : R.natDegree < S.card := by omega
  have top := coeff_last_barycentric S R lt
  rw [Sc,show 3-1=2 by decide] at top
  change R.coeff 2 = ∑ x∈({nodes A f,nodes A u,nodes A v}:Finset K),
    R.eval x/(nodalHull (S.erase x)).eval x at top
  rw [Finset.sum_insert (by simp [fu,fv]),Finset.sum_pair uv,←add_assoc] at top
  change G.eval (nodes A f)/(q.eval (nodes A f)*highTailCofactor A f u v (nodes A f))
    +G.eval (nodes A u)/(q.eval (nodes A u)*highTailCofactor A f u v (nodes A u))
    +G.eval (nodes A v)/(q.eval (nodes A v)*highTailCofactor A f u v (nodes A v))=_
  rw [trip f T.f_off (by simp [S,highTailClocks]),trip u T.u_off (by simp [S,highTailClocks]),
    trip v T.v_off (by simp [S,highTailClocks])]
  exact top.symm

/-- The two literal reflected tail measurements have nonzero ratio 1:2,
once the actual late-three hull has its paid quadratic remainder. -/
theorem highTail_moments_of_hull_remainder
    (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    {theta : K} (H : ExceptionalHead A theta)
    {delta : K} (dn : delta≠0) {Z : K[X]}
    (hF : highTailHull A f u v=C delta*(1+C 7*X)+exceptionalQuadratic*Z) :
    highTailMoment A f u v 2≠0 ∧ 2*highTailMoment A f u v 3=highTailMoment A f u v 2 := by
  let F := highTailHull A f u v
  let q : K[X] := exceptionalQuadratic
  let L : K[X] := 1+C 7*X
  let U : K[X] := C delta⁻¹*(X+C 5)
  let V : K[X] := C delta⁻¹*C 10
  let G₂ : K[X] := (1-X)^2
  let G₃ : K[X] := (1-X)^3
  let R₂ := -(C (6:K))-Z*U
  let R₂₃ := -(C (2:K))*X+C 3-Z*V
  have Fn : F.natDegree=3 := by
    exact (natDegree_nodalHull _).trans (highTailClocks_card seven three T)
  have Fc : F.coeff 3=1 := by
    have c : F.coeff F.natDegree=1 := (monic_nodalHull _).coeff_natDegree
    rwa [Fn] at c
  have qn : q.natDegree=2 := quadratic_exact_degree
  have qc : q.coeff 2=1 := by simp [q,exceptionalQuadratic,coeff_X_pow,coeff_X]
  have Ld : (C delta*L).natDegree≤1 := by
    apply (natDegree_C_mul_le _ _).trans
    simpa only [L,map_one] using affine_degree_le (1:K) 7
  change F=C delta*L+q*Z at hF
  have Zd : Z.natDegree≤1 := by
    by_cases Z0 : Z=0
    · simp [Z0]
    have Zeq : q*Z = F-C delta*L := by linear_combination -hF
    have n : (q*Z).natDegree≤3 := by
      rw [Zeq]
      exact natDegree_sub_le_of_le Fn.le (Ld.trans (show 1≤3 by decide))
    have nq : q≠0 := by intro e; simp [e] at qn
    rw [natDegree_mul nq Z0,qn] at n
    omega
  have Zc : Z.coeff 1=1 := by
    have e := congrArg (fun P : K[X] => P.coeff 3) hF
    have h3 : (q*Z).coeff 3=q.coeff 2*Z.coeff 1 :=
      coeff_mul_add_eq_of_natDegree_le qn.le Zd
    rw [Fc,coeff_add,coeff_eq_zero_of_natDegree_lt (Ld.trans_lt (by decide)),h3,qc,one_mul,zero_add] at e
    exact e.symm
  have Ud : U.natDegree≤1 := by
    apply (natDegree_C_mul_le _ _).trans
    exact natDegree_add_le_of_degree_le (show (X:K[X]).natDegree≤1 by simp) (by simp)
  have Uc : U.coeff 1=delta⁻¹ := by simp [U,coeff_X,coeff_C_mul]
  have Vd : V.natDegree≤0 := by simp [V,←map_mul]
  have C6d : (-(C (6:K))).natDegree≤2 := by rw [natDegree_neg]; simp
  have R2d : R₂.natDegree≤2 :=
    natDegree_sub_le_of_le C6d (natDegree_mul_le_of_le Zd Ud)
  have d23 : (-(C (2:K))*X+C 3).natDegree≤1 := by
    rw [show -(C (2:K))*X+C 3=C 3+C (-2:K)*X by simp only [map_neg]; ring]
    exact affine_degree_le _ _
  have wd : (Z*V).natDegree≤1 := natDegree_mul_le_of_le Zd Vd
  have R23d : R₂₃.natDegree≤1 := natDegree_sub_le_of_le d23 wd
  have top : R₂.coeff 2= -delta⁻¹ := by
    have exactTop : (Z*U).coeff 2=Z.coeff 1*U.coeff 1 :=
      coeff_mul_add_eq_of_natDegree_le Zd Ud
    simp [R₂,exactTop,Zc,Uc]
  have inv : (C delta*C delta⁻¹:K[X])=1 := by rw [←map_mul,mul_inv_cancel₀ dn,map_one]
  have pP := polynomial_char11 p
  have g2 : G₂=L*(X+C 5)-C 6*q := by
    simp only [G₂,L,q,exceptionalQuadratic,map_ofNat]
    linear_combination 4*(1-(X:K[X]))*pP
  have g23 : (2:K[X])*G₃-G₂=L*C 10+q*(-C 2*X+C 3) := by
    simp only [G₂,G₃,L,q,exceptionalQuadratic,map_ofNat]
    linear_combination -(5*(X:K[X])+3)*pP
  have div2 : G₂-F*U=q*R₂ := by
    dsimp only [U,R₂]
    rw [g2,hF]
    linear_combination -(L*(X+C 5))*inv
  have div23 : (2:K[X])*G₃-G₂-F*V=q*R₂₃ := by
    dsimp only [V,R₂₃]
    rw [g23,hF]
    linear_combination -(L*C 10)*inv
  have t2 := highTail_poly_moment_of_quotient seven three T H R2d div2
  change highTailPolyMoment A f u v ((1-X)^2)=R₂.coeff 2 at t2
  rw [←highTailMoment_poly,top] at t2
  have t23 := highTail_poly_moment_of_quotient seven three T H (R23d.trans (by decide)) div23
  rw [coeff_eq_zero_of_natDegree_lt (R23d.trans_lt (by decide))] at t23
  have lin : highTailPolyMoment A f u v ((2:K[X])*G₃-G₂)=
      2*highTailMoment A f u v 3-highTailMoment A f u v 2 := by
    simp only [highTailPolyMoment,highTailMoment,G₂,G₃,eval_sub,eval_mul,
      eval_ofNat,eval_pow,eval_one,eval_X,div_eq_mul_inv]
    ring
  rw [lin] at t23
  exact ⟨t2 ▸ neg_ne_zero.mpr (inv_ne_zero dn),sub_eq_zero.mp t23⟩

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_paid_tail_hull_remainder
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.highTail_moments_of_hull_remainder

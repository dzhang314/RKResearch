module

public import RKCert.ReviewedNative.UnitBubbleMoments
public import RKCert.ReviewedNative.LegendreModeEightShifted
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.UnitBubbleLobatto

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.UnitBubbleMoments
open RKCert.ReviewedNative.LegendreEnergy

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def OrdinaryThrough (L : K[X]) (d : ℕ) : Prop :=
  ∀ R : K[X], R.natDegree≤d → integral 0 1 (L*R)=0

theorem integral_const (l r a : K) : integral l r (C a)=(r-l)*a := by
  have h := integral_derivative l r (C a*X)
  rw [derivative_C_mul_X,eval_mul,eval_mul,eval_C,eval_C,eval_X,eval_X] at h
  linear_combination h

theorem formal_parts (l r : K) (F G : K[X]) :
    integral l r (F.derivative*G)+integral l r (F*G.derivative)=
      F.eval r*G.eval r-F.eval l*G.eval l := by
  have h := integral_derivative l r (F*G)
  rwa [derivative_mul,map_add,eval_mul,eval_mul] at h

theorem bubble_shape : (bubble K)=(X:K[X])-X^2 := by
  dsimp only [bubble]
  ring

theorem bubble_deg : (bubble K).natDegree=2 := by
  have e : (1-X : K[X])=-(X-C (1:K)) := by simp
  rw [bubble,e,natDegree_mul X_ne_zero (neg_ne_zero.mpr (X_sub_C_ne_zero _)),
    natDegree_X,natDegree_neg,natDegree_X_sub_C]

theorem bubble_nz : bubble K≠0 := by
  intro e
  have d := bubble_deg (K:=K)
  rw [e,natDegree_zero] at d
  omega

theorem factor_unit_endpoints (G : K[X]) (g0 : G.eval 0=0) (g1 : G.eval 1=0) :
    ∃ S : K[X], G=bubble K*S := by
  have Div : (X:K[X])∣G := by rwa [X_dvd_iff,coeff_zero_eq_eval_zero]
  obtain ⟨T,hT⟩ := Div
  have one : T.IsRoot 1 := by
    change T.eval 1=0
    rwa [hT,eval_mul,eval_X,one_mul] at g1
  obtain ⟨S,hS⟩ := dvd_iff_isRoot.mpr one
  refine ⟨-S,?_⟩
  rw [hT,hS]
  simp only [bubble,map_one]
  ring

theorem unit_integral_pos {G : K[X]} (gn : G≠0) (gd : G.natDegree<19)
    (pos : ∀ x∈Set.Ioo (0:K) 1, 0≤G.eval x) : 0 < integral 0 1 G := by
  obtain ⟨i,hi⟩ := exists_nonzero_grid_sample zero_lt_one gn gd
  exact integral_pos_of_grid_samples zero_lt_one gd.le
    (fun j=>pos _ (intervalPoint_mem zero_lt_one j)) ⟨i,
      lt_of_le_of_ne (pos _ (intervalPoint_mem zero_lt_one i)) hi.symm⟩

theorem ordinary_zero {L : K[X]} (d : L.natDegree≤7) (o : OrdinaryThrough L 7) : L=0 := by
  by_contra nz
  have p := unit_integral_pos (pow_ne_zero 2 nz)
    ((natDegree_pow_le_of_le 2 d).trans_lt (by decide))
    (fun x _=>by simpa only [eval_pow] using sq_nonneg (L.eval x))
  rw [pow_two,o L d] at p
  exact (lt_irrefl 0) p

theorem strip_top {G : K[X]} {d : ℕ} (le : G.natDegree≤d+1)
    (van : G.coeff (d+1)=0) : G.natDegree≤d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases e : n=d+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (le.trans_lt (by omega))

theorem bubble_derivative_top {L : K[X]} (d : L.natDegree≤8) :
    ((bubble K)*L.derivative).coeff 9=-(8:K)*L.coeff 8 := by
  have c9 : L.coeff 9=0 := coeff_eq_zero_of_natDegree_lt (d.trans_lt (by decide))
  rw [bubble_shape,sub_mul,coeff_sub,coeff_X_mul,
    coeff_X_pow_mul L.derivative 2 7,coeff_derivative,coeff_derivative,c9]
  norm_num <;> ring

structure HasNormalizedMode (D : K[X]) (L : K[X]) : Prop where
  degree : L.natDegree=8
  output : L.eval 1=1
  origin : L.eval 0=1
  orthogonal : OrdinaryThrough L 7
  derivativeScale : ∃ a : K, a≠0 ∧ L.derivative=C a*D
  equation : ((bubble K)*L.derivative).derivative+C (72:K)*L=0

theorem normalizedMode_of_bubble {D : K[X]} (dd : D.natDegree=7)
    (orth : OrthogonalThrough D 6) : ∃ L : K[X], HasNormalizedMode D L := by
  let G := formalPrimitive D
  let T := G-C (integral 0 1 G)
  have Dn : D≠0 := by intro e; rw [e,natDegree_zero] at dd;omega
  have Td : T.derivative=D := by
    simp only [T,G,derivative_sub,derivative_formalPrimitive,derivative_C,sub_zero]
  have T0 : integral 0 1 T=0 := by
    change integral 0 1 (G-C (integral 0 1 G))=0
    rw [map_sub,integral_const,sub_zero,one_mul,sub_self]
  have T8 : T.natDegree≤8 := natDegree_sub_le_of_le
    (p := G) (q := C (integral 0 1 G))
    ((natDegree_formalPrimitive_le D).trans (by rw [dd])) (by rw [natDegree_C])
  have Tdegree : T.natDegree=8 := by
    have l := natDegree_derivative_le T
    rw [Td,dd] at l
    omega
  have Tn : T≠0 := by intro e; apply Dn; rw [←Td,e,derivative_zero]
  have To : OrdinaryThrough T 7 := by
    intro R rd
    let S₀ := R-C (integral 0 1 R)
    let S := formalPrimitive S₀
    have Sd : S.natDegree≤8 := (natDegree_formalPrimitive_le _).trans
      (Nat.succ_le_succ (natDegree_sub_le_of_le (p:=R) (q:=C (integral 0 1 R)) rd (by rw [natDegree_C])))
    have S0 : S.eval 0=0 := formalPrimitive_eval_zero _
    have S1 : S.eval 1=0 := by
      change (formalPrimitive S₀).eval 1=0
      rw [←integral_zero_left]
      change integral 0 1 (R-C (integral 0 1 R))=0
      rw [map_sub,integral_const,sub_zero,one_mul,sub_self]
    obtain ⟨V,hV⟩ := factor_unit_endpoints S S0 S1
    have Vd : V.natDegree≤6 := by
      by_cases e : V=0
      · simp [e]
      · rw [hV,natDegree_mul bubble_nz e,bubble_deg] at Sd
        omega
    have dsv : integral 0 1 (D*S)=0 := by
      rw [hV,show D*(bubble K*V)=bubble K*D*V by ring]
      exact orth V Vd
    have ps := formal_parts (0:K) 1 T S
    rw [Td,show S.derivative=S₀ from derivative_formalPrimitive _,S0,S1,
      mul_zero,mul_zero,sub_zero,dsv,zero_add] at ps
    rw [show T*S₀=T*R-C (integral 0 1 R)*T by dsimp [S₀]; ring,
      map_sub,integral_C_mul,T0,mul_zero,sub_zero] at ps
    exact ps
  have T1 : T.eval 1≠0 := by
    intro bad
    obtain ⟨R,h⟩ := dvd_iff_isRoot.mpr (show T.IsRoot 1 from bad)
    have rn : R≠0 := by intro e; apply Tn; rw [h,e,mul_zero]
    have rd : R.natDegree≤7 := by
      have d := T8
      rw [h,natDegree_mul (X_sub_C_ne_zero _) rn,natDegree_X_sub_C] at d
      omega
    have test := To R rd
    have shape : T*R=-((1-X)*R^2) := by rw [h,map_one];ring
    rw [shape,map_neg,neg_eq_zero] at test
    have lin : (1-X:K[X])≠0 := by
      rw [show (1-X:K[X])=-(X-C (1:K)) by simp]
      exact neg_ne_zero.mpr (X_sub_C_ne_zero _)
    have fromD : (1-X:K[X]).natDegree=1 := by
      rw [show (1-X : K[X]) = -(X-C (1:K)) by simp, natDegree_neg, natDegree_X_sub_C]
    have pd : ((1-X)*R^2).natDegree<19 :=
      (natDegree_mul_le_of_le fromD.le (natDegree_pow_le_of_le 2 rd)).trans_lt (by decide)
    have pos := unit_integral_pos (mul_ne_zero lin (pow_ne_zero 2 rn)) pd
      (fun x hx=>by
        simp only [eval_mul,eval_sub,eval_one,eval_X,eval_pow]
        exact mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg _))
    exact pos.ne' test
  let a := (T.eval 1)⁻¹
  have an : a≠0 := inv_ne_zero T1
  let L := C a*T
  have L8 : L.natDegree=8 := by
    change (C a*T).natDegree=8
    rw [natDegree_C_mul an,Tdegree]
  have L1 : L.eval 1=1 := by
    simp only [L,a,eval_mul,eval_C,inv_mul_cancel₀ T1]
  have Ld : L.derivative=C a*D := by simp [L,derivative_mul,Td]
  have Lo : OrdinaryThrough L 7 := by
    intro R rd
    rw [show L*R=C a*(T*R) by dsimp [L];ring,integral_C_mul,To R rd,mul_zero]
  let F := (bubble K)*L.derivative
  let M := F.derivative+C (72:K)*L
  have F9 : F.natDegree≤9 := natDegree_mul_le_of_le bubble_deg.le
    ((natDegree_derivative_le L).trans (by rw [L8]))
  have Md : M.natDegree≤8 := natDegree_add_le_of_degree_le
    ((natDegree_derivative_le F).trans (by omega)) ((natDegree_C_mul_le _ _).trans L8.le)
  have M8 : M.coeff 8=0 := by
    dsimp only [M,F]
    rw [coeff_add,coeff_derivative,bubble_derivative_top L8.le,coeff_C_mul]
    push_cast
    simp only [L, coeff_C_mul]
    ring
  have M7 : M.natDegree≤7 := strip_top Md M8
  have Mo : OrdinaryThrough M 7 := by
    intro R rd
    have RP : R.derivative.natDegree≤6 := (natDegree_derivative_le _).trans (by omega)
    have low : integral 0 1 (F*R.derivative)=0 := by
      dsimp only [F]
      rw [Ld,show bubble K*(C a*D)*R.derivative=C a*(bubble K*D*R.derivative) by ring,
        integral_C_mul,orth R.derivative RP,mul_zero]
    have bp := formal_parts (0:K) 1 F R
    have v₀ : F.eval 0=0 := by simp [F,bubble]
    have v₁ : F.eval 1=0 := by simp [F,bubble]
    rw [low,add_zero,v₀,v₁,zero_mul,zero_mul,sub_zero] at bp
    rw [show M*R=F.derivative*R+C (72:K)*(L*R) by dsimp [M];ring,
      map_add,integral_C_mul,bp,Lo R rd,mul_zero,add_zero]
  have ode : F.derivative+C (72:K)*L=0 := ordinary_zero M7 Mo
  have L0 : L.eval 0=1 := by
    have normalized := LegendreModeEight.eq_polynomial (LegendreModeEight.centered_degree L8.le)
      (LegendreModeEight.centered_isMode ode) (LegendreModeEight.centered_at_one L1)
    have e := LegendreModeEight.centered_value (L:=L) (0:K)
    rw [normalized] at e
    norm_num [LegendreModeEight.value] at e
    exact e.symm
  exact ⟨L,⟨L8,L1,L0,Lo,⟨a,an,Ld⟩,ode⟩⟩

/-- Unweighted coefficient extraction without an orthogonal table. -/
theorem integral_mul_of_top {L : K[X]} (L8 : L.natDegree=8) (orth : OrdinaryThrough L 7)
    {G : K[X]} (g8 : G.natDegree≤8) (a : K) (top : G.coeff 8=a*L.coeff 8) :
    integral 0 1 (L*G)=a*integral 0 1 (L^2) := by
  let R := G-C a*L
  have R8 : R.natDegree≤8 := natDegree_sub_le_of_le g8 ((natDegree_C_mul_le _ _).trans L8.le)
  have z8 : R.coeff 8=0 := by simp only [R,coeff_sub,coeff_C_mul,top,sub_self]
  have r7 : R.natDegree≤7 := strip_top R8 z8
  have z := orth R r7
  rw [show L*R=L*G-C a*L^2 by dsimp [R];ring,map_sub,integral_C_mul] at z
  exact sub_eq_zero.mp z

end
end RKCert.ReviewedNative.UnitBubbleLobatto

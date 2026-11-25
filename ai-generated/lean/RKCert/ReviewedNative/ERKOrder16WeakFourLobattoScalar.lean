module

public import RKCert.ReviewedNative.UnitBubbleLobattoShape
public import RKCert.ReviewedNative.FiveNodalDiagonal
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourLobatto

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.UnitBubbleMoments
open RKCert.ReviewedNative.UnitBubbleLobatto
open RKCert.ReviewedNative.LegendreEnergy
open RKCert.ReviewedNative.FiveNodalDiagonal
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Mass (Q : K[X]) (y a : Fin 5→K) : Prop :=
  ∀ R : K[X], R.natDegree≤11 → integral 0 1 (Q*R)=∑ i,a i*R.eval (y i)

/-- Division by no unknown weight or nodal factor: use a genuine
degree-four Lagrange indicator at a known paid label. -/
theorem mass_of_erased_nodal {Q : K[X]} {y a : Fin 5→K}
    (simple : Function.Injective y) (paid : Mass Q y a) (i : Fin 5) :
    integral 0 1 (Q*Lagrange.nodal (Finset.univ.erase i) y)=a i*slope y i := by
  classical
  let M := Lagrange.nodal (Finset.univ.erase i) y
  let s := slope y i
  let U := C s⁻¹*M
  have d : M.natDegree≤4 := by
    dsimp only [M]
    rw [Lagrange.natDegree_nodal,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin]
  have ud : U.natDegree≤11 := (natDegree_C_mul_le _ _).trans (d.trans (by decide))
  have sn : s≠0 := slope_ne_zero simple i
  have self : M.eval (y i)=s :=
    (Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i)).symm
  have ui : U.eval (y i)=1 := by
    simp only [U,eval_mul,eval_C,self,inv_mul_cancel₀ sn]
  have outside (j : Fin 5) (ji : j≠i) : U.eval (y j)=0 := by
    have e : M.eval (y j)=0 :=
      Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨ji,Finset.mem_univ j⟩)
    simp only [U,eval_mul,e,mul_zero]
  have sum : (∑ j,a j*U.eval (y j))=a i := by
    calc
      _ = a i*U.eval (y i) :=
        Finset.sum_eq_single i (fun j _ ji=>by rw [outside j ji,mul_zero])
          (fun e=>(e (Finset.mem_univ i)).elim)
      _ = _ := by rw [ui,mul_one]
  have p := paid U ud
  rw [show Q*U=C s⁻¹*(Q*M) by dsimp [U];ring,integral_C_mul,sum] at p
  change integral 0 1 (Q*M)=a i*s
  calc
    _ = s*(s⁻¹*integral 0 1 (Q*M)) := by rw [←mul_assoc,mul_inv_cancel₀ sn,one_mul]
    _ = _ := by rw [p];ring

private theorem factor_top {G : K[X]} {d : ℕ} (gd : G.natDegree≤d) (r : K) :
    ((X-C r)*G).coeff (d+1)=G.coeff d := by
  rw [sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (gd.trans_lt (Nat.lt_succ_self d)),mul_zero,sub_zero]

/-- Denominator-free Lobatto normalization. G is literally the
quotient of the true knot product at a displayed root, and no full
splitting or numerical location of other roots is required. -/
theorem primitive_on_node_quotient
    {L G : K[X]} (lend : L.natDegree=8) (lo : OrdinaryThrough L 7)
    (ode : ((bubble K)*L.derivative).derivative+C (72:K)*L=0)
    (g8 : G.natDegree≤8) {r μ : K}
    (factor : (X-C r)*G=C μ*((bubble K)*L.derivative)) :
    L.eval r*integral 0 1 G=-(17:K)*μ*integral 0 1 (L^2) := by
  let F := (bubble K)*L.derivative
  have row : G.coeff 8=(-(8:K)*μ)*L.coeff 8 := by
    have v := congrArg (fun U : K[X]=>U.coeff 9) factor
    rw [factor_top g8 r,coeff_C_mul,bubble_derivative_top lend.le] at v
    linear_combination v
  have lhs := integral_mul_of_top lend lo g8 (-(8:K)*μ) row
  have root : (L-C (L.eval r)).IsRoot r := by simp [IsRoot.def]
  obtain ⟨T,rep⟩ := dvd_iff_isRoot.mpr root
  have d : T.natDegree≤7 := by
    by_cases tn : T=0
    · simp [tn]
    · have bound : (L-C (L.eval r)).natDegree≤8 := natDegree_sub_le_of_le (p := L) (q := C (L.eval r)) lend.le (by rw [natDegree_C])
      rw [rep,natDegree_mul (X_sub_C_ne_zero _) tn,natDegree_X_sub_C] at bound
      omega
  have tCoeff : T.coeff 7=L.coeff 8 := by
    have v := congrArg (fun U : K[X]=>U.coeff 8) rep
    rw [factor_top d r] at v
    simpa [coeff_sub,coeff_C] using v.symm
  let V := formalPrimitive T
  have v8 : V.natDegree≤8 := (natDegree_formalPrimitive_le T).trans (Nat.succ_le_succ d)
  have vCoeff : V.coeff 8=((1:K)/8)*L.coeff 8 := by
    have v := congrArg (fun U : K[X]=>U.coeff 7) (derivative_formalPrimitive T)
    change V.derivative.coeff 7=T.coeff 7 at v
    rw [coeff_derivative,tCoeff] at v
    norm_num at v
    linear_combination ((1:K)/8)*v
  have vPair := integral_mul_of_top lend lo v8 ((1:K)/8) vCoeff
  have fp : F.derivative=-(C (72:K)*L) := by
    change F.derivative+C (72:K)*L=0 at ode
    linear_combination ode
  have fv0 : F.eval 0=0 := by simp [F,bubble]
  have fv1 : F.eval 1=0 := by simp [F,bubble]
  have right : integral 0 1 (F*T)=9*integral 0 1 (L^2) := by
    have p := formal_parts (0:K) 1 F V
    rw [fp,show V.derivative=T from derivative_formalPrimitive _,
      show -(C (72:K)*L)*V=-(C (72:K)*(L*V)) by ring,
      map_neg,integral_C_mul,vPair,fv0,fv1,zero_mul,zero_mul,sub_zero] at p
    linarith only [p]
  have product : G*(L-C (L.eval r))=C μ*(F*T) := by
    rw [rep]
    calc
      _ = ((X-C r)*G)*T := by ring
      _ = _ := by rw [factor];dsimp only [F];ring
  have want : integral 0 1 (G*(L-C (L.eval r)))=
      9*μ*integral 0 1 (L^2) := by
    rw [product,integral_C_mul,right]
    ring
  rw [show G*(L-C (L.eval r))=L*G-C (L.eval r)*G by ring,
    map_sub,integral_C_mul,lhs] at want
  linear_combination -want

/-- The exact three independent geometric properties of the actual
chart reduce to this pure scalar five-label contradiction. -/
theorem five_paid_diagonal_impossible {Q H : K[X]} {y a : Fin 5→K}
    (qn : Q≠0) (qd : Q.natDegree≤4) (hd : H.natDegree≤2)
    (simple : Function.Injective y) (zero : ∃ i,y i=0) (one : ∃ i,y i=1)
    (paid : Mass Q y a) (diagonal : ∀ i, H.eval (y i)=(a i*slope y i)^2) : False := by
  classical
  let N := nodal y
  let F := N*Q
  have N5 : N.natDegree=5 := by simp [N,nodal,Lagrange.natDegree_nodal]
  have Nn : N≠0 := by intro e;rw [e,natDegree_zero] at N5;omega
  have Fn : F≠0 := mul_ne_zero Nn qn
  have F9 : F.natDegree≤9 := natDegree_mul_le_of_le N5.le qd
  have node (i : Fin 5) : N.eval (y i)=0 := Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  obtain ⟨i₀,y₀⟩ := zero
  obtain ⟨i₁,y₁⟩ := one
  have F0 : F.eval 0=0 := by
    calc
      F.eval 0 = F.eval (y i₀) := congrArg F.eval y₀.symm
      _ = 0 := by dsimp only [F]; rw [eval_mul,node,zero_mul]
  have F1 : F.eval 1=0 := by dsimp only [F]; rw [←y₁,eval_mul,node,zero_mul]
  obtain ⟨D,DF⟩ := factor_unit_endpoints F F0 F1
  have Dn : D≠0 := by intro e;apply Fn;rw [DF,e,mul_zero]
  have d7 : D.natDegree≤7 := by
    rw [DF,natDegree_mul bubble_nz Dn,bubble_deg] at F9
    omega
  have bits : OrthogonalThrough D 6 := by
    intro R rd
    have b : (N*R).natDegree≤11 := natDegree_mul_le_of_le N5.le rd
    have h := paid (N*R) b
    have s : (∑ i,a i*(N*R).eval (y i))=0 :=
      Finset.sum_eq_zero (fun i _=>by rw [eval_mul,node,zero_mul,mul_zero])
    rw [s,show Q*(N*R)=F*R by dsimp [F];ring,DF] at h
    exact h
  have D7 : D.natDegree=7 := degree_eq_succ Dn d7 bits (by decide)
  obtain ⟨L,B⟩ := normalizedMode_of_bubble D7 bits
  obtain ⟨c,cn,cd⟩ := B.derivativeScale
  let μ := c⁻¹
  have mn : μ≠0 := inv_ne_zero cn
  have Fc : F=C μ*((bubble K)*L.derivative) := by
    have u : C μ*C c=(1:K[X]) := by rw [←map_mul,show μ*c=1 from inv_mul_cancel₀ cn,map_one]
    rw [DF,cd,show C μ*(bubble K*(C c*D))=(C μ*C c)*(bubble K*D) by ring,u,one_mul]
  have Ln : L≠0 := by intro e;have h:=B.output;rw [e,eval_zero] at h;exact zero_ne_one h
  have ip : 0 < integral 0 1 (L^2) := unit_integral_pos (pow_ne_zero 2 Ln)
    ((natDegree_pow_le_of_le 2 B.degree.le).trans_lt (by decide))
    (fun x _=>by simpa only [eval_pow] using sq_nonneg (L.eval x))
  let v := -(17:K)*μ*integral 0 1 (L^2)
  have vn : v≠0 := mul_ne_zero (mul_ne_zero (by norm_num) mn) ip.ne'
  let h := v^2
  have hn : h≠0 := pow_ne_zero 2 vn
  have prod (i : Fin 5) : H.eval (y i)*L.eval (y i)^2=h := by
    let Ni := Lagrange.nodal (Finset.univ.erase i) y
    let G := Q*Ni
    have ed : Ni.natDegree≤4 := by
      dsimp only [Ni]
      rw [Lagrange.natDegree_nodal,Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ,Fintype.card_fin]
    have g8 : G.natDegree≤8 := natDegree_mul_le_of_le qd ed
    have fac : (X-C (y i))*G=F := by
      have n := Lagrange.nodal_eq_mul_nodal_erase (v:=y) (Finset.mem_univ i)
      change N=(X-C (y i))*Ni at n
      dsimp only [F,G]
      rw [n]
      ring
    have g := primitive_on_node_quotient B.degree B.orthogonal B.equation g8 (fac.trans Fc)
    have mass := mass_of_erased_nodal simple paid i
    rw [diagonal]
    calc
      _ = (L.eval (y i)*integral 0 1 G)^2 := by
        change _ = (L.eval (y i)*integral 0 1 (Q*Ni))^2
        rw [mass]
        ring
      _ = _ := by rw [g]
  have H0 : H.eval 0=h := by simpa only [y₀,B.origin,one_pow,mul_one] using prod i₀
  have H1 : H.eval 1=h := by simpa only [y₁,B.output,one_pow,mul_one] using prod i₁
  obtain ⟨J,rep⟩ := factor_unit_endpoints (H-C h) (by simp [H0]) (by simp [H1])
  have J0 : J.natDegree=0 := by
    by_cases e : J=0
    · simp [e]
    · have d : (H-C h).natDegree≤2 := natDegree_sub_le_of_le (p := H) (q := C h) hd (by rw [natDegree_C])
      rw [rep,natDegree_mul bubble_nz e,bubble_deg] at d
      omega
  let k := J.coeff 0
  have shape : H=C h+C k*bubble K := by
    rw [eq_C_of_natDegree_eq_zero J0] at rep
    change H-C h=bubble K*C k at rep
    linear_combination rep
  have neq : i₁≠i₀ := by
    intro e
    have bad : (1:K)=0 := y₁.symm.trans ((congrArg y e).trans y₀)
    exact one_ne_zero bad
  let S := ((Finset.univ : Finset (Fin 5)).erase i₀).erase i₁
  have cnt : S.card=3 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨neq,Finset.mem_univ i₁⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i₀),Finset.card_univ,Fintype.card_fin]
  let e : Fin 3 ≃ ↥S := Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_coe,cnt])
  let r (i : Fin 3) := y (e i).val
  have inj : Function.Injective r := fun i j h=>e.injective (Subtype.ext (simple h))
  have droot (i : Fin 3) : D.eval (r i)=0 := by
    have mem := (e i).property
    have off₁ : (e i).val≠i₁ := (Finset.mem_erase.mp mem).1
    have off₀ : (e i).val≠i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp mem).2).1
    have r0 : r i≠0 := fun h=>off₀ (simple (h.trans y₀.symm))
    have r1 : r i≠1 := fun h=>off₁ (simple (h.trans y₁.symm))
    have w : F.eval (r i)=0 := by dsimp only [F]; rw [eval_mul,node,zero_mul]
    rw [DF,eval_mul] at w
    have U : (bubble K).eval (r i)≠0 := by
      simp only [bubble,eval_mul,eval_sub,eval_X,eval_one]
      exact mul_ne_zero r0 (sub_ne_zero.mpr r1.symm)
    exact (mul_eq_zero.mp w).resolve_left U
  have inside (i : Fin 3) : 0<r i ∧ r i<1 := by
    obtain ⟨R,hr⟩ := dvd_iff_isRoot.mpr (show D.IsRoot (r i) from droot i)
    exact (quotient_interior_simple Dn D7 bits (by decide) hr).1
  have critical (i : Fin 3) : L.derivative.eval (r i)=0 := by
    rw [cd,eval_mul,droot i,mul_zero]
  have vals (i : Fin 3) : 1=L.eval (r i)^2*(1+(k/h)*r i*(1-r i)) := by
    have v := prod (e i).val
    change H.eval (r i)*L.eval (r i)^2=h at v
    rw [shape] at v
    simp only [bubble,eval_add,eval_mul,eval_sub,eval_C,eval_one,eval_X] at v
    have bump : (1+(k/h)*r i*(1-r i))*h=h+k*(r i*(1-r i)) := by
      field_simp [hn] <;> ring
    have u : (L.eval (r i)^2*(1+(k/h)*r i*(1-r i)))*h=1*h := by
      rw [mul_assoc,bump,one_mul]
      linear_combination v
    exact (mul_right_cancel₀ hn u).symm
  exact LegendreModeEight.not_shifted_three_critical_common_factor B.degree.le B.equation
    B.output r inj inside critical (k/h) vals

end
end RKCert.ReviewedNative.WeakFourLobatto

module

public import RKCert.ReviewedNative.ERKOrder16WeakFourLobattoScalar
public import RKCert.ReviewedNative.LegendreModeEightChord
public import RKCert.ReviewedNative.NodalOddDiagonal
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
open RKCert.ReviewedNative.UnitBubbleMoments RKCert.ReviewedNative.UnitBubbleLobatto
open RKCert.ReviewedNative.LegendreEnergy RKCert.ReviewedNative.FiveNodalDiagonal
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure FivePaidMode (y a : Fin 5→K) (L : K[X]) (h : K) : Prop where
  degree : L.natDegree=8
  ode : ((X*(1-X))*L.derivative).derivative+C (72:K)*L=0
  atZero : L.eval 0=1
  atOne : L.eval 1=1
  hne : h≠0
  values : ∀ i, (a i*slope y i)^2*L.eval (y i)^2=h
  interior : ∀ i, y i≠0 → y i≠1 → 0<y i ∧ y i<1 ∧ L.derivative.eval (y i)=0

/-- The mass reconstruction, independent of which physical groups later
supply a diagonal. In particular the mass at a doubled group is not
assumed to square to that group's matrix diagonal. -/
theorem exists_five_paid_mode {Q : K[X]} {y a : Fin 5→K}
    (qn : Q≠0) (qd : Q.natDegree≤4) (simple : Function.Injective y)
    (zero : ∃ i,y i=0) (one : ∃ i,y i=1) (paid : Mass Q y a) :
    ∃ L : K[X], ∃ h : K, FivePaidMode y a L h := by
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
  have prod (i : Fin 5) : (a i*slope y i)^2*L.eval (y i)^2=h := by
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
    calc
      _ = (L.eval (y i)*integral 0 1 G)^2 := by
        change _ = (L.eval (y i)*integral 0 1 (Q*Ni))^2
        rw [mass]
        ring
      _ = _ := by rw [g]
  refine ⟨L,h,⟨B.degree,B.equation,B.origin,B.output,hn,prod,?_⟩⟩
  intro i n0 n1
  have w : F.eval (y i)=0 := by dsimp only [F]; rw [eval_mul,node,zero_mul]
  rw [DF,eval_mul] at w
  have ub : (bubble K).eval (y i)≠0 := by
    simp only [bubble,eval_mul,eval_sub,eval_X,eval_one]
    exact mul_ne_zero n0 (sub_ne_zero.mpr n1.symm)
  have dr : D.eval (y i)=0 := (mul_eq_zero.mp w).resolve_left ub
  obtain ⟨R,hr⟩ := dvd_iff_isRoot.mpr (show D.IsRoot (y i) from dr)
  obtain ⟨inside,_⟩ := quotient_interior_simple Dn D7 bits (by decide) hr
  exact ⟨inside.1,inside.2,by rw [cd,eval_mul,dr,mul_zero]⟩

theorem FivePaidMode.crit_sq_lt_one {y a : Fin 5→K} {L : K[X]} {h : K}
    (M : FivePaidMode y a L h) {i : Fin 5} (di : L.derivative.eval (y i)=0) :
    L.eval (y i)^2<1 := by
  have b := LegendreModeEight.critical_sq_lt_quarter
    (LegendreModeEight.centered_degree M.degree.le)
    (LegendreModeEight.centered_isMode M.ode)
    (LegendreModeEight.centered_at_one M.atOne)
    (LegendreModeEight.centered_critical di)
  rw [LegendreModeEight.centered_value] at b
  linarith only [b]

theorem FivePaidMode.eval_ne_zero {y a : Fin 5→K} {L : K[X]} {h : K}
    (M : FivePaidMode y a L h) (i : Fin 5) : L.eval (y i)≠0 := by
  intro e
  have m := M.values i
  rw [e,zero_pow (by decide : (2:ℕ)≠0),mul_zero] at m
  exact M.hne m.symm

private theorem linear_root_shape (F : K[X]) (d : F.natDegree≤1) {r : K}
    (root : F.eval r=0) : ∃ k : K, F=C k*(X-C r) := by
  obtain ⟨J,Jr⟩ := dvd_iff_isRoot.mpr (show F.IsRoot r from root)
  have j0 : J.natDegree=0 := by
    by_cases z : J=0
    · simp [z]
    · rw [Jr,natDegree_mul (X_sub_C_ne_zero _) z,natDegree_X_sub_C] at d
      omega
  refine ⟨J.coeff 0,?_⟩
  rw [eq_C_of_natDegree_eq_zero j0] at Jr
  exact Jr.trans (mul_comm _ _)

private theorem index_three {i0 i1 : Fin 5} (ne : i1≠i0) :
    ∃ f : Fin 3→Fin 5, Function.Injective f ∧
      (∀ i, f i≠i0 ∧ f i≠i1) ∧ (∀ j, j≠i0 → j≠i1 → ∃ i, f i=j) := by
  classical
  let S := ((Finset.univ : Finset (Fin 5)).erase i0).erase i1
  have cnt : S.card=3 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne,Finset.mem_univ i1⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i0),Finset.card_univ,Fintype.card_fin]
  let e : Fin 3 ≃ ↥S := Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_coe,cnt])
  refine ⟨fun i=>(e i).val,fun i j h=>e.injective (Subtype.ext h),?_,?_⟩
  · intro i
    have hi := Finset.mem_erase.mp (e i).property
    exact ⟨(Finset.mem_erase.mp hi.2).1,hi.1⟩
  · intro j h0 h1
    let z : ↥S := ⟨j,Finset.mem_erase.mpr ⟨h1,Finset.mem_erase.mpr ⟨h0,Finset.mem_univ _⟩⟩⟩
    exact ⟨e.symm z,congrArg Subtype.val (e.apply_symm_apply z)⟩

/-- Scaling the common positive nodal value: an affine comparison of
secants is forced without dividing by a tap or a nodal displacement. -/
private theorem scale_of_cross {h k B T P S : K} (kn : k≠0) (den : 1-P≠0)
    (identity : (h+k*T)*P=h) (fact : B=T*S) :
    B*P/(1-P)=(h/k)*S := by
  have hc : k*T*P=h*(1-P) := by linear_combination identity
  apply (div_eq_iff den).mpr
  apply mul_left_cancel₀ kn
  rw [fact]
  calc
    _ = S*(k*T*P) := by ring
    _ = S*(h*(1-P)) := by rw [hc]
    _ = _ := by rw [show k*((h/k)*S*(1-P))=S*(h*(1-P)) by
      field_simp [kn] <;> ring]

/-- Exactly one group may contain two real physical rows. At that group
no diagonal value is prescribed. -/
theorem five_paid_repeated_group_impossible {Q H : K[X]} {y a : Fin 5→K} (bad : Fin 5)
    (qn : Q≠0) (qd : Q.natDegree≤4) (hd : H.natDegree≤1)
    (simple : Function.Injective y) (zero : ∃ i,y i=0) (one : ∃ i,y i=1)
    (paid : Mass Q y a)
    (diag : ∀ i, i≠bad → H.eval (y i)=(a i*slope y i)^2) : False := by
  classical
  obtain ⟨L,h,M⟩ := exists_five_paid_mode qn qd simple zero one paid
  obtain ⟨j0,e0⟩ := zero
  obtain ⟨j1,e1⟩ := one
  have ne : j1≠j0 := fun e=>one_ne_zero (e1.symm.trans ((congrArg y e).trans e0))
  obtain ⟨f,fi,off,enum⟩ := index_three ne
  let z (i : Fin 3) := y (f i)
  have zi : Function.Injective z := fun _ _ h=>fi (simple h)
  have interior (i : Fin 3) : 0<z i ∧ z i<1 ∧ L.derivative.eval (z i)=0 :=
    M.interior _ (fun e=>(off i).1 (simple (e.trans e0.symm)))
      (fun e=>(off i).2 (simple (e.trans e1.symm)))
  have val (j : Fin 5) (hj : j≠bad) : H.eval (y j)*L.eval (y j)^2=h := by
    rw [diag j hj]
    exact M.values j
  have H0 (j : j0≠bad) : H.eval 0=h := by simpa only [e0,M.atZero,one_pow,mul_one] using val j0 j
  have H1 (j : j1≠bad) : H.eval 1=h := by simpa only [e1,M.atOne,one_pow,mul_one] using val j1 j
  have ch : (C h).natDegree ≤ 1 := (natDegree_C h).trans_le (Nat.zero_le 1)
  have deg : (H - C h).natDegree ≤ 1 := natDegree_sub_le_of_le hd ch
  have contradiction (j : Fin 3) (ev : H.eval (z j)=h) (good : f j≠bad) : False := by
    have v := val (f j) good
    change H.eval (z j)*L.eval (z j)^2=h at v
    rw [ev] at v
    have v' : h*L.eval (z j)^2=h*1 := by simpa only [mul_one] using v
    have d : L.eval (z j)^2=1 := mul_left_cancel₀ M.hne v'
    exact (M.crit_sq_lt_one (i:=f j) (interior j).2.2).ne d
  have atEnd (ell : K) (el : ell=0 ∨ ell=1)
      (on : H.eval ell=h) (good : ∀ i, f i≠bad) : False := by
    obtain ⟨k,hr⟩ := linear_root_shape (H-C h) deg (r:=ell) (by simp [on])
    have ep (x : K) : H.eval x=h+k*(x-ell) := by
      have g := congrArg (Polynomial.eval x) hr
      simp only [eval_sub,eval_C,eval_mul,eval_X] at g
      linarith only [g]
    have kn : k≠0 := by
      intro e
      exact contradiction 0 (by rw [ep,e,zero_mul,add_zero]) (good 0)
    have cross (i : Fin 3) : (h+k*(z i-ell))*L.eval (z i)^2=h := by
      rw [←ep]
      exact val (f i) (good i)
    have pos (i : Fin 3) : 1-L.eval (z i)^2≠0 :=
      sub_ne_zero.mpr (M.crit_sq_lt_one (i:=f i) (interior i).2.2).ne'
    rcases el with rfl|rfl
    · apply LegendreModeEight.no_shifted_critical_scale_affine M.degree.le M.ode M.atOne
        z zi (fun i=>⟨(interior i).1,(interior i).2.1⟩) (fun i=>(interior i).2.2) (h/k) (-(h/k))
      intro i
      calc
        _ = (h/k)*(1-z i) :=
          scale_of_cross kn (pos i) (cross i) (by ring)
        _ = _ := by ring
    · apply LegendreModeEight.no_shifted_critical_scale_affine M.degree.le M.ode M.atOne
        z zi (fun i=>⟨(interior i).1,(interior i).2.1⟩) (fun i=>(interior i).2.2) 0 (-(h/k))
      intro i
      calc
        _ = (h/k)*(-z i) :=
          scale_of_cross kn (pos i) (cross i) (by ring)
        _ = _ := by ring
  by_cases b0 : j0=bad
  · exact atEnd 1 (Or.inr rfl) (H1 (fun e=>ne (e.trans b0.symm)))
      (fun i e=>(off i).1 (e.trans b0.symm))
  by_cases b1 : j1=bad
  · exact atEnd 0 (Or.inl rfl) (H0 b0) (fun i e=>(off i).2 (e.trans b1.symm))
  obtain ⟨k,hr⟩ := linear_root_shape (H-C h) deg (r:=0) (by simp [H0 b0])
  have kn : k=0 := by
    have g := congrArg (Polynomial.eval (1:K)) hr
    simpa [H1 b1] using g.symm
  have const (i : Fin 3) : H.eval (z i)=h := by
    have g := congrArg (Polynomial.eval (z i)) hr
    simpa [kn,sub_eq_zero] using g
  by_cases f0 : f 0=bad
  · exact contradiction 1 (const 1)
      (fun e=>(by decide : (1:Fin 3)≠0) (fi (e.trans f0.symm)))
  · exact contradiction 0 (const 0) f0

private theorem six_slope {y : Fin 5→K} (ξ : K) (i : Fin 5) :
    NodalOddDiagonal.slope (Fin.cases ξ y) i.succ=(y i-ξ)*slope y i := by
  have f : NodalOddDiagonal.nodal (Fin.cases ξ y)=(X-C ξ)*nodal y := by
    simp [NodalOddDiagonal.nodal,nodal,Lagrange.nodal,Fin.prod_univ_succ]
  dsimp only [NodalOddDiagonal.slope,slope]
  rw [f,derivative_mul,eval_add,eval_mul,eval_mul]
  change ((X-C ξ).derivative).eval (y i)*(nodal y).eval (y i)+
      (X-C ξ).eval (y i)*(nodal y).derivative.eval (y i)=_
  rw [show (nodal y).eval (y i)=0 from Lagrange.eval_nodal_at_node (Finset.mem_univ i),
    mul_zero,zero_add,eval_sub,eval_X,eval_C]

/-- A sixth distinct numerical node with zero original mass. Its actual
diagonal zero is used, not inferred merely from a vanished grouped sum. -/
theorem five_paid_with_zero_mass_extra_impossible {Q H : K[X]} {y a : Fin 5→K} {ξ : K}
    (qn : Q≠0) (qd : Q.natDegree≤4) (hd : H.natDegree≤3)
    (simple : Function.Injective y) (zero : ∃ i,y i=0) (one : ∃ i,y i=1)
    (paid : Mass Q y a) (off : ∀ i, y i≠ξ)
    (extra : H.eval ξ=0)
    (diag : ∀ i, H.eval (y i)=(a i*NodalOddDiagonal.slope (Fin.cases ξ y) i.succ)^2) :
    False := by
  classical
  obtain ⟨L,h,M⟩ := exists_five_paid_mode qn qd simple zero one paid
  obtain ⟨H1,rep⟩ := dvd_iff_isRoot.mpr (show H.IsRoot ξ from extra)
  have h1d : H1.natDegree≤2 := by
    by_cases e : H1=0
    · simp [e]
    · rw [rep,natDegree_mul (X_sub_C_ne_zero _) e,natDegree_X_sub_C] at hd
      omega
  have val (i : Fin 5) : H1.eval (y i)*L.eval (y i)^2=h*(y i-ξ) := by
    have e := diag i
    rw [rep,eval_mul,eval_sub,eval_X,eval_C,six_slope] at e
    have ve : (y i-ξ)*(H1.eval (y i)*L.eval (y i)^2)=
        (y i-ξ)*(h*(y i-ξ)) := calc
      _ = ((y i-ξ)*H1.eval (y i))*L.eval (y i)^2 := by ring
      _ = (y i-ξ)^2*((a i*slope y i)^2*L.eval (y i)^2) := by rw [e];ring
      _ = _ := by rw [M.values i];ring
    exact mul_left_cancel₀ (sub_ne_zero.mpr (off i)) ve
  obtain ⟨j0,e0⟩ := zero
  obtain ⟨j1,e1⟩ := one
  have ne : j1≠j0 := fun e=>one_ne_zero (e1.symm.trans ((congrArg y e).trans e0))
  have H0 : H1.eval 0=h*(0-ξ) := by simpa only [e0,M.atZero,one_pow,mul_one] using val j0
  have H1o : H1.eval 1=h*(1-ξ) := by simpa only [e1,M.atOne,one_pow,mul_one] using val j1
  obtain ⟨J,rJ⟩ := factor_unit_endpoints (H1-C h*(X-C ξ)) (by simp [H0]) (by simp [H1o])
  have J0 : J.natDegree=0 := by
    by_cases e : J=0
    · simp [e]
    · have rl : (X - C ξ).natDegree ≤ 2 := (natDegree_X_sub_C ξ).trans_le (by decide : (1 : ℕ) ≤ 2)
      have cl : (C h * (X - C ξ)).natDegree ≤ 2 := (natDegree_C_mul_le h (X - C ξ)).trans rl
      have bound : (H1 - C h * (X - C ξ)).natDegree ≤ 2 := natDegree_sub_le_of_le h1d cl
      rw [rJ,natDegree_mul bubble_nz e,bubble_deg] at bound
      omega
  let k := J.coeff 0
  have shape : H1=C h*(X-C ξ)+C k*bubble K := by
    rw [eq_C_of_natDegree_eq_zero J0] at rJ
    change H1-C h*(X-C ξ)=bubble K*C k at rJ
    linear_combination rJ
  obtain ⟨f,fi,fo,_⟩ := index_three ne
  let z (i : Fin 3) := y (f i)
  have zi : Function.Injective z := fun _ _ h=>fi (simple h)
  have interior (i : Fin 3) : 0<z i ∧ z i<1 ∧ L.derivative.eval (z i)=0 :=
    M.interior _ (fun e=>(fo i).1 (simple (e.trans e0.symm)))
      (fun e=>(fo i).2 (simple (e.trans e1.symm)))
  have cross (i : Fin 3) :
      k*(z i*(1-z i))*L.eval (z i)^2=h*(z i-ξ)*(1-L.eval (z i)^2) := by
    have v := val (f i)
    change H1.eval (z i)*L.eval (z i)^2=h*(z i-ξ) at v
    rw [shape] at v
    simp only [bubble,eval_add,eval_mul,eval_sub,eval_C,eval_X,eval_one] at v
    linear_combination v
  have pos (i : Fin 3) : 1-L.eval (z i)^2≠0 :=
    sub_ne_zero.mpr (M.crit_sq_lt_one (i:=f i) (interior i).2.2).ne'
  have kn : k≠0 := by
    intro e
    have cc := cross 0
    rw [e,zero_mul,zero_mul] at cc
    exact (mul_ne_zero (mul_ne_zero M.hne (sub_ne_zero.mpr (off (f 0)))) (pos 0)) cc.symm
  apply LegendreModeEight.no_shifted_critical_scale_affine M.degree.le M.ode M.atOne
    z zi (fun i=>⟨(interior i).1,(interior i).2.1⟩) (fun i=>(interior i).2.2) (-(h/k)*ξ) (h/k)
  intro i
  apply (div_eq_iff (pos i)).mpr
  apply mul_left_cancel₀ kn
  calc
    _ = h*(z i-ξ)*(1-L.eval (z i)^2) := by rw [←cross i];ring
    _ = _ := by field_simp [kn] <;> ring

end
end RKCert.ReviewedNative.WeakFourLobatto

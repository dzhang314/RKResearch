module
public import RKCert.DirkQuinticFixed9
public import RKCert.DirkQuinticFixed10
public import RKCert.DirkQuinticLinear
public import RKCert.DirkQuinticPhysical
public import RKCert.DirkGridOmitted
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
@[expose] public section
namespace RKCert.DirkQuintic
open RKCert.FixedFactor Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]

/-- The exact scaled root-tuple certificate never reduces unknown tableau
coefficients or an unknown residual polynomial. -/
theorem specialization9
    (check:∀v:Fin 4→ZMod 10709,(∀i,v i∈grid9) → (∀i j:Fin 4,i≠j → v i≠v j) → zEval test v≠0)
    (w:Fin 4→K) (roots:∀i,((X-1)*lobatto 9).eval (w i)=0) (inj:Function.Injective w) :
    obstruction (w 0) (w 1) (w 2) (w 3)≠0 :=by
  have r(i:Fin 4):(integral9.map (Int.castRingHom K)).eval (4862*w i)=0:=by
    have e:=scale_eqn9 (w i)
    rw [roots i,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have D:=split_prime_root_tuple 10709 integral9 monic_scaled9 grid9 split_scaled9
    (fun z hz=>by rw [split_scaled9];exact simple_product_of_nodup grid9 (by decide) hz)
    test (fun i j:Fin 4=>i≠j) check (fun i=>4862*w i) r
    (fun i j ij e=>ij (inj (mul_left_cancel₀ (by norm_num : (4862:K)≠0) e)))
  rw [eval_test,obstruction_scale] at D
  exact (mul_ne_zero_iff.mp D).2

/-- The exact scaled root-tuple certificate never reduces unknown tableau
coefficients or an unknown residual polynomial. -/
theorem specialization10
    (check:∀v:Fin 4→ZMod 15727,(∀i,v i∈grid10) → (∀i j:Fin 4,i≠j → v i≠v j) → zEval test v≠0)
    (w:Fin 4→K) (roots:∀i,((X-1)*lobatto 10).eval (w i)=0) (inj:Function.Injective w) :
    obstruction (w 0) (w 1) (w 2) (w 3)≠0 :=by
  have r(i:Fin 4):(integral10.map (Int.castRingHom K)).eval (16796*w i)=0:=by
    have e:=scale_eqn10 (w i)
    rw [roots i,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have D:=split_prime_root_tuple 15727 integral10 monic_scaled10 grid10 split_scaled10
    (fun z hz=>by rw [split_scaled10];exact simple_product_of_nodup grid10 (by decide) hz)
    test (fun i j:Fin 4=>i≠j) check (fun i=>16796*w i) r
    (fun i j ij e=>ij (inj (mul_left_cancel₀ (by norm_num : (16796:K)≠0) e)))
  rw [eval_test,obstruction_scale] at D
  exact (mul_ne_zero_iff.mp D).2

theorem fixed_native_exclusion {m s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} [IsAlgClosed K]
    (hm:m=9 ∨ m=10) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    (dg:((X-1)*lobatto (K:=K) m).natDegree=m+1)
    (sep:((X-1)*lobatto (K:=K) m).Separable)
    (gate:∀w:Fin 4→K,(∀i,((X-1)*lobatto m).eval (w i)=0) → Function.Injective w →
      obstruction (w 0) (w 1) (w 2) (w 3)≠0) : False :=by
  classical
  obtain ⟨Z,Q,u,zm,dz,divi,un,zu,dq,qn,paid,tests⟩:=fifth_grid_reduction hm ha ho he
  obtain ⟨v,vi,vu,gv,qv⟩:=omitted_grid_triple hm Z Q u dz zm divi zu dq paid dg (IsAlgClosed.splits _) sep
  have gu:((X-1)*lobatto m).eval u=0:=by
    obtain ⟨H,e⟩:=divi;rw [e,eval_mul,zu,zero_mul]
  let w:Fin 4→K:=![v 0,v 1,v 2,u]
  have rootw(i:Fin 4):((X-1)*lobatto m).eval (w i)=0:=by
    fin_cases i <;> first | exact gv 0 | exact gv 1 | exact gv 2 | exact gu
  have nv (i j:Fin 3) (ij:i≠j):v i≠v j:=fun e=>ij (vi e)
  have inj:Function.Injective w:=by
    intro x y e
    fin_cases x <;> fin_cases y <;> first
      | rfl
      | exact False.elim (nv _ _ (by decide) e)
      | exact False.elim (vu _ e)
      | exact False.elim (vu _ e.symm)
  apply qn
  exact quintic_of_nonsingular (nv 0 1 (by decide)) (nv 0 2 (by decide)) (nv 1 2 (by decide)) un
    (qv 0) (qv 1) (qv 2) dq tests (gate w rootw inj)

/-- Base change is applied only to pass to a splitting field for the physical
grid. A counterexample over the original field would give one there. -/
theorem from_fixed_grid {m s:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
    (hm:m=9 ∨ m=10) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (dg:((X-1)*lobatto (K:=AlgebraicClosure K) m).natDegree=m+1)
    (sep:((X-1)*lobatto (K:=AlgebraicClosure K) m).Separable)
    (gate:∀w:Fin 4→AlgebraicClosure K,(∀i,((X-1)*lobatto m).eval (w i)=0) → Function.Injective w →
      obstruction (w 0) (w 1) (w 2) (w 3)≠0) :
    3*m-2≤s :=by
  have old:=(even_floor (by rcases hm with rfl|rfl <;>decide) ha ho).1
  by_contra! short
  have pos:9≤m:=by rcases hm with rfl|rfl <;>decide
  cases s with
  | zero=>omega
  | succ s=>
    have eqn:s+1+3=3*m:=by omega
    let φ:K→+*AlgebraicClosure K:=algebraMap K (AlgebraicClosure K)
    exact fixed_native_exclusion hm (lowerTriangular_map ha φ) (ho.map φ) eqn dg sep gate
end RKCert.DirkQuintic


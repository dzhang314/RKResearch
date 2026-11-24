module
public import RKCert.ERKFiniteKnots

@[expose] public section

/-! # Native primitive tests and coefficient adapters at the actual knots -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 1200000

structure KnotPair (P G:K[X]) (q:ℕ) (u v:K) : Prop where
  u_ne : u≠0
  v_ne : v≠0
  different : v≠u
  u_head : P.eval u≠0
  v_head : P.eval v≠0
  u_mesh : G.eval u=0
  v_mesh : G.eval v=0
  first : ∀ k<q-5,(Paired.primitive (X^k*(X*P))).eval u=0
  second : ∀ k<q-6,(Paired.primitive (X^k*(X*(X-C u)*P))).eval v=0

theorem actual_two_knots {s q ε d a r:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
    {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
    (ha:StrictLower A) (hq:8≤q) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) (Pr:Profile A q a U w G P) :
    ∃ u v:K, KnotPair P G q u v := by
  obtain ⟨i,_,_,G₁,n₁,h₁⟩:=physical_knot ha hq S M C Pr (X:K[X]) X_ne_zero (by rw [natDegree_X];omega)
  let u:=nodes A i
  have u0 : u≠0 := by
    intro e
    apply n₁
    change (X*P).eval u=0
    simp [e]
  have pu : P.eval u≠0 := by
    intro e
    apply n₁
    change (X*P).eval u=0
    simp [e]
  let Q : K[X] := X*(X-Polynomial.C u)
  have qn : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)
  have qd : Q.natDegree=2 := by
    dsimp [Q]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨j,_,_,G₂,n₂,h₂⟩:=physical_knot ha hq S M C Pr Q qn (by rw [qd];omega)
  let v:=nodes A j
  have nz : v*(v-u)*P.eval v≠0 := by simpa [Q,v] using n₂
  have v0 : v≠0 := by intro hh;apply nz;simp [hh]
  have vu : v≠u := by intro hh;apply nz;simp [hh]
  have vp : P.eval v≠0 := by intro hh;apply nz;simp [hh]
  refine ⟨u,v,⟨u0,v0,vu,pu,vp,G₁,G₂,?_,?_⟩⟩
  · intro k hk
    exact h₁ (X^k) (by rw [natDegree_X_pow,natDegree_X];omega)
  · intro k hk
    exact h₂ (X^k) (by rw [natDegree_X_pow,qd];omega)

theorem first_moment {P G:K[X]} {q n:ℕ} {u v:K} (J:KnotPair P G q u v)
    (e:Fin n→K) (ep:Polynomial.ofFn n e=P) {k:ℕ} (hk:k<q-5) :
    moment e u (k+1)=0 := by
  have h := J.first k hk
  rw [←mul_assoc,←pow_succ] at h
  have h' := primitive_monomial_moment e u (k+1)
  rw [ep] at h'
  exact h'.symm.trans h

theorem second_moment {P G:K[X]} {q n:ℕ} {u v:K} (J:KnotPair P G q u v)
    (e:Fin n→K) (ep:Polynomial.ofFn n e=P) {k:ℕ} (hk:k<q-6) :
    moment e v (k+2)=u*moment e v (k+1) := by
  have h := J.second k hk
  have ee : X^k*(X*(X-Polynomial.C u)*P)=X^(k+2)*P-u•(X^(k+1)*P) := by
    rw [←Polynomial.C_mul',pow_succ _ (k+1),pow_succ _ k]
    ring
  have p1 := primitive_monomial_moment e v (k+1)
  have p2 := primitive_monomial_moment e v (k+2)
  rw [ep] at p1 p2
  rw [ee,map_sub,map_smul,eval_sub,eval_smul,p1,p2,smul_eq_mul] at h
  exact sub_eq_zero.mp h

theorem endpoint_tests_three {P G:K[X]} {q n:ℕ} {u v:K} (J:KnotPair P G q u v) (hq:8≤q)
    (e:Fin n→K) (ep:Polynomial.ofFn n e=P) :
    EndpointPhysical.tests e u v 3 := by
  refine ⟨fun k=>first_moment J e ep (by have:=k.isLt;omega),?_,?_⟩
  · exact sub_eq_zero.mpr (second_moment J e ep (k:=0) (by omega))
  · exact sub_eq_zero.mpr (second_moment J e ep (k:=1) (by omega))

theorem q9_no_profile {P G:K[X]} {u v:K}
    (J:KnotPair P G 9 u v) (dP:P.natDegree≤4) : P=0 := by
  classical
  let e : Fin 5→K := fun k=>P.coeff k.val
  have eq:ofFn 5 e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have z : e=0 := physical_jacobi_gate (m:=4) (by decide) e u v J.u_ne J.v_ne J.different
    (fun k=>first_moment J e eq (by have:=k.isLt;omega))
    (fun k=>second_moment J e eq (by have:=k.isLt;omega))
  rw [←eq,z,map_zero]

theorem cubic_no_profile {P G:K[X]} {u v:K} {q:ℕ}
    (hq:8≤q) (J:KnotPair P G q u v) (dP:P.natDegree≤3) : P=0 := by
  classical
  let e : Fin 4→K := fun k=>P.coeff k.val
  have eq:ofFn 4 e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have z : e=0 := (EndpointPhysical.rescale_eq_zero_iff e J.u_ne).mp <|
    match3 _ _ (div_ne_zero J.v_ne J.u_ne)
      (fun h=>J.different ((div_eq_one_iff_eq J.u_ne).mp h))
      (EndpointPhysical.normalize J.u_ne (endpoint_tests_three J hq e eq))
  rw [←eq,z,map_zero]

end RKCert.Paired.FiniteMidpoint


module
public import RKCert.ERKOrderFifteenEarlyTerminal
public import RKCert.ERKOrderFifteenAliasGate
public import RKCert.ERKOrderFifteenPencil

@[expose] public section

/-! # Genuine explicit order fifteen requires twenty-three stages over ordered fields. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint RKCert.Paired.Clock RKCert.OneEscape Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s a : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G P : K[X]}

omit [CharZero K] in
theorem OddSevenChart.mesh_zero_off_core (C:OddSevenChart A 1 a 2 U w G)
    (i:Fin (s+1)) (on:¬Live U i) (wi:w i=0) : G.eval (nodes A i)=0 := by
  have h:=C.meshPaid
  rw [C.marked.edge] at h
  obtain ⟨v,hv,Q,_,e⟩:=exists_head_poly h
  have vi : v i=0 := by by_contra nz;exact on ⟨v,hv,nz⟩
  simpa [vi,wi] using e i

theorem fifteen_two_budget_square (ha:StrictLower A)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 1)
    (C:OddSevenChart A 1 a 2 U w G) (Pr:SevenProfile A 2 U w P)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤2) :
    ∃ i:Fin (s+1), ¬Live U i ∧ w i=0 ∧ (Q*P).eval (nodes A i)≠0 ∧
      ∀ J:K[X],J.natDegree+Q.natDegree≤2→(primitive (J*(Q*P))).eval (nodes A i)=0 := by
  have last : defectPlus A 1 7≤chain (diag (nodes A)) U w 4 := by
    rw [C.marked.paid 7 (by decide) (by decide)]
  exact physical_knot_of_paid (j:=6) (m:=2) (n:=4) ha S M C.marked Pr (by decide)
    (by have :=Pr.degree;omega) (C.marked.core.trans (Fplus_mono A 1 (by decide)))
    (marked_weighted_six C.marked) last Q qn qd

theorem order15_no_head_zero_at_origin (ha:StrictLower A)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 1)
    (C:OddSevenChart A 1 a 2 U w G) (Pr:SevenProfile A 2 U w P) :
    P.eval 0≠0 := by
  intro p0
  have dvd : (X:K[X])∣P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
  obtain ⟨R,eq⟩:=dvd
  have rn:R≠0 := fun h=>Pr.nonzero (by rw [eq,h,mul_zero])
  have rd:R.natDegree≤3 := by
    have h := Pr.degree
    rw [eq,natDegree_X_mul rn] at h
    omega
  obtain ⟨i,_,_,un,ht⟩:=fifteen_two_budget_square ha S M C Pr
    (1:K[X]) one_ne_zero (by simp)
  let u:=nodes A i
  have uz : u*R.eval u≠0 := by simpa [eq,u] using un
  have u0:u≠0 := fun h=>uz (by rw [h,zero_mul])
  have ru:R.eval u≠0 := fun h=>uz (by rw [h,mul_zero])
  let Q : K[X] := X-Polynomial.C u
  have qd:Q.natDegree=1 := natDegree_X_sub_C _
  have qn:Q≠0 := X_sub_C_ne_zero _
  obtain ⟨j,_,_,vn,vt⟩:=fifteen_two_budget_square ha S M C Pr Q qn (by omega)
  let v:=nodes A j
  have mask : Q*P=X*(X-Polynomial.C u)*R := by rw [eq];unfold Q;ring
  have nz : v*(v-u)*R.eval v≠0 := by simpa [mask,v] using vn
  have v0:v≠0 := fun h=>nz (by simp [h])
  have vu:v≠u := fun h=>nz (by simp [h])
  have rv:R.eval v≠0 := fun h=>nz (by simp [h])
  have J : KnotPair R (0:K[X]) 8 u v := by
    refine ⟨u0,v0,vu,ru,rv,eval_zero,eval_zero,?_,?_⟩
    · intro k hk
      have e:=ht (X^k) (by rw [natDegree_X_pow,natDegree_one];omega)
      simpa [eq] using e
    · intro k hk
      have e:=vt (X^k) (by rw [natDegree_X_pow,qd];omega)
      rwa [mask] at e
  exact rn (cubic_no_profile (by decide) J rd)

theorem actual_order15_early_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 1)
    (C:OddSevenChart A 1 a 2 U w G) (term:terminal (K:=K) s∈treeSpace A 8) : False := by
  obtain ⟨v,P,C',Pr,div,deg⟩:=early_fifteen_profile ha ho S M C term
  obtain ⟨i,on,wi,nx,tests⟩:=fifteen_two_budget_square ha S M C' Pr
    (X:K[X]) X_ne_zero (by simp)
  let u:=nodes A i
  have nz : u*P.eval u≠0 := by simpa [u] using nx
  have un:u≠0 := fun e=>nz (by rw [e,zero_mul])
  have pn:P.eval u≠0 := fun e=>nz (by rw [e,mul_zero])
  have gu : G.eval u=0 := C'.mesh_zero_off_core i on wi
  have m1 : (primitive (X*P)).eval u=0 := by
    simpa only [one_mul] using tests (1:K[X]) (by simp)
  rcases C'.chartType with a7|⟨a6,_⟩
  · have m2 : (primitive (X*(X*P))).eval u=0 := tests X (by simp)
    have nn := order15_no_head_zero_at_origin ha S M C' Pr
    exact variable_fifteen_pencil_gate C'.mesh (by have :=C'.meshDegree;omega)
      (by omega) div nn un pn gu m1 m2
  · have C6 : OddSevenChart A 1 6 2 U v G := a6 ▸ C'
    exact C6.alias_first_moment P div (by omega) un gu m1

end RKCert.Paired.FiniteMidpoint

namespace RKCert
open RKCert.Paired RKCert.Paired.FiniteMidpoint

/-- Backend certificate in the original-tree representation. The public
reviewed RKResearch statement is supplied by the single project bridge. -/
theorem explicit_order_fifteen_at_least_twenty_three {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15) : 23≤s := by
  by_contra! small
  cases s with
  | zero =>
    have le := explicit_order_le_stages ha ho
    omega
  | succ s =>
    obtain ⟨_,_,_,_,S,M,C,t⟩:=order15_only_early_terminal ha ho (by omega)
    exact actual_order15_early_impossible ha ho S M C t

end RKCert

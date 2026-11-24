module
public import RKCert.ERKFiniteChart
public import RKCert.ERKFiniteShifts

@[expose] public section

/-! # Exactly affordable polynomial leakage packets -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.OneEscape RKCert.Paired.Clock Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s q ε d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

omit [CharZero K] in
inductive Ghost (P:K[X]) : ℕ→ℕ→ℕ→ℕ→Prop
  | even8 (t:K) (eq:P=t • even6) : Ghost P 8 0 0 8
  | even9 (eq:P=0) : Ghost P 9 0 0 9
  | full8 (t:K) (eq:P=t • odd7) : Ghost P 8 1 0 8
  | full9 (eq:P=0) : Ghost P 9 1 0 9
  | prefix8 (t u:K) (eq:P=t • dx6 + u • dx7) : Ghost P 8 1 1 8
  | prefix9 (t:K) (eq:P=t • dx8) : Ghost P 9 1 1 9
  | alias8 (t u:K) (eq:P=t • dx5 + u • dx6) : Ghost P 8 1 1 7
  | alias9 (t:K) (eq:P=t • dx7) : Ghost P 9 1 1 8

theorem get_ghost (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:q=8∨q=9)
    (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    {G:K[X]} (C:Chart A q ε d a r U w G) (P:K[X])
    (hd:P.natDegree≤a) (hP:evalNodes A P∈defectPlus A d (10+(q-a)))
    (hl:ε=0→P.eval 1=0) : Ghost P q ε d a := by
  have hzero:=marked_eval_origin ha (by have := S.size;omega) P hP
  have hdeg:P.natDegree≤10+(q-a) := by have := C.aLe;omega
  have htype: (ε=0 ∧ d=0 ∧ a=q) ∨ (ε=1 ∧ d=0 ∧ a=q) ∨
      (ε=1 ∧ d=1 ∧ a=q) ∨ (ε=1 ∧ d=1 ∧ a=q-1) := by
    have ht:=M.budget
    rcases C.chartType with h|h <;> omega
  rcases htype with ⟨hε,hd',ha'⟩|⟨hε,hd',ha'⟩|⟨hε,hd',ha'⟩|⟨hε,hd',ha'⟩
  · subst ε
    subst d
    subst a
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,h⟩:= ghostEven8_decode P hd hzero (hl rfl) (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P hP hdeg (by omega))
      exact .even8 t h
    · have h:= ghostEven9_decode P hd hzero (hl rfl) (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P hP hdeg (by omega))
      exact .even9 h
  · subst ε
    subst d
    subst a
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,h⟩:= ghostFull8_decode P hd hzero (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P hP hdeg (by omega))
      exact .full8 t h
    · have h:= ghostFull9_decode P hd hzero (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P hP hdeg (by omega))
      exact .full9 h
  · subst ε
    subst d
    subst a
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,u,h⟩:= ghostPrefix8_decode P hd hzero (fun k => by
        have := k.isLt
        exact marked_moment_difference ho P hP hdeg M.atOne (by omega))
      exact .prefix8 t u h
    · obtain ⟨t,h⟩:= ghostPrefix9_decode P hd hzero (fun k => by
        have := k.isLt
        exact marked_moment_difference ho P hP hdeg M.atOne (by omega))
      exact .prefix9 t h
  · subst ε
    subst d
    subst a
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,u,h⟩:= ghostAlias8_decode P hd hzero (fun k => by
        have := k.isLt
        exact marked_moment_difference ho P hP hdeg M.atOne (by omega))
      exact .alias8 t u h
    · obtain ⟨t,h⟩:= ghostAlias9_decode P hd hzero (fun k => by
        have := k.isLt
        exact marked_moment_difference ho P hP hdeg M.atOne (by omega))
      exact .alias9 t h

omit [CharZero K] in
theorem mesh_comb_low {P Q R:K[X]} {t u:K} (h:P=t•Q+u•R)
    (hqr:Q.natDegree<R.natDegree) (hd:P.natDegree≤Q.natDegree) : P=t•Q := by
  have hu:u=0 := by
    by_contra hn
    have qd := natDegree_smul_le t Q
    have rd := natDegree_smul R hn
    rw [h,natDegree_add_eq_right_of_natDegree_lt (by rw [rd];omega),rd] at hd
    omega
  simpa only [hu,zero_smul,add_zero] using h

omit [CharZero K] in
theorem diff_clock_degree (P Q:K[X]) (n:ℕ) (hp:P.natDegree≤n) (hq:Q.natDegree≤n) :
    ((X:K[X])*P-Q).natDegree≤n+1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_mul_le).trans (by rw [natDegree_X];omega)
  · omega

theorem ghost_cancel {P Q R:K[X]}
    (h0:Ghost P q ε d a) (h1:Ghost Q q ε d a) (h2:Ghost R q ε d a)
    (d0:P.natDegree≤a) (d1:Q.natDegree≤a) (d2:R.natDegree≤a)
    (m0:Mesh (X*P-Q) q ε d) (m1:Mesh (X*Q-R) q ε d) : P=0 := by
  cases h0 with
  | even8 t hp=>
    cases h1 with | even8 v hq =>
      cases m0 with | even8 m hm =>
        rw [hp,hq] at hm
        have z := shiftEven8 t v m hm
        simp [hp,z]
  | even9 hp=>exact hp
  | full8 t hp=>
    cases h1 with | full8 v hq =>
      cases m0 with | full8 m hm =>
        rw [hp,hq] at hm
        have z := shiftFull8 t v m hm
        simp [hp,z]
  | full9 hp=>exact hp
  | prefix8 t u hp=>
    cases h1 with | prefix8 v v' hq =>
      cases h2 with | prefix8 z y hr =>
        cases m0 with | prefix8 m n hm =>
          cases m1 with | prefix8 m' n' hn =>
            rw [hp,hq] at hm
            rw [hq,hr] at hn
            obtain ⟨z0,z1⟩ := shiftPrefix8 t u v v' z y m n m' n' hm hn
            simp [hp,z0,z1]
  | prefix9 t hp=>
    cases h1 with | prefix9 v hq =>
      cases m0 with | prefix9 m n hm =>
        rw [hp,hq] at hm
        have z := shiftPrefix9 t v m n hm
        simp [hp,z]
  | alias8 t u hp=>
    cases h1 with | alias8 v v' hq =>
      cases h2 with | alias8 z y hr =>
        cases m0 with | prefix8 m n hm =>
          cases m1 with | prefix8 m' n' hn =>
            have hm' := mesh_comb_low hm (by rw [dx7_degree,dx8_degree];decide)
              (by rw [dx7_degree]; exact diff_clock_degree P Q _ d0 d1)
            have hn' := mesh_comb_low hn (by rw [dx7_degree,dx8_degree];decide)
              (by rw [dx7_degree]; exact diff_clock_degree Q R _ d1 d2)
            rw [hp,hq] at hm'
            rw [hq,hr] at hn'
            obtain ⟨z0,z1⟩ := shiftAlias8 t u v v' z y m m' hm' hn'
            simp [hp,z0,z1]
  | alias9 t hp=>
    cases h1 with | alias9 v hq =>
      cases m0 with | prefix9 m n hm =>
        have hm' := mesh_comb_low hm (by rw [dx8_degree,dx9_degree];decide)
          (by rw [dx8_degree]; exact diff_clock_degree P Q _ d0 d1)
        rw [hp,hq] at hm'
        have z := shiftAlias9 t v m hm'
        simp [hp,z]

end RKCert.Paired.FiniteMidpoint


module
public import RKCert.ERKFiniteMarkedMoments
public import RKCert.ERKFinitePackets

@[expose] public section

/-! # Actual midpoint root mesh and uniquely possible alias -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint RKCert.OneEscape RKCert.Paired.Clock Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s p q ε d : ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

omit [CharZero K] in
theorem tail_zero_iff {j : ℕ} {v:Vec K (s+1)} :
    v∈defectPlus A 0 j ↔ v∈zeroSpace A j := by simp [defectPlus, tailPlane]

theorem firstEscape_last_zero (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (hq:8≤q) (S:Saturated A b q 0) {v:Vec K (s+1)} (hv:v∈firstEscape A 0 q) :
    v (Fin.last s)=0 := by
  have hm : v∈zeroSpace A q⊔(zeroSpace A q).map (diag (nodes A)) := by
    simpa [firstEscape,tailPlane] using hv
  obtain ⟨u,hu,_,⟨w,hw,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hm
  rw [Pi.add_apply,diag_apply,even_last_zero ha ho hq S _ hu,even_last_zero ha ho hq S _ hw,mul_zero,add_zero]

omit [CharZero K] in
inductive Mesh (P:K[X]) : ℕ → ℕ → ℕ → Prop
  | even8 (t:K) (cert : P=t • even7) : Mesh P 8 0 0
  | even9 (t:K) (cert : P=t • even8) : Mesh P 9 0 0
  | full8 (t:K) (cert : P=t • odd8) : Mesh P 8 1 0
  | full9 (t:K) (cert : P=t • odd9) : Mesh P 9 1 0
  | prefix8 (t u:K) (cert : P=t • dx7 + u • dx8) : Mesh P 8 1 1
  | prefix9 (t u:K) (cert : P=t • dx8 + u • dx9) : Mesh P 9 1 1

theorem get_mesh (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq : q=8 ∨ q=9) (he : ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (P:K[X]) (hd : P.natDegree≤q+1) (hP : evalNodes A P∈firstEscape A d q) :
    Mesh P q ε d := by
  have hzero := marked_eval_origin ha (by have := S.size;omega) P (firstEscape_defect hP)
  have de : d≤ε := by have := M.budget;omega
  have ht : ε=0 ∨ (ε=1 ∧ d=0) ∨ (ε=1 ∧ d=1) := by omega
  rcases ht with he'|⟨he',hd'⟩|⟨he',hd'⟩
  · have hd' : d=0 := by omega
    subst ε
    subst d
    have ho':HasTreeOrderAtLeast A b (2*q) := by simpa using ho
    have hl := firstEscape_last_zero ha ho' (by omega) S hP
    have hv := (even_terminal_column ha ho' (by omega) S).1
    have h1:P.eval 1=0 := by simpa only [evalNodes_apply,hv] using hl
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,hg⟩ := meshEven8_decode P hd hzero h1  (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P (firstEscape_defect hP) hd (by omega))
      exact .even8 t hg
    · obtain ⟨t,hg⟩ := meshEven9_decode P hd hzero h1  (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P (firstEscape_defect hP) hd (by omega))
      exact .even9 t hg
  · subst ε
    subst d
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,hg⟩ := meshFull8_decode P hd hzero  (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P (firstEscape_defect hP) hd (by omega))
      exact .full8 t hg
    · obtain ⟨t,hg⟩ := meshFull9_decode P hd hzero  (fun k => by
        have := k.isLt
        exact marked_moment_zero ho P (firstEscape_defect hP) hd (by omega))
      exact .full9 t hg
  · subst ε
    subst d
    rcases hq with hq|hq <;> subst q
    · obtain ⟨t,u,hg⟩ := meshPrefix8_decode P hd hzero  (fun k => by
        have := k.isLt
        exact marked_moment_difference ho P (firstEscape_defect hP) hd M.atOne (by omega))
      exact .prefix8 t u hg
    · obtain ⟨t,u,hg⟩ := meshPrefix9_decode P hd hzero  (fun k => by
        have := k.isLt
        exact marked_moment_difference ho P (firstEscape_defect hP) hd M.atOne (by omega))
      exact .prefix9 t u hg

omit [CharZero K] in
theorem mesh_line_degree {P Q:K[X]} {t:K} (h:P=t•Q) (hn:P≠0) : P.natDegree=Q.natDegree := by
  have ht:t≠0:=by intro hz;apply hn;rw [h,hz,zero_smul]
  simpa only [h] using natDegree_smul Q ht

omit [CharZero K] in
theorem mesh_span_degree {P Q R:K[X]} {t u:K} (h:P=t•Q+u•R) (hqr:Q.natDegree<R.natDegree)
    (hd:P.natDegree≤Q.natDegree) (hn:P≠0) : P.natDegree=Q.natDegree := by
  by_cases hu:u=0
  · apply mesh_line_degree (t:=t) _ hn
    simpa only [hu,zero_smul,add_zero] using h
  · have qd := natDegree_smul_le t Q
    have rd := natDegree_smul R hu
    rw [h,natDegree_add_eq_right_of_natDegree_lt (by rw [rd];omega),rd] at hd
    omega

theorem mesh_alias {P:K[X]} (h:Mesh P q ε d) (hd:P.natDegree≤q) (hn:P≠0) :
    d=1 ∧ P.natDegree=q := by
  cases h with
  | even8 t hg => have eq:= (mesh_line_degree hg hn).trans even7_degree; omega
  | even9 t hg => have eq:= (mesh_line_degree hg hn).trans even8_degree; omega
  | full8 t hg => have eq:= (mesh_line_degree hg hn).trans odd8_degree; omega
  | full9 t hg => have eq:= (mesh_line_degree hg hn).trans odd9_degree; omega
  | prefix8 t u hg =>
      refine ⟨rfl,?_⟩
      apply (mesh_span_degree hg (by rw [dx7_degree,dx8_degree];decide) (by rwa [dx7_degree]) hn).trans dx7_degree
  | prefix9 t u hg =>
      refine ⟨rfl,?_⟩
      apply (mesh_span_degree hg (by rw [dx8_degree,dx9_degree];decide) (by rwa [dx8_degree]) hn).trans dx8_degree

end RKCert.Paired.FiniteMidpoint


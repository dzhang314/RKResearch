module
public import RKCert.DirkTwoReverse
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ} {A:Fin (s+1)→Fin (s+1)→K}
variable {b v:Vec K (s+1)}
noncomputable section

theorem rev_coefficient_moment {d:ℕ} {Q:K[X]} (hQ:Q.natDegree≤d) (x:K) (k:ℕ) :
    (formalPrimitive (X^k*Q)).eval x=moment (toFn (d+1) Q) x k := by
  classical
  let e:=toFn (d+1) Q
  have eq:ofFn (d+1) e=Q:=ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  calc
    _ = (formalPrimitive (X^k*(ofFn (d+1) e))).eval x := congrArg (fun H:K[X] => (formalPrimitive (X^k*H)).eval x) eq.symm
    _ = _ := by rw [formalPrimitive_eq_treePrimitive,primitive_monomial_moment]

theorem profile_native_moments (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {d j:ℕ} (lo:2≤j) (hi:j+4≤m) {Q:K[X]} (hd:Q.natDegree≤d) (hQ:Q≠0) {θ:Vec K (s+1)}
    (h:ReverseTrace A b (2*m) j θ Q) (active:∀i,θ i≠0 → b i≠0 ∧ tau A b i=0) :
    ∃i l:Fin (s+1), let u:=mirror A i; let v:=mirror A l; let e:=toFn (d+1) Q
      b i≠0 ∧ tau A b i=0 ∧ b l≠0 ∧ tau A b l=0 ∧
      u≠0 ∧ v≠0 ∧ v≠u ∧
      (∀ k:ℕ,j+k+2≤m → moment e u (k+1)=0) ∧
      (∀ k:ℕ,j+k+3≤m → moment e v (k+2)=u*moment e v (k+1)) := by
  obtain ⟨i,l,bi,τi,bl,τl,ui,ul,lu,_,_,h1,h2⟩:=
    native_two_reverse hm ha ho he non lo hi hQ h active
  exact ⟨i,l,bi,τi,bl,τl,ui,ul,lu,fun k hk=>by simpa only [rev_coefficient_moment hd] using h1 k hk,
    fun k hk=>by simpa only [rev_coefficient_moment hd] using h2 k hk⟩

omit [CharZero K] in
private theorem both_hidden {q:K[X]} (fit:∀i,tau A b i≠0 → v i=q.eval (mirror A i))
    (off:∀i,tau A b i=0 → b i*v i=0) (hq:q=0) : b*v=0 ∧ tau A b*v=0 := by
  have on (i) (hi:tau A b i≠0) : v i=0 := by simpa [hq] using fit i hi
  constructor <;> ext i
  · by_cases h:tau A b i=0
    · exact off i h
    · simp [on i h]
  · by_cases h:tau A b i=0
    · simp [h]
    · simp [on i h]

/-- The nonlocal cubic port is invisible on both the scalar weight and cubic
reverse-word support at *all* attained native even boundaries. -/
theorem nonlocal_cubic_hidden (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    (hv:v∈zeroSpace A 3) : b*v=0 ∧ tau A b*v=0 := by
  classical
  obtain ⟨Q,hd,fit,off,θ,hθ,active⟩:=port_contrast hm ha ho he non (by decide) (by omega) hv
  apply both_hidden fit off
  by_contra hQ
  obtain ⟨i,l,_,_,_,_,hu,hv,hvu,first,second⟩:=
    profile_native_moments hm ha ho he non (by decide) (by omega) hd hQ hθ active
  let e:=toFn 4 Q
  let u:=mirror A i
  let z:=mirror A l
  have tests:EndpointPhysical.tests e u z 3 := ⟨fun k=>first k.val (by have :=k.isLt;omega),
    sub_eq_zero.mpr (second 0 (by omega)),sub_eq_zero.mpr (second 1 (by omega))⟩
  have hzero:e=0 := (EndpointPhysical.rescale_eq_zero_iff e hu).mp (Endpoint.match3 _ _
    (div_ne_zero hv hu) (fun h=>hvu ((div_eq_one_iff_eq hu).mp h)) (EndpointPhysical.normalize hu tests))
  have rep:ofFn 4 e=Q:=ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  exact hQ (by rw [←rep,hzero,map_zero])

/-- A generic cross-order hidden-support result. Every ordinary j-defect
in the nonlocal even boundary lies off b and τ as soon as the full Jacobi
tests are paid. This conclusion is about original coordinates, not removal. -/
theorem nonlocal_grade_hidden (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (jl:4≤j) (jh:2*j+1≤m) (hv:v∈zeroSpace A j) : b*v=0 ∧ tau A b*v=0 := by
  classical
  obtain ⟨Q,hd,fit,off,θ,hθ,active⟩:=port_contrast hm ha ho he non (by omega) (by omega) hv
  apply both_hidden fit off
  by_contra hQ
  obtain ⟨i,l,_,_,_,_,hu,hv,hvu,first,second⟩:=
    profile_native_moments hm ha ho he non (by omega) (by omega) hd hQ hθ active
  let e:=toFn (j+1) Q
  have hzero:e=0:=physical_jacobi_gate jl e (mirror A i) (mirror A l) hu hv hvu
    (fun k=>first k.val (by have:=k.isLt;omega)) (fun k=>second k.val (by have:=k.isLt;omega))
  have rep:ofFn (j+1) e=Q:=ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  exact hQ (by rw [←rep,hzero,map_zero])

/-- On the true 21-stage p16 chart the fixed-grid repair pays the otherwise
missing fourth first-site test. Thus *all* genuine F4 coordinates are jointly
invisible to b and τ in the nonlocal cubic branch, over any characteristic-zero
field, without assuming the two primitive tests or ordering the clock values. -/
theorem order16_nonlocal_quartic_hidden {T:Fin 21→Fin 21→K} {β f:Vec K 21}
    (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β 16)
    (non:¬(dirkBack T β 1).map (diag (mirror T))≤dirkBack T β 1) (hf:f∈zeroSpace T 4) :
    β*f=0 ∧ tau T β*f=0 := by
  classical
  obtain ⟨Q,hd,fit,off,θ,hθ,active⟩:=port_contrast (s:=20) (m:=8) (by decide) ha ho (by decide)
    non (by decide) (by decide) hf
  apply both_hidden fit off
  by_contra hQ
  obtain ⟨i,l,bi,τi,bl,τl,hu,hv,hvu,first,second⟩:=profile_native_moments (s:=20) (m:=8)
    (by decide) ha ho (by decide) non (by decide) (by decide) hd hQ hθ active
  obtain ⟨t,ct,_,gate⟩:=order16_boundary_clean_quartic ha ho
  have not_t (a:Fin 21) (hh:mirror T a≠0) : a≠t := by
    rintro rfl
    exact hh (by change 1-nodes T a=0; rw [ct,sub_self])
  let e:=toFn 5 Q
  have clean (a:Fin 21) (ba:β a≠0) (ta:tau T β a=0) :
      ∀w∈zeroSpace T 7,w a=0 := fun w hw =>
    weighted_clean (s:=20) (m:=8) (by decide) ha ho (by decide) non a ba ta _
      (zeroSpace_mono T (by decide : 7≤8) hw)
  have tests:EndpointPhysical.tests e (mirror T i) (mirror T l) 3 :=
    ⟨fun k=>first k.val (by have:=k.isLt;omega),
      sub_eq_zero.mpr (second 0 (by decide)),sub_eq_zero.mpr (second 1 (by decide))⟩
  have hz:e=0:=gate i l (not_t _ hu) (not_t _ hv) (clean _ bi τi) (clean _ bl τl)
    (mirror T i) (mirror T l) rfl rfl hu hv hvu e tests
  have rep:ofFn 5 e=Q:=ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  exact hQ (by rw [←rep,hz,map_zero])

end
end RKCert.Paired.Terminal

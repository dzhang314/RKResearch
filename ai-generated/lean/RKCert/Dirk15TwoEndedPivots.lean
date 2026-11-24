module

public import RKCert.Dirk15PhysicalSignatures
public import RKCert.Dirk15NativePivots
public import RKCert.Dirk15RadauPorts

@[expose] public section

/-! # Chronological cut for the true two-ended order-fifteen certificate
The mixed-product geometric hypotheses are exposed. No determinant
nonvanishing or exclusion of the other native charts is asserted. -/
namespace RKCert.Paired
open RKCert.Endpoint RKCert.OneEscape Polynomial Signature
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20} {P D : K[X]}

/-- From a true paid quartic contrast, choose the earliest original nonzero
coordinate, not the earliest nonzero output weight. -/
theorem order15_forward_quartic_cut (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (T : PhysicalTerminal (s:=19) A b) (hP : P≠0) (dP : P.natDegree≤4)
    {θ : Vec K 20} (hθ : OrdinaryTrace A 4 θ P)
    (clean : ∀ i, i≠Fin.last 19 → (diag (nodes A) θ) i≠0 →
      P.eval (nodes A i)≠0 ∧ D.eval (nodes A i)=0 ∧ ∀ w∈zeroSpace A 7,w i=0) :
    ∃ i : Fin 20, i≠Fin.last 19 ∧ nodes A i≠0 ∧ P.eval (nodes A i)≠0 ∧
      D.eval (nodes A i)=0 ∧ A i i=0 ∧
      paidMoment P (nodes A i) 1=0 ∧ paidMoment P (nodes A i) 2=0 := by
  obtain ⟨j,hj,hx⟩ := hθ.nonterminal_clock_witness hP dP ho (by decide) (Fin.last 19) T.node_one
  have hv : diag (nodes A) θ≠0 := fun e => hx (congrFun e j)
  obtain ⟨i,hi,hpre⟩ := exists_first_coordinate hv
  have hnt : i≠Fin.last 19 := by
    intro he
    exact hx (hpre j (he ▸ lt_of_le_of_ne (Fin.le_last j) hj))
  have hc : nodes A i≠0 := fun e => hi (by simp [e])
  obtain ⟨hP',hD',hClean⟩ := clean i hnt hi
  obtain ⟨hdiag,h1,h2⟩ := hθ.clock.two_primitive_first_pivot
    ha ho (H:=7) (by decide) (by decide) hi hpre hClean
  exact ⟨i,hnt,hc,hP',hD',hdiag,h1,h2⟩

/-- The reverse pivot is active, cubic-clean and nonterminal. The hypothesis
linking its clock to D is only used after those exact properties are proved. -/
theorem order15_reverse_quartic_cut (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b) (hm : Module.finrank K (marked A 15 4)=2)
    (hfirst : ¬(markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3)
    (hP : P≠0) (dP : P.natDegree≤4) {v : Vec K 20} (hv : v∈zeroSpace A 4)
    (matchP : ∀ i, reverseCubic A b i≠0 → v i=P.eval (nodes A i))
    (clean : ∀ i, i≠Fin.last 19 → b i≠0 → v i=0 → P.eval (nodes A i)≠0 →
      D.eval (nodes A i)=0) :
    ∃ i : Fin 20, i≠Fin.last 19 ∧ mirror A i≠0 ∧ b i≠0 ∧ v i=0 ∧
      P.eval (nodes A i)≠0 ∧ D.eval (nodes A i)=0 ∧ A i i=0 ∧
      paidMoment (reflectPolynomial P) (mirror A i) 1=0 ∧
      paidMoment (reflectPolynomial P) (mirror A i) 2=0 := by
  let θ := weightedEval (nodes A) b P-b*v
  let Q := reflectPolynomial P
  have hQ : Q≠0 := by
    intro e
    apply hP
    rw [←reflectPolynomial_involutive P,show reflectPolynomial P=0 from e]
    simp [reflectPolynomial]
  have dQ : Q.natDegree≤4 := (reflectPolynomial_degree P).trans dP
  have hprofile : ReverseTrace A b 15 4 θ Q := by
    have H := (ReverseTrace.scalar A b (P:=Q) dQ).sub_pure
      (weights_mul_zeroSpace ho (by decide : 4+1≤15) hv)
    simpa only [weightedEval_reflect, Q, reflectPolynomial_involutive] using H
  obtain ⟨i,hi,hpre⟩ := exists_last_coordinate (hprofile.clock_witness ho hQ dQ (by decide))
  have hθi : θ i≠0 := fun e => hi (by simp [e])
  have hy : mirror A i≠0 := fun e => hi (by simp [e])
  have hnt : i≠Fin.last 19 := fun e => hy (e ▸ terminal_mirror_zero h.terminal)
  have hbi : b i≠0 := by
    intro e
    apply hθi
    simp [θ,e]
  have htt : reverseCubic A b i=0 := by
    by_contra hn
    apply hθi
    simp [θ,matchP i hn,mul_comm]
  obtain ⟨W,_,_,hzero⟩ := order15_grade_four_profile ha ho h hm hfirst hv
  have hvi := hzero i hbi htt
  have hP' : P.eval (nodes A i)≠0 := by
    intro e
    apply hθi
    simp [θ,hvi,e]
  have hclean (w : Vec K 20) (hw : w∈markedTerminalZero (s:=19) A 15 7) : w i=0 := by
    rw [order15_minimal_cubic_orbit ha ho h hfirst 7 (by decide) (by decide)] at hw
    obtain ⟨u,hu,R,_,he⟩ := Clock.exists_head_poly hw
    have hu0 : u=0 := by simpa using hu
    simpa only [hu0,Pi.zero_apply,htt,mul_zero,add_zero] using he i
  obtain ⟨hdiag,h1,h2⟩ := hprofile.clock (by decide : 4+2≤15) |>.two_primitive_last_pivot
    ha ho h.terminal (H:=7) (by decide) (by decide) hi hpre hbi hclean
  exact ⟨i,hnt,hy,hbi,hvi,hP',clean i hnt hbi hvi hP',hdiag,h1,h2⟩

/-- The non-divisor polynomial case necessarily yields two Gram equations,
one in each endpoint, for a single exact factor T of D up to reflection. -/
theorem two_ended_gram_of_mixed (D R S P : K[X])
    (hP : P≠0) (hS : S≠0) (dS : S.natDegree≤1) (dP : P.natDegree≤4)
    (he : D*S=P*R) (hno : ¬P∣D) {u y : K}
    (hu1 : paidMoment P u 1=0) (hu2 : paidMoment P u 2=0)
    (hy1 : paidMoment (reflectPolynomial P) y 1=0)
    (hy2 : paidMoment (reflectPolynomial P) y 2=0) :
    ∃ T : K[X], T≠0 ∧ T.natDegree≤3 ∧ P=S*T ∧ T∣D ∧
      paidMoment T u 1*paidMoment T u 3-(paidMoment T u 2)^2=0 ∧
      paidMoment (reflectPolynomial T) y 1*paidMoment (reflectPolynomial T) y 3-
        (paidMoment (reflectPolynomial T) y 2)^2=0 := by
  obtain ⟨T,hn,dT,hT,hdiv⟩ := affine_factor_from_mixed D R S P hP hS dS dP he hno
  have hR : reflectPolynomial P=reflectPolynomial S*reflectPolynomial T := by
    simp only [hT,reflectPolynomial,mul_comp]
  have hSr : reflectPolynomial S≠0 := by
    intro e
    apply hS
    rw [←reflectPolynomial_involutive S,e]
    simp [reflectPolynomial]
  exact ⟨T,hn,dT,hT,hdiv,
    affine_gram_zero S T hS dS u 1 (by rwa [←hT]) (by rwa [←hT]),
    affine_gram_zero (reflectPolynomial S) (reflectPolynomial T) hSr
      ((reflectPolynomial_degree S).trans dS) y 1 (by rwa [←hR]) (by rwa [←hR])⟩

end RKCert.Paired

module
public import RKCert.ERKFiniteLeakage
public import RKCert.CoreSupport

@[expose] public section

/-! # Physical one-head multiplier; signed weights and ties are retained -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
set_option maxHeartbeats 1500000
variable {K:Type*} [Field K] [CharZero K] {s q ε d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}

omit [CharZero K] in
theorem marked_power (H:MarkedHead A q d r U w) (hq:5≤q) {k:ℕ} (hk:k<r) :
    (diag (nodes A)^k) w∈defectPlus A d 5 := by
  have h := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) r).mp le_rfl
  simp only [H.paid 5 le_rfl hq,Nat.sub_self,Nat.add_zero]
  exact h.2 k hk

omit [CharZero K] in
theorem chart_count_ten (hq:8≤q) (C:Chart A q ε d a r U w G) :
    headLen q a r 10 < (headSites (nodes A) w).card := by
  have h:=chart_sites hq C
  have aLe:=C.aLe
  have aLo:=C.aLo
  unfold headLen at *
  omega

theorem marked_five_last (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:8≤q) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (hl:ε=0) {v:Vec K (s+1)} (hv:v∈defectPlus A d 5) : v (Fin.last s)=0 := by
  have hd:d=0 := by have := M.budget;omega
  subst ε
  subst d
  exact even_last_zero ha (by simpa using ho) hq S _ (zeroSpace_mono A (by omega) (tail_zero_iff.mp hv))

theorem core_times_five (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) {v:Vec K (s+1)} (hv:v∈defectPlus A d 5)
    {u:Vec K (s+1)} (hu:u∈U) : u*v∈U := by
  classical
  let c:=nodes A
  let D:=diag c
  have dec : u*v=∑ z∈sites c, fiber c z u*v := by rw [←Finset.sum_mul,sum_fibers]
  rw [dec]
  apply U.sum_mem
  intro z _
  have tstable (y : Vec K (s+1)) (hy:y∈U) : D y∈U :=
    C.marked.stable (show D y∈U.map (diag (nodes A)) from ⟨y,hy,rfl⟩)
  have fu : fiber c z u∈U := fiber_mem C.marked.stable z hu
  have hfu: fiber c z u∈defectPlus A d 5 := C.marked.core fu
  have f0 : fiber c z u * v∈defectPlus A d 10 :=
    Fplus_mul (A:=A) (d:=d) (j:=5) (k:=5) hfu hv
  have f1 : D (fiber c z u*v)∈defectPlus A d 10 := by
    have eq : D (fiber c z u*v)=(D (fiber c z u))*v := by ext i; simp [D,mul_assoc]
    rw [eq]
    have hd : D (fiber c z u)∈defectPlus A d 5 := C.marked.core (tstable _ fu)
    exact Fplus_mul (A:=A) (d:=d) (j:=5) (k:=5) hd hv
  have f2 : D (D (fiber c z u*v))∈defectPlus A d 10 := by
    have eq : D (D (fiber c z u*v))=(D (D (fiber c z u)))*v := by ext i; simp [D,mul_assoc]
    rw [eq]
    have hd : D (D (fiber c z u))∈defectPlus A d 5 := C.marked.core (tstable _ (tstable _ fu))
    exact Fplus_mul (A:=A) (d:=d) (j:=5) (k:=5) hd hv
  have hl (h:ε=0) : (fiber c z u*v) (Fin.last s)=0 := by
    rw [Pi.mul_apply,marked_five_last ha ho (by omega) S M h hv,mul_zero]
  have h := (leak_free ha ho hq he S M C f0 f1 f2 hl).1
  apply localized_mem (z:=z) C.marked.stable C.marked.norm (chart_count_ten (by omega) C) h
  intro i hzi
  change c i≠z at hzi
  simp [fiber,hzi]

theorem clean_head (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) :
    ∃ v:Vec K (s+1), Chart A q ε d a r U v G ∧ MulClosed U ∧
      ∀ i,Live U i→v i=0 := by
  have mulc : MulClosed U := fun _ hu _ hv => core_times_five ha ho hq he S M C (C.marked.core hv) hu
  have h5w : w∈defectPlus A d 5 := by
    simpa using marked_power C.marked (by omega) (k:=0) (by have := C.marked.rTwo;omega)
  obtain ⟨v,_,dis,eq⟩:=disjoint_head C.marked.stable mulc (fun u hu=>core_times_five ha ho hq he S M C h5w hu)
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    classical
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have e:=dis i ⟨_,hz,hn⟩
    simp [fiber,e] at hn
  have H : MarkedHead A q d r U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=> (C.marked.paid j hj hq).trans (eq _).symm,
      C.marked.edge.trans (eq _).symm,C.marked.edgeRank⟩
  refine ⟨v,⟨H,C.chartType,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩,mulc,dis⟩
  intro j hj hm
  unfold forwardBand
  rw [eq]
  exact C.chart j hj hm

theorem head_square_band (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) :
    ∀ k≤2*r-2,(diag (nodes A)^k) (w*w)∈forwardBand A q a r U w 10 := by
  let c:=nodes A
  let D:=diag c
  have rTwo:=C.marked.rTwo
  have powPaid (k:ℕ) (hk:k≤2*r-2) : (D^k) (w*w)∈defectPlus A d 10 := by
    let f:=min k (r-1)
    let g:=k-f
    have e:f+g=k := by dsimp [g];have hf:=min_le_left k (r-1);omega
    have hf:f<r := by dsimp [f];have := min_le_right k (r-1);omega
    have hg:g<r := by dsimp [g,f];omega
    have p1 : (D^f) w∈defectPlus A d 5 := marked_power C.marked (by omega) hf
    have p2 : (D^g) w∈defectPlus A d 5 := marked_power C.marked (by omega) hg
    have ee : (D^k) (w*w) = ((D^f) w)*((D^g) w) := by
      ext i
      simp only [D,pow_diag_apply,Pi.mul_apply]
      rw [←e,pow_add]
      ring
    rw [ee]
    exact Fplus_mul (A:=A) (d:=d) (j:=5) (k:=5) p1 p2
  have hw5 : w∈defectPlus A d 5 := by
    simpa using marked_power C.marked (by omega) (k:=0) (by omega)
  intro k hk
  let j:=min k (2*r-4)
  have ej:j≤k:=min_le_left .. 
  have ej2:j≤2*r-4:=min_le_right ..
  have last (h:ε=0) : ((D^j) (w*w)) (Fin.last s)=0 := by
    have z:=marked_five_last ha ho (by omega) S M h hw5
    simp [D,pow_diag_apply,z]
  have e1 : D ((D^j) (w*w))=(D^(j+1)) (w*w) := by rw [pow_succ'];rfl
  have e2 : D (D ((D^j) (w*w)))=(D^(j+2)) (w*w) := by
    calc
      _ = D ((D^(j+1)) (w*w)) := congrArg D e1
      _ = _ := by rw [show j+2=j+1+1 by omega,pow_succ' D (j+1)];rfl
  have hz := leak_free ha ho hq he S M C (powPaid j (by omega))
    (by rw [e1];exact powPaid _ (by omega)) (by rw [e2];exact powPaid _ (by omega)) last
  have choose : k=j ∨ k=j+1 ∨ k=j+2 := by dsimp [j] at *;omega
  change (D^k) (w*w)∈forwardBand A q a r U w 10
  rcases choose with e|e|e
  · rw [e];exact hz.1
  · rw [e,←e1];exact hz.2.1
  · rw [e,←e2];exact hz.2.2

omit [CharZero K] in
theorem weighted_sum {c v:Vec K (s+1)} (P:K[X]) :
    weightedEval c v P=∑ k∈P.support,P.coeff k • ((diag c^k) v) := by
  ext i
  rw [weightedEval_apply,eval_eq_sum,Polynomial.sum,Finset.sum_mul,Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul,pow_diag_apply,mul_assoc]

omit [CharZero K] in
theorem weighted_paid {c v:Vec K (s+1)} (P:K[X]) {Z:Submodule K (Vec K (s+1))}
    (h:∀ k∈P.support, (diag c^k) v∈Z) : weightedEval c v P∈Z := by
  rw [weighted_sum]
  exact Z.sum_mem (fun i hi=>Z.smul_mem _ (h i hi))

omit [CharZero K] in
theorem weighted_chain {c v:Vec K (s+1)} {n:ℕ} (P:K[X]) (hd:P.natDegree<n) :
    weightedEval c v P∈chain (diag c) U v n := by
  have mem:∀ k<n,(diag c^k) v∈chain (diag c) U v n := ((chain_le_iff n).mp le_rfl).2
  apply weighted_paid
  intro k hk
  exact mem _ ((le_natDegree_of_mem_supp k hk).trans_lt hd)

end RKCert.Paired.FiniteMidpoint


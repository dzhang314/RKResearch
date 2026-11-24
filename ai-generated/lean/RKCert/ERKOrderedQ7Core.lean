module
public import RKCert.ERKOrderedQ7Leakage
public import RKCert.ERKFiniteKnots

@[expose] public section

/-! # The actual q=7 core algebra and multiplier degree -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 1500000

omit [CharZero K] in
theorem even_seven_count_ten (C:EvenSevenChart A r U w G) :
    headLen 7 7 r 10 < (headSites (nodes A) w).card := by
  have := even_seven_sites C
  unfold headLen
  omega

theorem grade_five_last_seven (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) {v:Vec K (s+1)} (hv:v∈defectPlus A 0 5) : v (Fin.last s)=0 :=
  even_last_zero_short ha ho (by decide) S _ (zeroSpace_mono A (by decide) (tail_zero_iff.mp hv))

theorem seven_core_times_five (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (M:Margin A b 7 0 0)
    (C:EvenSevenChart A r U w G) {v:Vec K (s+1)} (hv:v∈defectPlus A 0 5)
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
  have hfu: fiber c z u∈defectPlus A 0 5 := C.marked.core fu
  have f0 : fiber c z u * v∈defectPlus A 0 10 :=
    Fplus_mul (A:=A) (d:=0) (j:=5) (k:=5) hfu hv
  have f1 : D (fiber c z u*v)∈defectPlus A 0 10 := by
    have eq : D (fiber c z u*v)=(D (fiber c z u))*v := by ext i; simp [D,mul_assoc]
    rw [eq]
    have hd : D (fiber c z u)∈defectPlus A 0 5 := C.marked.core (tstable _ fu)
    exact Fplus_mul (A:=A) (d:=0) (j:=5) (k:=5) hd hv
  have f2 : D (D (fiber c z u*v))∈defectPlus A 0 10 := by
    have eq : D (D (fiber c z u*v))=(D (D (fiber c z u)))*v := by ext i; simp [D,mul_assoc]
    rw [eq]
    have hd : D (D (fiber c z u))∈defectPlus A 0 5 := C.marked.core (tstable _ (tstable _ fu))
    exact Fplus_mul (A:=A) (d:=0) (j:=5) (k:=5) hd hv
  have hl : (fiber c z u*v) (Fin.last s)=0 := by
    rw [Pi.mul_apply,grade_five_last_seven ha ho S hv,mul_zero]
  have h := (even_seven_leak_free ha ho S M C f0 f1 f2 hl).1
  apply localized_mem (z:=z) C.marked.stable C.marked.norm (even_seven_count_ten C) h
  intro i hzi
  change c i≠z at hzi
  simp [fiber,hzi]

theorem clean_seven_head (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (M:Margin A b 7 0 0)
    (C:EvenSevenChart A r U w G) :
    ∃ v:Vec K (s+1), EvenSevenChart A r U v G ∧ MulClosed U ∧
      ∀ i,Live U i→v i=0 := by
  have mulc : MulClosed U := fun _ hu _ hv => seven_core_times_five ha ho S M C (C.marked.core hv) hu
  have h5w : w∈defectPlus A 0 5 := by
    simpa using marked_power C.marked (by omega) (k:=0) (by have := C.marked.rTwo;omega)
  obtain ⟨v,_,dis,eq⟩:=disjoint_head C.marked.stable mulc (fun u hu=>seven_core_times_five ha ho S M C h5w hu)
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    classical
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have e:=dis i ⟨_,hz,hn⟩
    simp [fiber,e] at hn
  have H : MarkedHead A 7 0 r U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=> (C.marked.paid j hj hq).trans (eq _).symm,
      C.marked.edge.trans (eq _).symm,C.marked.edgeRank⟩
  refine ⟨v,⟨H,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩,mulc,dis⟩
  intro j hj hm
  unfold SevenBand forwardBand
  rw [eq]
  exact C.chart j hj hm

theorem seven_square_band (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (M:Margin A b 7 0 0)
    (C:EvenSevenChart A r U w G) :
    ∀ k≤2*r-2,(diag (nodes A)^k) (w*w)∈SevenBand A r U w 10 := by
  let c:=nodes A
  let D:=diag c
  have rTwo:=C.marked.rTwo
  have powPaid (k:ℕ) (hk:k≤2*r-2) : (D^k) (w*w)∈defectPlus A 0 10 := by
    let f:=min k (r-1)
    let g:=k-f
    have e:f+g=k := by dsimp [g];have hf:=min_le_left k (r-1);omega
    have hf:f<r := by dsimp [f];have := min_le_right k (r-1);omega
    have hg:g<r := by dsimp [g,f];omega
    have p1 : (D^f) w∈defectPlus A 0 5 := marked_power C.marked (by omega) hf
    have p2 : (D^g) w∈defectPlus A 0 5 := marked_power C.marked (by omega) hg
    have ee : (D^k) (w*w) = ((D^f) w)*((D^g) w) := by
      ext i
      simp only [D,pow_diag_apply,Pi.mul_apply]
      rw [←e,pow_add]
      ring
    rw [ee]
    exact Fplus_mul (A:=A) (d:=0) (j:=5) (k:=5) p1 p2
  have hw5 : w∈defectPlus A 0 5 := by
    simpa using marked_power C.marked (by omega) (k:=0) (by omega)
  intro k hk
  let j:=min k (2*r-4)
  have ej:j≤k:=min_le_left .. 
  have ej2:j≤2*r-4:=min_le_right ..
  have last : ((D^j) (w*w)) (Fin.last s)=0 := by
    have z:=grade_five_last_seven ha ho S hw5
    simp [D,pow_diag_apply,z]
  have e1 : D ((D^j) (w*w))=(D^(j+1)) (w*w) := by rw [pow_succ'];rfl
  have e2 : D (D ((D^j) (w*w)))=(D^(j+2)) (w*w) := by
    calc
      _ = D ((D^(j+1)) (w*w)) := congrArg D e1
      _ = _ := by rw [show j+2=j+1+1 by omega,pow_succ' D (j+1)];rfl
  have hz := even_seven_leak_free ha ho S M C (powPaid j (by omega))
    (by rw [e1];exact powPaid _ (by omega)) (by rw [e2];exact powPaid _ (by omega)) last
  have choose : k=j ∨ k=j+1 ∨ k=j+2 := by dsimp [j] at *;omega
  change (D^k) (w*w)∈SevenBand A r U w 10
  rcases choose with e|e|e
  · rw [e];exact hz.1
  · rw [e,←e1];exact hz.2.1
  · rw [e,←e2];exact hz.2.2


structure SevenProfile (A:Fin (s+1)→Fin (s+1)→K) (r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (P:K[X]) : Prop where
  algebra : MulClosed U
  disjoint : ∀ i,Live U i→w i=0
  nonzero : P≠0
  degree : P.natDegree+r≤6
  repr : ∀ i,w i≠0→w i=P.eval (nodes A i)

theorem even_seven_profile (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (M:Margin A b 7 0 0) (C:EvenSevenChart A r U w G) :
    ∃ v P,EvenSevenChart A r U v G ∧ SevenProfile A r U v P := by
  classical
  obtain ⟨v,C,mulc,dis⟩:=clean_seven_head ha ho S M C
  have r2:=C.marked.rTwo
  have cn:=even_seven_count_ten C
  obtain ⟨P,pd,hP⟩:=multiplier_degree (a:=v) (d:=2*r-2) dis cn (seven_square_band ha ho S M C)
  have pn:P≠0 := by
    intro hz
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    exact hi' (by rw [hP _ hi',hz,eval_zero])
  have pdeg := pd.resolve_left pn
  unfold headLen at pdeg
  exact ⟨v,P,C,⟨mulc,dis,pn,by omega,hP⟩⟩

end RKCert.Paired.FiniteMidpoint

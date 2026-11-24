module
public import RKCert.ERKOrderFifteenLeakage
public import RKCert.ERKOrderedQ7Core

@[expose] public section

/-! # Pure order-15 physical heads and large-r degree bounds -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d a r : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G P : K[X]}

omit [CharZero K] in
theorem OddSevenChart.ten_count (C:OddSevenChart A d a r U w G) :
    headLen 7 a r 10<(headSites (nodes A) w).card := by
  have c := C.sites
  have e := C.aLe
  unfold headLen at c ⊢
  omega

theorem fifteen_core_times_five (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d)
    (C:OddSevenChart A d a r U w G) {v : Vec K (s+1)} (hv:v∈defectPlus A d 5)
    {u : Vec K (s+1)} (hu:u∈U) : u*v∈U := by
  let c:=nodes A
  let D:=diag c
  have e : u*v=∑ z∈sites c,fiber c z u*v := by rw [←Finset.sum_mul,sum_fibers]
  rw [e]
  apply U.sum_mem
  intro z _
  have fu : fiber c z u∈U := fiber_mem C.marked.stable z hu
  have huD (i:ℕ) : (D^i) (fiber c z u)∈U := by
    induction i with
    | zero => simpa only [pow_zero,one_apply_eq_self] using fu
    | succ i ih =>
      rw [pow_succ',mul_apply_eq_comp]
      exact C.marked.stable (Submodule.mem_map_of_mem ih)
  have costs (i:ℕ) : (D^i) (fiber c z u*v)∈defectPlus A d 10 := by
    have fit : (D^i) (fiber c z u*v)=(D^i) (fiber c z u)*v := by
      ext j
      simp only [D,pow_diag_apply,Pi.mul_apply,mul_assoc]
    rw [fit]
    exact Fplus_mul (j:=5) (k:=5) (C.marked.core (huD i)) hv
  have pure := C.leak_free_ten ha ho S M (fun i _=>costs i)
  apply localized_mem (z:=z) C.marked.stable C.marked.norm C.ten_count pure
  intro i hz
  simp [fiber,c,hz]

theorem clean_fifteen_head (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d) (C:OddSevenChart A d a r U w G) :
    ∃ v:Vec K (s+1), OddSevenChart A d a r U v G ∧ MulClosed U ∧
      ∀ i, Live U i→v i=0 := by
  have mulc : MulClosed U := fun _ hu _ hv => fifteen_core_times_five ha ho S M C (C.marked.core hv) hu
  have w5 : w∈defectPlus A d 5 := by
    simpa using marked_power C.marked (by decide) (k:=0) (by have := C.marked.rTwo;omega)
  obtain ⟨v,_,dis,eq⟩:=disjoint_head C.marked.stable mulc (fun u hu=>fifteen_core_times_five ha ho S M C w5 hu)
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have e:=dis i ⟨_,hz,hn⟩
    simp [fiber,e] at hn
  have H : MarkedHead A 7 d r U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=> (C.marked.paid j hj hq).trans (eq _).symm,
      C.marked.edge.trans (eq _).symm,C.marked.edgeRank⟩
  refine ⟨v,⟨H,C.chartType,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩,mulc,dis⟩
  intro j hj hm
  unfold forwardBand
  rw [eq]
  exact C.chart j hj hm

omit [CharZero K] in
theorem fifteen_square_cost (H:MarkedHead A 7 d r U w) (k:ℕ) (hk:k≤2*r-2) :
    (diag (nodes A)^k) (w*w)∈defectPlus A d 10 := by
  let D:=diag (nodes A)
  have rTwo:=H.rTwo
  let f:=min k (r-1)
  let g:=k-f
  have e:f+g=k := by dsimp [g];have hf:=min_le_left k (r-1);omega
  have hf:f<r := by dsimp [f];have := min_le_right k (r-1);omega
  have hg:g<r := by dsimp [g,f];omega
  have p1 : (D^f) w∈defectPlus A d 5 := marked_power H (by decide) hf
  have p2 : (D^g) w∈defectPlus A d 5 := marked_power H (by decide) hg
  have fit : (D^k) (w*w) = ((D^f) w)*((D^g) w) := by
    ext i
    simp only [D,pow_diag_apply,Pi.mul_apply]
    rw [←e,pow_add]
    ring
  rw [fit]
  exact Fplus_mul (j:=5) (k:=5) p1 p2

theorem fifteen_large_square_band (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d) (C:OddSevenChart A d a r U w G)
    (large : 3≤r) :
    ∀ k≤2*r-2,(diag (nodes A)^k) (w*w)∈forwardBand A 7 a r U w 10 := by
  intro k hk
  let D:=diag (nodes A)
  let n:=if d=0 then 2 else 3
  let j:=min k (2*r-2-n)
  have ncap : n≤2*r-2 := by by_cases dz:d=0 <;> simp [n,dz] <;> omega
  have jk : j≤k := min_le_left _ _
  have jb : j≤2*r-2-n := min_le_right _ _
  have win : k-j≤n := by dsimp [j];omega
  have paid (i : ℕ) (hi:i≤n) : (D^i) ((D^j) (w*w))∈defectPlus A d 10 := by
    rw [←mul_apply_eq_comp,←pow_add]
    exact fifteen_square_cost C.marked _ (by omega)
  have L := C.leak_free_ten_all ha ho S M paid (k-j) win
  rw [←mul_apply_eq_comp,←pow_add,show k-j+j=k by omega] at L
  exact L

theorem fifteen_large_profile (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d) (C:OddSevenChart A d a r U w G)
    (large : 3≤r) :
    ∃ (v:Vec K (s+1)) (P:K[X]), OddSevenChart A d a r U v G ∧ MulClosed U ∧
      (∀ i,Live U i→v i=0) ∧ P≠0 ∧
      P.natDegree+2*r-2<headLen 7 a r 10 ∧
      (∀ i,v i≠0→v i=P.eval (nodes A i)) := by
  obtain ⟨v,C,mulc,dis⟩:=clean_fifteen_head ha ho S M C
  have square := fifteen_large_square_band ha ho S M C large
  obtain ⟨P,pd,hP⟩:=multiplier_degree (a:=v) (d:=2*r-2) dis C.ten_count square
  have pn:P≠0 := by
    intro hz
    have hc := C.ten_count
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hx
    have vn := (Finset.mem_filter.mp hi).2
    exact vn (by rw [hP _ vn,hz,eval_zero])
  refine ⟨v,P,C,mulc,dis,pn,?_,hP⟩
  have h := pd.resolve_left pn
  omega

end RKCert.Paired.FiniteMidpoint

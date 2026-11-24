module
public import RKCert.DirkEvenHiddenPort
public import RKCert.DirkFixedEvenBoundary
public import RKCert.DirkMarkedBudget
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K : Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}

/-- An attained even boundary has no trailing zero-weight row, by restriction
of genuine tree conditions to the lower principal prefix and the same stage
bound for the shortened array, not by a hidden-stage removal argument. -/
theorem last_weight_ne_zero (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) : b (Fin.last s)≠0 := by
  intro hb
  have ht:s≤s+1 := by omega
  have hz (i:Fin (s+1)) (hi:s ≤ i.val) : b i=0 := by
    have hh:i=Fin.last s := Fin.ext (by have := i.isLt; change i.val=s; omega)
    simpa [hh] using hb
  have order:=order_on_lower_prefix ha ho ht hz
  have count:=(even_floor hm (lower_prefix ha ht) order).1
  omega

/-- The simple terminal coordinate really is the last physical coordinate,
and the actual last column of A is zero; the complete original array is
retained in every subsequent comparison. -/
theorem last_physical (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    b (Fin.last s)≠0 ∧ nodes A (Fin.last s)=1 ∧
    (∀i,A i (Fin.last s)=0) ∧ Pi.single (Fin.last s) (1:K)∈treeSpace A m ∧
    ∀f∈zeroSpace A m,f (Fin.last s)=0 := by
  classical
  let t:=Fin.last s
  have hb:b t≠0 := last_weight_ne_zero hm ha ho he
  have hz (j:Fin (s+1)) (hlt:t<j) : b j=0 := False.elim ((not_lt_of_ge (Fin.le_last j)) hlt)
  obtain ⟨d1,d2⟩:=even_zero_reverse_seeds hm ha ho he
  have hy:=dirk_last_node ha t hb hz d1 d2
  have ht:nodes A t=1 := (sub_eq_zero.mp (show 1-nodes A t=0 from hy)).symm
  have hdiag:A t t=0 := by
    have h:=congrFun d1 t
    change transMat A b t-mirror A t*b t=0 at h
    have tr:=causalDiag_transpose ha t b (fun j hj => hz j (Fin.rev_lt_rev.mp hj))
    rw [tr,hy,zero_mul,sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hb
  have hcol (i:Fin (s+1)) : A i t=0 := by
    rcases lt_or_eq_of_le (Fin.le_last i) with h|h
    · exact ha i t h
    · simpa [h,t] using hdiag
  have a:=even_dual_band hm ha ho he (q:=m) (r:=m-3) (by omega) (by omega)
  have card:Pi.single t (1:K)∈treeSpace A m := by
    rw [a.2.2.2,mem_annih]
    intro v hv
    have hv0:v t=0 := dirkBack_prior ha t hz hy d1 d2 (m-3) hv t (show t≤t from le_rfl)
    simp [row_apply,Pi.single_apply,hv0]
  have prev:=cardinal_clean_lower ho (j:=m-1) (by omega) t hb card
  refine ⟨hb,ht,hcol,card,?_⟩
  intro f hf
  rw [even_boundary_step hm ha ho he] at hf
  obtain ⟨u,hu,_,⟨v,hv,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hf
  change u t + (nodes A t)*(v t)=0
  rw [prev _ hu,prev _ hv,mul_zero,add_zero]

/-- Below the midpoint all genuine marked rows are exactly the native
reverse words. -/
theorem marked_eq_words (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) {j:ℕ} (hj:2≤j) (jl:j<m) :
    marked A (2*m) j=dirkBack A b (j-2) := by
  exact (even_dual_band hm ha ho he (q:=2*m-1-j) (r:=j-2) (by omega) (by omega)).2.2.1.symm

/-- Up to and including the midpoint the actual terminal-zero marked rows
belong to the reverse word flag. Only at the last grade is the zero
coordinate needed. -/
theorem marked_to_words (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) {j:ℕ} (hj:2≤j) (jl:j≤m)
    {w:Vec K (s+1)} (hw:w∈marked A (2*m) j) (wt:w (Fin.last s)=0) : w∈dirkBack A b (j-2) := by
  rcases lt_or_eq_of_le jl with lt|eq
  · rwa [marked_eq_words hm ha ho he hj lt] at hw
  · subst j
    obtain ⟨t,_,last,_,_,_,_,br,_⟩:=true_terminal_zero_band hm ha ho he
    have ht:t=Fin.last s := by
      by_contra hh
      exact last_weight_ne_zero hm ha ho he (last _ (lt_of_le_of_ne (Fin.le_last _) hh))
    rw [ht] at br
    rw [br,mem_annih]
    intro u hu
    obtain ⟨v,hv,_,hc,rfl⟩:=Submodule.mem_sup.mp hu
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hc
    have hz:row w v=0 := mem_annih.mp hw v (by
      rwa [show 2*m-1-m=m-1 by omega])
    rw [map_add,map_smul,hz,zero_add,row_single_right,wt,smul_zero]

/-- The true weighted image, not a zero-profile ansatz. -/
theorem weight_times_defect (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) {j:ℕ}
    (hj:2≤j) (jl:j≤m) {v:Vec K (s+1)} (hv:v∈zeroSpace A j) :
    b*v∈dirkBack A b (j-2) := by
  have clean: v (Fin.last s)=0:=(last_physical hm ha ho he).2.2.2.2 _ (zeroSpace_mono A jl hv)
  exact marked_to_words hm ha ho he hj jl (weights_mul_zeroSpace ho (by omega) hv)
    (by simp [clean])

/-- Products of a genuine reverse word and an ordinary tree column stay
in the paid word range, including the endpoint-refunded last grade. -/
theorem word_times_tree (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) {r k:ℕ}
    (hpay:r+k+2≤m) {w v:Vec K (s+1)} (hw:w∈dirkBack A b r) (hv:v∈treeSpace A k) :
    w*v∈dirkBack A b (r+k) := by
  obtain ⟨bt,ht,_⟩:=last_physical hm ha ho he
  obtain ⟨d1,d2⟩:=even_zero_reverse_seeds hm ha ho he
  have last (i:Fin (s+1)) (hl:Fin.last s < i) : b i=0 :=
    False.elim ((not_lt_of_ge (Fin.le_last i)) hl)
  have hy:mirror A (Fin.last s)=0 := by change 1-nodes A _=0; rw [ht,sub_self]
  have z:w (Fin.last s)=0 := dirkBack_prior ha _ last hy d1 d2 r hw _ (show Fin.last s ≤ Fin.last s from le_rfl)
  have hmark:w∈marked A (2*m) (r+2) := back_sub_marked ho (by omega) (by omega) (by simpa using hw)
  have hwv:=marked_mul_tree (j:=r+2) (k:=k) (by omega : r+2+k+1≤2*m) hmark hv
  have hh:=marked_to_words hm ha ho he (j:=r+2+k) (by omega) (by omega) hwv (by simp [z])
  rwa [show r+2+k-2=r+k by omega] at hh

end RKCert.Paired.Terminal

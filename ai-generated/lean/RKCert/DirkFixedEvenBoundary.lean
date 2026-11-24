module
public import RKCert.DirkEvenBoundary
public import RKCert.TerminalLobatto
@[expose] public section
namespace RKCert.Paired.Terminal
variable {K : Type*} [Field K] [CharZero K] {s m:ℕ} {A : Fin (s+1)→Fin (s+1)→K}
variable {b : Vec K (s+1)}

/-- At equality, the actual last defect increment is exactly the span of
the preceding column space and its clock images. In particular no new
physical support can appear across that increment. -/
theorem even_boundary_step (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    zeroSpace A m = zeroSpace A (m-1) ⊔ (zeroSpace A (m-1)).map (diag (nodes A)) := by
  obtain ⟨_,_,_,rprev,rm,_,_⟩ := even_boundary hm ha ho he
  have jm:m-1+1=m := by omega
  have one:Module.finrank K (zeroSpace A (m-1+1))≤Module.finrank K (zeroSpace A (m-1))+1 := by
    rw [jm,rprev,rm]; omega
  have esc:¬ (zeroSpace A (m-1)).map (diag (nodes A))≤zeroSpace A (m-1) := by
    intro hh
    have h:=dirk_forward_invariant_outgoing ha ho (j:=m-1) (by omega) (zeroSpace A (m-1))
      le_rfl (fun v hv => hh ⟨v,hv,rfl⟩)
    rw [jm,rprev,rm] at h
    omega
  simpa only [jm] using Clock.ordinary_step one esc

/-- On each of the four actual sharp-count boundary charts, the cardinal,
its nonzero output weight, and the true clean-row clock polynomial are
forced by the tableau alone.  The right endpoint is earned, not picked. -/
theorem fixed_even_boundary (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    ∃t:Fin (s+1), nodes A t=1 ∧ Pi.single t (1:K)∈treeSpace A m ∧
    Pi.single t (1:K)-(b t) • evalNodes A (lobatto m)∈zeroSpace A m ∧
    b t*((m*(m+1):ℕ):K)=1 ∧
    ∀i:Fin (s+1),i≠t → (∀f∈zeroSpace A (m-1), f i=0) → (lobatto m).eval (nodes A i)=0 := by
  obtain ⟨origin,_,_,_,_,_,t,_,h1,card,_,clean1⟩ := even_boundary (by omega) ha ho he
  have ⟨moment,atOne⟩:=lobatto_fixed (K:=K) hm
  have h0:nodes A 0=0 := by simp [nodes,origin]
  obtain ⟨rep,bw,roots⟩:=lobatto_tableau ho (by omega) (by omega) 0 t h0 h1
    (fun _ hf => zeroSpace_first_of_row origin m hf) clean1 card moment atOne
  refine ⟨t,h1,card,rep,bw,?_⟩
  intro i hit hi
  apply roots i hit
  intro f hf
  rw [even_boundary_step (by omega) ha ho he] at hf
  obtain ⟨u,hu,_,⟨v,hv,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hf
  simp [diag_apply,hi _ hu,hi _ hv]

end RKCert.Paired.Terminal

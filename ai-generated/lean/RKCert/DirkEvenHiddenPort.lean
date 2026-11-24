module
public import RKCert.DirkEvenDual
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K : Type*} [Field K] [CharZero K] {s p m:ℕ} {A : Fin s→Fin s→K} {b : Vec K s}

omit [CharZero K] in
theorem cardinal_not_mem (ho:HasTreeOrderAtLeast A b p) (hp:2*m+2≤p) (t:Fin s)
    (bne:b t≠0) (h1:nodes A t=1) : Pi.single t (1:K)∉treeSpace A m := by
  classical
  intro h
  obtain ⟨a,ha⟩:=exists_poly_zeroSpace ho (by omega) h
  apply bne
  apply constant_moments_unanchored ho hp a (b t)
  intro k
  have hh : probe A b k.val (Pi.single t (1:K) - polyEval A m a)=0 :=
    probe_zeroSpace ho (by omega) ha
  rw [map_sub,sub_eq_zero] at hh
  simpa [probe,Pi.single_apply,h1] using hh.symm

variable {T : Fin (s+1)→Fin (s+1)→K} {β : Vec K (s+1)}

/-- The extra terminal-zero one-mark space at the midpoint is exactly the
genuine reverse word space, even one index beyond the ordinary saturation
band. The annihilator includes precisely the *physical* terminal coordinate.
There is no division by an individual possibly zero interior weight. -/
theorem true_terminal_zero_band (hm:7≤m) (ha:LowerArray T)
    (ho:HasTreeOrderAtLeast T β (2*m)) (he:s+1+3=3*m) :
    ∃t:Fin (s+1), β t≠0 ∧ (∀ i : Fin (s+1), t < i → β i=0) ∧ nodes T t=1 ∧
    Pi.single t (1:K)∉treeSpace T (m-1) ∧
    finrank K (treeSpace T (m-1))=2*m-2 ∧ finrank K (dirkBack T β (m-2))=m-2 ∧
    dirkBack T β (m-2) = annih (treeSpace T (m-1) ⊔ K ∙ Pi.single t (1:K)) ∧
    treeSpace T (m-1) ⊔ K ∙ Pi.single t (1:K) = annih (dirkBack T β (m-2)) := by
  classical
  obtain ⟨_,_,_,rprev,_,_,_⟩:=even_boundary hm ha ho he
  obtain ⟨d1,d2⟩:=even_zero_reverse_seeds hm ha ho he
  obtain ⟨t,hw,hlast⟩:=last_output ho (by omega)
  have hy:=dirk_last_node ha t hw hlast d1 d2
  have ht:nodes T t=1 := (sub_eq_zero.mp (show 1-nodes T t=0 from hy)).symm
  have outside:=cardinal_not_mem ho (m:=m-1) (by omega) t hw ht
  let E:=treeSpace T (m-1) ⊔ K ∙ Pi.single t (1:K)
  let B:=dirkBack T β (m-2)
  have da:finrank K E=finrank K (treeSpace T (m-1))+1 :=
    Submodule.finrank_sup_span_singleton outside
  have df:=treeSpace_rank ho (q:=m-1) (by omega)
  have db:=dirkBack_rank ha ho (m-2) (by omega)
  have eperp:treeSpace T (m-1)≤annih B:=annih_flip_le (dirkBack_annih ho _ _ (by omega))
  have prior:=dirkBack_prior ha t hlast hy d1 d2 (m-2)
  have eperp':E≤annih B := sup_le eperp (Submodule.span_singleton_le_iff_mem .. |>.mpr (by
    apply mem_annih.mpr
    intro v hv
    have hzero:v t=0 := prior hv t (show t ≤ t from le_rfl)
    simp [row_apply,Pi.single_apply,hzero]))
  have bperp:=annih_flip_le eperp'
  have ds:=finrank_annih_le eperp'
  have db':m-2≤finrank K B := by dsimp [B]; omega
  have ee:=finrank_annih_le (le_refl (annih B))
  have er:=finrank_annih_le (le_refl (annih E))
  have eqB:B=annih E:=Submodule.eq_of_le_of_finrank_le bperp (by omega)
  have eqE:E=annih B:=Submodule.eq_of_le_of_finrank_le eperp' (by omega)
  exact ⟨t,hw,hlast,ht,outside,by omega,by change finrank K B=_; omega,eqB,eqE⟩

end RKCert.Paired.Terminal


namespace RKCert.Paired.Terminal
variable {K : Type*} [Field K] {s p q:ℕ} {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}

/-- A genuinely invisible physical column in the ordinary span plus one
boundary cardinal was already a genuine ordinary defect. The proof uses
paid field-valued probes, never the support of a quadratic form. -/
theorem hidden_mem_defect (ho:HasTreeOrderAtLeast A b p) (hp:2*q+1≤p)
    (h0:∀j,A 0 j=0) (t:Fin (s+1)) (hw:b t≠0) (ht:nodes A t=1)
    {z:Vec K (s+1)} (z0:z 0=0) (zb:∀i,b i*z i=0)
    (hz:z∈treeSpace A q ⊔ K ∙ Pi.single t (1:K)) : z∈zeroSpace A q := by
  classical
  have hnode:nodes A 0=0 := by simp [nodes,h0]
  have hot:(0:Fin (s+1))≠t := by intro e; rw [←e,hnode] at ht; exact zero_ne_one ht
  obtain ⟨e,he,_,hc,rfl⟩:=Submodule.mem_sup.mp hz
  obtain ⟨α,rfl⟩:=Submodule.mem_span_singleton.mp hc
  obtain ⟨a,hf⟩:=exists_poly_zeroSpace ho (by omega) he
  have e0:e 0=0 := by simpa [Pi.single_eq_of_ne hot] using z0
  have a0:a 0=0 := by
    have h : (e-polyEval A q a) 0=0 := zeroSpace_first_of_row h0 q hf
    rw [Pi.sub_apply,e0,zero_sub,neg_eq_zero,polyEval_first_of_row h0] at h
    exact h
  have zprobe (k:ℕ):probe A b k (e+α • Pi.single t (1:K))=0 := by
    rw [probe,row_apply]
    apply Finset.sum_eq_zero
    intro i _
    calc
      b i*(nodes A i)^k*(e+α • Pi.single t (1:K) : Vec K (s+1)) i =
          (b i*(e+α • Pi.single t (1:K) : Vec K (s+1)) i)*(nodes A i)^k := by ring
      _ = 0 := by rw [zb,zero_mul]
  have mom (k:Fin (q+1)) : probe A b k.val (polyEval A q a)= -(α*b t) := by
    have hdef: probe A b k.val (e-polyEval A q a)=0 := probe_zeroSpace ho (by omega) hf
    rw [map_sub,sub_eq_zero] at hdef
    have hs:probe A b k.val (Pi.single t (1:K))=b t := by simp [probe,Pi.single_apply,ht]
    have hh:=zprobe k.val
    rw [map_add,map_smul,smul_eq_mul,hs,hdef] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have ab:=constant_moments_origin_zero ho hp a a0 (-(α*b t)) mom
  have az:α=0 := (mul_eq_zero.mp (neg_eq_zero.mp ab)).resolve_right hw
  have coef:a=0 := by
    ext j
    apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l => by omega) a _ j
    intro k
    have h:=mom k
    rw [probe_polyEval ho (by omega),ab] at h
    exact h
  simpa [az,coef] using hf

end RKCert.Paired.Terminal

namespace RKCert.Paired.Terminal
variable {K : Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}

/-- All simultaneous invisible columns are contained in the true preceding
defect space at an even boundary. No converse or shorter tableau is claimed. -/
theorem hidden_port (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) {z:Vec K (s+1)} (z0:z 0=0) (zb:∀i,b i*z i=0)
    (hz:z∈annih (dirkBack A b (m-2))) : z∈zeroSpace A (m-1) := by
  obtain ⟨h0,_⟩:=even_boundary hm ha ho he
  obtain ⟨t,hw,_,ht,_,_,_,_,hE⟩:=true_terminal_zero_band hm ha ho he
  rw [←hE] at hz
  exact hidden_mem_defect ho (by omega) h0 t hw ht z0 zb hz

/-- If an actual physical coordinate misses the weight and every paid
reverse word, the single-coordinate vector occurs in the ordinary defect
space. This locates the physical stage; it does not remove it. -/
theorem hidden_coordinate (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (i:Fin (s+1)) (hi:i≠0) (b0:b i=0)
    (hrev:∀ w∈dirkBack A b (m-2), w i=0) : Pi.single i (1:K)∈zeroSpace A (m-1) := by
  classical
  apply hidden_port hm ha ho he
  · exact Pi.single_eq_of_ne (Ne.symm hi) _
  · intro j
    by_cases h:j=i
    · simp [h,b0]
    · simp [Pi.single_eq_of_ne h]
  · apply mem_annih.mpr
    intro w hw
    simp [row_apply,Pi.single_apply,hrev _ hw]

end RKCert.Paired.Terminal

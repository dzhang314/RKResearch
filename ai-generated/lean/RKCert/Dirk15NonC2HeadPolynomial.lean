module

public import RKCert.Dirk15NonC2Square
public import RKCert.CoreSupport

@[expose] public section

/-! # The actual forward head is a factor of the fixed Radau profile -/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

omit [CharZero K] in
theorem nonC2_ghost_channels_of_live {i : Fin 20}
    (h : Clock.Live (nonC2Ghosts A b) i) : b i=0 ∧ reverseCubic A b i=0 := by
  obtain ⟨z,hz,hi⟩ := h
  exact ⟨by_contra (fun u => hi (mem_nonC2Ghosts.mp hz i (Or.inl u))),
    by_contra (fun u => hi (mem_nonC2Ghosts.mp hz i (Or.inr u)))⟩

theorem order15_nonC2_head_polynomial (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b) :
    ∃ P : K[X],P≠0 ∧ P.natDegree≤4 ∧
      (∀ i,h.head i≠0 → h.head i=P.eval (nodes A i)) ∧
      P∣(normalizedRightRadau7 : K[X]) := by
  classical
  let c := nodes A
  let w := h.head
  let S := Clock.headSites c w
  have ns : 9≤S.card := order15_nonC2_head_sites ha ho hq h
  have dis (i : Fin 20) (hi : Clock.Live (nonC2Ghosts A b) i) : w i=0 :=
    h.disjoint i (nonC2_ghost_channels_of_live hi).1 (nonC2_ghost_channels_of_live hi).2
  have pay (k : ℕ) (hk : k≤2) : ((diag c)^k) (w*w)∈h.orbit 7 :=
    order15_nonC2_square_tail ha ho hq h ⟨k,by omega⟩
  obtain ⟨P,dP,headP⟩ := Clock.multiplier_degree (c:=c) (w:=w) (U:=nonC2Ghosts A b)
    (a:=w) (n:=7) (d:=2) dis (by omega : 7<S.card) pay
  have reps (z : K) (hz : z∈S) : ∃ i : Fin 20,w i≠0 ∧ c i=z := by
    obtain ⟨i,hm,eq⟩ := Finset.mem_image.mp hz
    exact ⟨i,(Finset.mem_filter.mp hm).2,eq⟩
  have pn : P≠0 := by
    intro e
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0<S.card)
    obtain ⟨i,hi,_⟩ := reps z hz
    exact hi (by simpa only [e,eval_zero] using headP i hi)
  have deg : P.natDegree≤4 := by
    have g := dP.resolve_left pn
    omega
  refine ⟨P,pn,deg,headP,?_⟩
  let G : K[X] := normalizedRightRadau7
  have v : terminalCardinal K 19-evalNodes A G∈h.orbit 4 :=
    (h.band 2 (by decide)).le (order15_nonC2_terminal_profile ha ho hq)
  obtain ⟨u,hu,Q,dQ,eQ⟩ := Clock.exists_head_poly v
  have dq : Q.natDegree≤3 := by
    by_cases hz : Q=0
    · simp [hz]
    · have d := (natDegree_lt_iff_degree_lt hz).mpr dQ
      omega
  have H := order15_nonC2_rank_chart ha ho hq
  have wt : w (Fin.last 19)=0 := by
    apply h.orbit_last H 4
    have pp := ((chain_le_iff (T:=diag c) (U:=nonC2Ghosts A b) (w:=w) 4).mp le_rfl).2 0 (by decide)
    change w∈chain (diag c) (nonC2Ghosts A b) w 4
    simpa only [pow_zero,one_apply_eq_self] using pp
  have product : G=P*(-Q) := by
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq S
    · apply degree_le_natDegree.trans_lt
      exact_mod_cast (show G.natDegree<S.card by
        have e : G.natDegree=7 := normalizedRightRadau7_degree
        omega)
    · apply degree_le_natDegree.trans_lt
      exact_mod_cast (show (P*(-Q)).natDegree<S.card from
        natDegree_mul_le.trans_lt (by rw [natDegree_neg]; omega))
    · intro z hz
      obtain ⟨i,wi,rfl⟩ := reps z hz
      have it : i≠Fin.last 19 := fun e => wi (e ▸ wt)
      have ui : u i=0 := by
        by_contra no
        exact wi (dis i ⟨u,hu,no⟩)
      have e := eQ i
      change (terminalCardinal K 19-evalNodes A G) i=u i+Q.eval (c i)*w i at e
      simp only [Pi.sub_apply,terminalCardinal_apply_ne it,evalNodes_apply,zero_sub,ui,zero_add,headP i wi] at e
      rw [eval_mul,eval_neg]
      linear_combination -e
  exact ⟨-Q,product⟩

end
end RKCert.Paired

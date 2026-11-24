module
public import RKCert.Dirk19Rank
public import RKCert.DirkTerminalDelete
public import RKCert.DirkReverseHermite
@[expose] public section
namespace RKCert.Paired.Nineteen
open Module Terminal
variable {K:Type*} [Field K] [CharZero K] {A:Fin 26→Fin 26→K} {b:Vec K 26}

omit [CharZero K] in
theorem kernel_terminal_eq_last {s p j:ℕ} (T:Fin (s+1)→Fin (s+1)→K) :
    ReverseHermite.zeroMarked T p (Fin.last s) j=markedTerminalZero (s:=s) T p j :=by
  ext x
  change (x∈marked T p j ∧ x (Fin.last s)=0) ↔ (x∈marked T p j ∧ x∈prior (Fin.last s))
  rw [prior_last_iff]

structure TerminalBand (A:Fin 26→Fin 26→K) (b:Vec K 26) : Prop where
  last : PhysicalTerminal (s:=25) A b
  cardinal : terminalCardinal K 25∈treeSpace A 10
  col_zero : ∀i,A i (Fin.last 25)=0
  f9_zero : ∀v∈zeroSpace A 9,v (Fin.last 25)=0
  tail : ∀q r:ℕ,10≤q→q+r=16→finrank K (treeSpace A q)=q+10 ∧
    finrank K (dirkBack A b r)=r ∧ dirkBack A b r=annih (treeSpace A q) ∧ treeSpace A q=annih (dirkBack A b r)
  full : ∀j:ℕ,2≤j→j≤8→marked A 19 j=dirkBack A b (j-2) ∧ finrank K (marked A 19 j)=j-2
  zeroWords : ∀j:ℕ,2≤j→j≤9→ReverseHermite.zeroMarked A 19 (Fin.last 25) j=dirkBack A b (j-2)
  wordRank : ∀r:ℕ,r+2≤9→finrank K (dirkBack A b r)=r
  dual_nine : annih (dirkBack A b 7)=treeSpace A 9 ⊔ Submodule.span K ({terminalCardinal K 25}:Set (Vec K 26))

/-- At 26 stages, the grade-ten gain makes the entire marked flag through
eight minimal even on the anchored branch: no separate early-surplus chart.
At grade nine only the actual terminal-zero subspace is required. -/
theorem terminal_band (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) : TerminalBand A b:=by
  classical
  let R:=initial_ranks ha ho
  let t:=Fin.last 25
  let ec:=terminalCardinal K 25
  have bank:=R.e10
  have tail (q r:ℕ) (lo:10≤q) (eq:q+r=16) :
      finrank K (treeSpace A q)=q+10 ∧ finrank K (dirkBack A b r)=r ∧
      dirkBack A b r=annih (treeSpace A q) ∧ treeSpace A q=annih (dirkBack A b r):=by
    obtain ⟨hn,rest⟩:=paid_tail_duality ha ho (m:=10) (d:=20) (r₀:=6) bank.ge (by decide) (by decide)
      (q:=q) (r:=r) lo (by omega)
    exact ⟨by omega,rest⟩
  have hw:=terminal_weight ha ho
  obtain ⟨T,card⟩:=terminal_last_space_of_budget (s:=25) ha ho hw (m:=10) (r:=6) (by decide)
    (by change 26≤finrank K (treeSpace A 10)+6;omega)
  have col (i:Fin 26):A i t=0:=by
    have q:=congrFun T.annihilated i
    simpa [t,terminalCardinal,mat_apply,Pi.single_apply,mul_ite] using q
  have f8zero:=cardinal_clean_lower ho (j:=8) (by decide:8+10+1≤19) t hw card
  have esc:¬(zeroSpace A 8).map (diag (nodes A))≤zeroSpace A 8:=by
    intro inv
    have g:=dirk_forward_invariant_outgoing ha ho (j:=8) (by decide) (zeroSpace A 8) le_rfl (fun v hv=>inv ⟨v,hv,rfl⟩)
    change finrank K (zeroSpace A 8)+4≤finrank K (zeroSpace A 9) at g
    have h:=R.f8;have q:=R.f9;omega
  have join:=Clock.ordinary_step (A:=A) (j:=8) (by change finrank K (zeroSpace A 9)≤finrank K (zeroSpace A 8)+1;have h:=R.f8;have q:=R.f9;omega) esc
  have f9zero (v:Vec K 26) (hv:v∈zeroSpace A 9) : v t=0:=by
    rw [join] at hv
    obtain ⟨x,hx,y,⟨y',hy',rfl⟩,rfl⟩:=Submodule.mem_sup.mp hv
    simp [diag_apply,f8zero x hx,f8zero y' hy']
  have full (j:ℕ) (lo:2≤j) (hi:j≤8) : marked A 19 j=dirkBack A b (j-2) ∧ finrank K (marked A 19 j)=j-2:=by
    have tr:=tail (18-j) (j-2) (by omega) (by omega)
    have e:marked A 19 j=dirkBack A b (j-2):=tr.2.2.1.symm
    exact ⟨e,e ▸ tr.2.1⟩
  have low (j:ℕ) (lo:2≤j) (hi:j≤9):
      dirkBack A b (j-2)≤markedTerminalZero (s:=25) A 19 j:=back_sub_markedTerminalZero ha ho T lo (by omega)
  let M:=markedTerminalZero (s:=25) A 19 9
  have upper:finrank K M≤7:=by
    have num:=marked_rank A 19 9
    change finrank K (treeSpace A 9)+finrank K (marked A 19 9)=26 at num
    have er:=R.e9
    by_cases h:q₂ (mat A) (nodes A) 1=0
    · have ex:excess A=0:=by simp [excess,h]
      have forbidden:=first_row_anchored_terminal_not_mem (s:=25) ho (m:=9) (by decide) T (dirk_first_row ha h)
      have lt:M<marked A 19 9:=by
        apply lt_of_le_of_ne inf_le_left
        intro eq
        have all:marked A 19 9≤prior t:=eq ▸ (inf_le_right : M≤prior t)
        have hit:=terminal_cardinal_annihilates all
        rw [marked,annih_annih_paired] at hit
        exact forbidden hit
      have drop:finrank K M<finrank K (marked A 19 9):=Submodule.finrank_lt_finrank_of_lt lt
      rw [ex] at er;omega
    · have ex:excess A=1:=by simp [excess,h]
      have drop:finrank K M≤finrank K (marked A 19 9):=Submodule.finrank_mono (inf_le_left:M≤marked A 19 9)
      rw [ex] at er;omega
  have h7:=dirkBack_rank ha ho 7 (by decide)
  have inc9:=low 9 (by decide) (by decide)
  have eq9 : M=dirkBack A b 7:=by
    symm;apply Submodule.eq_of_le_of_finrank_le inc9
    change finrank K M≤finrank K (dirkBack A b 7)
    omega
  have b7:finrank K (dirkBack A b 7)=7:=by
    have ub:finrank K (dirkBack A b 7)≤7:=eq9 ▸ upper;omega
  have zero (j:ℕ) (lo:2≤j) (hi:j≤9) :
      ReverseHermite.zeroMarked A 19 t j=dirkBack A b (j-2):=by
    rw [kernel_terminal_eq_last]
    rcases lt_or_eq_of_le hi with lt|rfl
    · apply le_antisymm _ (low j lo hi)
      exact (inf_le_left:_≤marked A 19 j).trans (full j lo (by omega)).1.le
    · exact eq9
  have wr (r:ℕ) (hi:r+2≤9):finrank K (dirkBack A b r)=r:=by
    by_cases hr:r=7
    · subst r;exact b7
    · exact (tail (16-r) r (by omega) (by omega)).2.1
  have E:treeSpace A 9 ≤ annih M:=annih_flip_le (show M≤marked A 19 9 from inf_le_left)
  have Tmem:ec∈annih M:=terminal_cardinal_annihilates (T:=M) inf_le_right
  have sub:treeSpace A 9 ⊔ Submodule.span K ({ec}:Set (Vec K 26))≤annih M:=
    sup_le E ((Submodule.span_singleton_le_iff_mem _ _).mpr Tmem)
  have dim:finrank K (dirkBack A b 7)+finrank K (annih (dirkBack A b 7))=26:=finrank_annih_eq _
  have dual:annih M=treeSpace A 9 ⊔ Submodule.span K ({ec}:Set (Vec K 26)):=by
    symm;apply Submodule.eq_of_le_of_finrank_le sub
    rw [eq9]
    by_cases h:q₂ (mat A) (nodes A) 1=0
    · have ex:excess A=0:=by simp [excess,h]
      have forbid:ec∉treeSpace A 9:=first_row_anchored_terminal_not_mem (s:=25) ho (m:=9) (by decide) T (dirk_first_row ha h)
      rw [Submodule.finrank_sup_span_singleton forbid]
      change finrank K (annih (dirkBack A b 7))≤finrank K (treeSpace A 9)+1
      have er:=R.e9;rw [ex] at er;omega
    · have ex:excess A=1:=by simp [excess,h]
      have lb:=Submodule.finrank_mono (le_sup_left:treeSpace A 9≤treeSpace A 9 ⊔ Submodule.span K ({ec}:Set (Vec K 26)))
      have er:=R.e9;rw [ex] at er;omega
  exact ⟨T,card,col,f9zero,tail,full,zero,wr,eq9 ▸ dual⟩
end RKCert.Paired.Nineteen

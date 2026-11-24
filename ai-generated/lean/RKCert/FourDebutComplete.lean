module
public import RKCert.FourDebutHeads
public import RKCert.FourDebutMoments
@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape Module Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s}

theorem bary_native {k : ℕ} {i : Fin s} (ix : Fin (k+1)→Fin s)
    (ha : SDIRK.lower A) (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U)
    (hin : U≤zeroSpace A (k+3)) (chain_in : chain (diag (nodes A)) U w k ≤ zeroSpace A (k+3))
    (flag : zeroSpace A (k+4) ≤ chain (diag (nodes A)) U w (k+1))
    (prior : ∀ l, ix l < i) (outs : ∀l,¬Live U (ix l)) (outi : ¬Live U i)
    (cover : ∀ l < i, ¬Live U l → nodes A l≠0 → ∃a,nodes A l=nodes A (ix a))
    (wi : ∀ l,w (ix l) ≠ 0) (fresh : ∀l,nodes A i≠nodes A (ix l))
    (nu : nodes A i≠0) (nz : ∀l,nodes A (ix l)≠0)
    (distinct : Function.Injective (fun l => nodes A (ix l))) (ai : A i i=0) :
    (∑ l, (nodes A (ix l)^2/w (ix l))*(nodes A (ix l)-nodes A i))=0 := by
  obtain ⟨P,Q,Pn,deg,P0,dq,pv,vi,vb⟩ := native_paired_cut ix ha hT hU hin chain_in flag prior outs
    outi cover wi distinct ai
  exact barycentric_sum (fun l=>nodes A (ix l)) (fun l=>w (ix l)) (nodes A i)
    distinct fresh nu nz wi Pn deg P0 dq pv vi vb

structure FourSites (A : Fin s→Fin s→K) (U : Submodule K (Vec K s)) where
  i0 : Fin s
  i1 : Fin s
  i2 : Fin s
  i3 : Fin s
  h0 : Debut (nodes A) U ∅ i0
  h1 : Debut (nodes A) U {nodes A i0} i1
  h2 : Debut (nodes A) U {nodes A i0,nodes A i1} i2
  h3 : Debut (nodes A) U {nodes A i0,nodes A i1,nodes A i2} i3

omit [CharZero K] in
theorem four_sites (h : 4≤(outerSites (nodes A) U).card) : Nonempty (FourSites A U) := by
  classical
  obtain ⟨i0,d0⟩ := next_debut (c:=nodes A) (U:=U) ∅ (by simpa using Nat.lt_of_lt_of_le (by decide : 0<4) h)
  obtain ⟨i1,d1⟩ := next_debut (c:=nodes A) (U:=U) {nodes A i0} (by simpa using Nat.lt_of_lt_of_le (by decide : 1<4) h)
  have card2 (x y : K) : ({x,y}:Finset K).card≤2 := (Finset.card_insert_le x {y}).trans (by simp)
  have card3 (x y z : K) : ({x,y,z}:Finset K).card≤3 := (Finset.card_insert_le x {y,z}).trans
    (by have := card2 y z; omega)
  obtain ⟨i2,d2⟩ := next_debut (c:=nodes A) (U:=U) {nodes A i0,nodes A i1}
    ((card2 ..).trans_lt ((by decide : 2<4).trans_le h))
  obtain ⟨i3,d3⟩ := next_debut (c:=nodes A) (U:=U) {nodes A i0,nodes A i1,nodes A i2}
    ((card3 ..).trans_lt ((by decide : 3<4).trans_le h))
  exact ⟨⟨i0,i1,i2,i3,d0,d1,d2,d3⟩⟩

omit [CharZero K] in
theorem degreeZ2 (a b : K) : (Z2 a b).natDegree≤2 := by
  exact (Polynomial.natDegree_mul_le (p:=X-C a) (q:=X-C b)).trans (by simp)

omit [CharZero K] in
theorem degreeZ3 (a b u : K) : (Z3 a b u).natDegree≤3 := by
  exact (Polynomial.natDegree_mul_le (p:=Z2 a b) (q:=X-C u)).trans (by
    rw [natDegree_X_sub_C]; have := degreeZ2 a b; omega)

set_option maxHeartbeats 2000000 in
/-- A genuine degree-four head on an invariant F3 cannot persist through
F4,F5,F6. All four chronological debuts, refunds, cuts, and scalar equations
are conclusions of the native tableau flag, not interface assumptions. -/
theorem no_grade4_head (ha : SDIRK.lower A) (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U) (hin : U≤zeroSpace A 3)
    (band : ∀ k≤2,zeroSpace A (4+k)=chain (diag (nodes A)) U w (1+k)) : False := by
  classical
  obtain ⟨⟨i0,i1,i2,i3,d0,d1,d2,d3⟩⟩ := four_sites (outer_count ho hp hT hU hin)
  let a := nodes A i0
  let beta := nodes A i1
  let u := nodes A i2
  let v := nodes A i3
  let t := diag (nodes A)
  change Debut (nodes A) U {a} i1 at d1
  change Debut (nodes A) U {a,beta} i2 at d2
  change Debut (nodes A) U {a,beta,u} i3 at d3
  have f4 : zeroSpace A 4=chain t U w 1 := band 0 (by decide)
  have f5 : zeroSpace A 5=chain t U w 2 := band 1 (by decide)
  have f6 : zeroSpace A 6=chain t U w 3 := band 2 (by decide)
  have h01 : i0 < i1 := debut_before d0 d1 (by simp) (by simp [a])
  have h12 : i1 < i2 := debut_before d1 d2 (by simp) (by simp [beta])
  have h23 : i2 < i3 := debut_before d2 d3 (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at *; exact hz.imp id Or.inl) (by simp [u])
  have h02 := h01.trans h12
  have h13 := h12.trans h23
  have h03 := h02.trans h23
  have ba : beta≠a := by intro e; exact d1.fresh (by change beta∈{a}; simp [e])
  have uv : u≠v := by intro e; exact d3.fresh (by change v∈{a,beta,u}; simp [e])
  have au : a≠u := by intro e; exact d2.fresh (by change u∈{a,beta}; simp [e])
  have bu : beta≠u := by intro e; exact d2.fresh (by change u∈{a,beta}; simp [e])
  have av : a≠v := by intro e; exact d3.fresh (by change v∈{a,beta,u}; simp [e])
  have bv : beta≠v := by intro e; exact d3.fresh (by change v∈{a,beta,u}; simp [e])
  have wa := early_head ha ho hp hT hU hin f5.le f6.le d0 (by simp)
  have wb := early_head ha ho hp hT hU hin f5.le f6.le d1 (by simp)
  have card2 : ({a,beta}:Finset K).card≤2 := (Finset.card_insert_le a {beta}).trans (by simp)
  have wu := early_head ha ho hp hT hU hin f5.le f6.le d2 card2
  let ix : Fin 2→Fin s := ![i0,i1]
  let iy : Fin 3→Fin s := ![i0,i1,i2]
  have px (l : Fin 2) : ix l < i2 := by fin_cases l <;> first | exact h02 | exact h12
  have py (l : Fin 3) : iy l < i3 := by fin_cases l <;> first | exact h03 | exact h13 | exact h23
  have ox (l : Fin 2) : ¬Live U (ix l) := by fin_cases l <;> first | exact d0.outsideU | exact d1.outsideU
  have oy (l : Fin 3) : ¬Live U (iy l) := by fin_cases l <;> first | exact d0.outsideU | exact d1.outsideU | exact d2.outsideU
  have wx (l : Fin 2) : w (ix l)≠0 := by fin_cases l <;> first | exact wa | exact wb
  have wy (l : Fin 3) : w (iy l)≠0 := by fin_cases l <;> first | exact wa | exact wb | exact wu
  have nx (l : Fin 2) : nodes A (ix l)≠0 := by fin_cases l <;> first | exact d0.nz | exact d1.nz
  have ny (l : Fin 3) : nodes A (iy l)≠0 := by fin_cases l <;> first | exact d0.nz | exact d1.nz | exact d2.nz
  have fx (l : Fin 2) : u≠nodes A (ix l) := by fin_cases l <;> first | exact au.symm | exact bu.symm
  have fy (l : Fin 3) : v≠nodes A (iy l) := by fin_cases l <;> first | exact av.symm | exact bv.symm | exact uv.symm
  have injx : Function.Injective (fun l=>nodes A (ix l)) := by
    intro k l e
    fin_cases k <;> fin_cases l <;> first | rfl | exact (ba e).elim | exact (ba e.symm).elim
  have injy : Function.Injective (fun l=>nodes A (iy l)) := by
    intro k l e
    fin_cases k <;> fin_cases l <;> first | rfl | exact (ba e).elim | exact (ba e.symm).elim | exact (au e).elim | exact (au e.symm).elim | exact (bu e).elim | exact (bu e.symm).elim
  have cx (l : Fin s) (hl : l < i2) (n : ¬Live U l) (nz : nodes A l≠0) :
      ∃k, nodes A l=nodes A (ix k) := by
    have e := d2.old l hl n nz
    simp only [Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with e|e
    · exact ⟨0,e⟩
    · exact ⟨1,e⟩
  have cy (l : Fin s) (hl : l < i3) (n : ¬Live U l) (nz : nodes A l≠0) :
      ∃k, nodes A l=nodes A (iy k) := by
    have e := d3.old l hl n nz
    simp only [Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with e|e|e
    · exact ⟨0,e⟩
    · exact ⟨1,e⟩
    · exact ⟨2,e⟩
  have zero2 : A i2 i2=0 := general_refund (j:=3) ix d2 ha ho (by omega) (by decide) hT hU hin
    (by omega) px ox wx injx f5.le
  have card3 : ({a,beta,u}:Finset K).card≤3 :=
    (Finset.card_insert_le a {beta,u}).trans (by have := Finset.card_insert_le beta {u}; simp at this; omega)
  have zero3 : A i3 i3=0 := general_refund (j:=4) iy d3 ha ho (by omega) (by decide) hT hU hin
    (by omega) py oy wy injy f6.le
  have hi4 := hin.trans (zeroSpace_mono A (by decide : 3≤4))
  have hi5 := hin.trans (zeroSpace_mono A (by decide : 3≤5))
  have cut3 := bary_native ix ha hT hU hi4 f4.ge f5.le px ox d2.outsideU cx wx fx d2.nz nx injx zero2
  have cut4 := bary_native iy ha hT hU hi5 f5.ge f6.le py oy d3.outsideU cy wy fy d3.nz ny injy zero3
  have cut3' : (a^2/w i0)*(a-u)+(beta^2/w i1)*(beta-u)=0 := by
    simpa [ix,a,beta,u,Fin.sum_univ_succ] using cut3
  have cut4' : (a^2/w i0)*(a-v)+(beta^2/w i1)*(beta-v)+(u^2/w i2)*(u-v)=0 := by
    simpa [iy,a,beta,u,v,Fin.sum_univ_succ,add_assoc] using cut4
  obtain ⟨Q0,deg0,eq0⟩ := masked_primitive (P:=X*Z2 a beta) d2 ha hT hU hin f4.le zero2
    (Polynomial.natDegree_mul_le.trans (by rw [natDegree_X]; have := degreeZ2 a beta; omega))
    (by simp) (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
                  rcases hz with rfl|rfl <;> simp [Z2])
  obtain ⟨Q1,deg1,eq1⟩ := masked_primitive (P:=X*Z3 a beta u) d3 ha hT hU hi4 f5.le zero3
    (Polynomial.natDegree_mul_le.trans (by rw [natDegree_X]; have := degreeZ3 a beta u; omega))
    (by simp) (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
                  rcases hz with rfl|rfl|rfl <;> simp [Z3])
  obtain ⟨Q2,deg2,eq2⟩ := masked_primitive (P:=X^2*Z3 a beta u) d3 ha hT hU hi5 f6.le zero3
    (Polynomial.natDegree_mul_le.trans (by rw [natDegree_X_pow]; have := degreeZ3 a beta u; omega))
    (by simp) (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
                  rcases hz with rfl|rfl|rfl <;> simp [Z3])
  have P0 (l : Fin s) (hl : l ≤ i2) (n : ¬ Live U l) :
      (nodes A l)^2*L2 a beta (nodes A l)=w l*Q0.coeff 0 := by
    rw [←primitive2,eq0 l hl n,represent0 deg0]
  have B (l : Fin s) (hl : l ≤ i3) (n : ¬Live U l) :
      B1 a beta u (nodes A l)=w l*(Q1.coeff 1*(nodes A l)+Q1.coeff 0) ∧
      B2 a beta u (nodes A l)=w l*(Q2.coeff 2*(nodes A l)^2+Q2.coeff 1*(nodes A l)+Q2.coeff 0) := by
    rw [←primitive31,←primitive32,eq1 l hl n,eq2 l hl n,represent1 deg1,represent2 deg2]; exact ⟨rfl,rfl⟩
  apply fourth_impossible (a:=a) (b:=beta) (u:=u) (v:=v) (wv:=w i3)
    (l₁:=Q1.coeff 1) (l₀:=Q1.coeff 0) (q₂:=Q2.coeff 2) (q₁:=Q2.coeff 1) (q₀:=Q2.coeff 0)
    d0.nz d1.nz d2.nz d3.nz ba.symm au bu av bv uv wa wb wu cut3' cut4'
    (P0 i0 h02.le d0.outsideU) (P0 i1 h12.le d1.outsideU) (P0 i2 le_rfl d2.outsideU)
  intro x y h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact B i0 h03.le d0.outsideU
  · exact B i1 h13.le d1.outsideU
  · exact B i2 h23.le d2.outsideU
  · exact B i3 le_rfl d3.outsideU
end RKCert.FourDebut

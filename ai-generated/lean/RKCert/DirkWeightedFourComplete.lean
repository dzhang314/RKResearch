module
public import RKCert.DirkWeightedFourCut
@[expose] public section
namespace RKCert.Paired.LocalProjection.WeightedFour
open RKCert.Endpoint Polynomial RKCert.OneEscape RKCert.FourDebut
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section
variable (D:WeightedFour K s)

theorem debut_before {S T:Finset K} {i j:Fin s} (u:Debut D S i) (v:Debut D T j)
    (h:S⊆T) (hj:D.clock i∈T) : j < i := by
  by_contra! he
  rcases lt_or_eq_of_le he with hlt|rfl
  · exact v.fresh (h (u.old j hlt v.active v.nz))
  · exact v.fresh hj

theorem masked_primitive [CharZero K] {S:Finset K} {i:Fin s} {P:K[X]} (db:Debut D S i) {j:ℕ} (hj:3≤j) (jh:j≤5)
    (off:D.pivot i=0) (dp:P.natDegree≤j) (p0:P.eval 0=0) (roots:∀a∈S,P.eval a=0) :
    ∃Q:K[X],Q.degree<(j-2:ℕ) ∧ ∀l,i ≤ l → D.base l≠0 → (Paired.primitive P).eval (D.clock l)=D.amp l*Q.eval (D.clock l) := by
  have hz:(0:K[X]).degree<(j-3:ℕ):= by rw [degree_zero]; exact WithBot.bot_lt_coe _
  obtain ⟨Q,hQ,h⟩:=D.primitive_cut hj jh off dp hz (by simpa using D.mask db p0 roots)
  refine ⟨Q,hQ,fun l hl hb=>?_⟩
  rw [←formalPrimitive_eq_treePrimitive]
  exact D.normalize l hb (h l hl)

set_option maxHeartbeats 2000000 in
/-- A single weighted head starting in grade four cannot satisfy the
two paid error families, even with zero or signed physical weights and
repeated abscissae. Characteristic zero, without a compatible ordering. -/
theorem impossible [CharZero K] (D:WeightedFour K s) : False := by
  classical
  have h:=D.count
  obtain ⟨i0,d0⟩:=D.next_debut ∅ (by simpa using Nat.lt_of_lt_of_le (by decide:0<4) h)
  obtain ⟨i1,d1⟩:=D.next_debut {D.clock i0} (by simpa using Nat.lt_of_lt_of_le (by decide:1<4) h)
  have cardTwo (x y:K):({x,y}:Finset K).card≤2:=(Finset.card_insert_le x {y}).trans (by simp)
  have cardThree (x y z:K):({x,y,z}:Finset K).card≤3:=(Finset.card_insert_le x {y,z}).trans (by have:=cardTwo y z; omega)
  obtain ⟨i2,d2⟩:=D.next_debut {D.clock i0,D.clock i1} ((cardTwo ..).trans_lt ((by decide:2<4).trans_le h))
  obtain ⟨i3,d3⟩:=D.next_debut {D.clock i0,D.clock i1,D.clock i2} ((cardThree ..).trans_lt ((by decide:3<4).trans_le h))
  let a := D.clock i0
  let beta := D.clock i1
  let u := D.clock i2
  let v := D.clock i3
  change Debut D {a} i1 at d1
  change Debut D {a,beta} i2 at d2
  change Debut D {a,beta,u} i3 at d3
  have h01 : i1 < i0 := D.debut_before d0 d1 (by simp) (by simp [a])
  have h12 : i2 < i1 := D.debut_before d1 d2 (by simp) (by simp [beta])
  have h23 : i3 < i2 := D.debut_before d2 d3 (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at *; exact hz.imp id Or.inl) (by simp [u])
  have h02 := h12.trans h01
  have h13 := h23.trans h12
  have h03 := h23.trans h02
  have ba : beta≠a := by intro e; exact d1.fresh (by change beta∈{a}; simp [e])
  have uv : u≠v := by intro e; exact d3.fresh (by change v∈{a,beta,u}; simp [e])
  have au : a≠u := by intro e; exact d2.fresh (by change u∈{a,beta}; simp [e])
  have bu : beta≠u := by intro e; exact d2.fresh (by change u∈{a,beta}; simp [e])
  have av : a≠v := by intro e; exact d3.fresh (by change v∈{a,beta,u}; simp [e])
  have bv : beta≠v := by intro e; exact d3.fresh (by change v∈{a,beta,u}; simp [e])
  have wa := D.early_head d0 (by simp)
  have wb := D.early_head d1 (by simp)
  have card2 : ({a,beta}:Finset K).card≤2 := (Finset.card_insert_le a {beta}).trans (by simp)
  have wu := D.early_head d2 card2
  let ix : Fin 2→Fin s := ![i0,i1]
  let iy : Fin 3→Fin s := ![i0,i1,i2]
  have px (l : Fin 2) : i2 < ix l := by fin_cases l <;> first | exact h02 | exact h12
  have py (l : Fin 3) : i3 < iy l := by fin_cases l <;> first | exact h03 | exact h13 | exact h23
  have ox (l : Fin 2) : D.base (ix l)≠0 := by fin_cases l <;> first | exact d0.active | exact d1.active
  have oy (l : Fin 3) : D.base (iy l)≠0 := by fin_cases l <;> first | exact d0.active | exact d1.active | exact d2.active
  have wx (l : Fin 2) : D.head (ix l)≠0 := by fin_cases l <;> first | exact wa | exact wb
  have wy (l : Fin 3) : D.head (iy l)≠0 := by fin_cases l <;> first | exact wa | exact wb | exact wu
  have nx (l : Fin 2) : D.clock (ix l)≠0 := by fin_cases l <;> first | exact d0.nz | exact d1.nz
  have ny (l : Fin 3) : D.clock (iy l)≠0 := by fin_cases l <;> first | exact d0.nz | exact d1.nz | exact d2.nz
  have fx (l : Fin 2) : u≠D.clock (ix l) := by fin_cases l <;> first | exact au.symm | exact bu.symm
  have fy (l : Fin 3) : v≠D.clock (iy l) := by fin_cases l <;> first | exact av.symm | exact bv.symm | exact uv.symm
  have injx : Function.Injective (fun l=>D.clock (ix l)) := by
    intro k l e
    fin_cases k <;> fin_cases l <;> first | rfl | exact (ba e).elim | exact (ba e.symm).elim
  have injy : Function.Injective (fun l=>D.clock (iy l)) := by
    intro k l e
    fin_cases k <;> fin_cases l <;> first | rfl | exact (ba e).elim | exact (ba e.symm).elim | exact (au e).elim | exact (au e.symm).elim | exact (bu e).elim | exact (bu e.symm).elim
  have cx (l : Fin s) (hl : i2 < l) (n : D.base l≠0) (nz : D.clock l≠0) :
      ∃k, D.clock l=D.clock (ix k) := by
    have e := d2.old l hl n nz
    simp only [Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with e|e
    · exact ⟨0,e⟩
    · exact ⟨1,e⟩
  have cy (l : Fin s) (hl : i3 < l) (n : D.base l≠0) (nz : D.clock l≠0) :
      ∃k, D.clock l=D.clock (iy k) := by
    have e := d3.old l hl n nz
    simp only [Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with e|e|e
    · exact ⟨0,e⟩
    · exact ⟨1,e⟩
    · exact ⟨2,e⟩
  have zero2:=D.general_refund (j:=3) ix d2 (by decide) (by decide) (by omega) (by decide) px wx injx
  have card3 : ({a,beta,u}:Finset K).card≤3 :=
    (Finset.card_insert_le a {beta,u}).trans (by have := Finset.card_insert_le beta {u}; simp at this; omega)
  have zero3:=D.general_refund (j:=4) iy d3 (by decide) (by decide) (by omega) (by decide) py wy injy
  have wx' (l:Fin 2):D.amp (ix l)≠0 := div_ne_zero (wx l) (ox l)
  have wy' (l:Fin 3):D.amp (iy l)≠0 := div_ne_zero (wy l) (oy l)
  have cut3:=D.bary (by decide:1≤2) ix px ox d2.active cx wx' fx d2.nz nx injx zero2
  have cut4:=D.bary (by decide:2≤2) iy py oy d3.active cy wy' fy d3.nz ny injy zero3
  have cut3' : (a^2/D.amp i0)*(a-u)+(beta^2/D.amp i1)*(beta-u)=0 := by
    simpa [ix,a,beta,u,Fin.sum_univ_succ] using cut3
  have cut4' : (a^2/D.amp i0)*(a-v)+(beta^2/D.amp i1)*(beta-v)+(u^2/D.amp i2)*(u-v)=0 := by
    simpa [iy,a,beta,u,v,Fin.sum_univ_succ,add_assoc] using cut4
  obtain ⟨Q0,deg0,eq0⟩ := D.masked_primitive (P:=X*Z2 a beta) d2 (j:=3) (by decide) (by decide) zero2
    (Polynomial.natDegree_mul_le.trans (by rw [natDegree_X]; have := degreeZ2 a beta; omega))
    (by simp) (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
                  rcases hz with rfl|rfl <;> simp [Z2])
  obtain ⟨Q1,deg1,eq1⟩ := D.masked_primitive (P:=X*Z3 a beta u) d3 (j:=4) (by decide) (by decide) zero3
    (Polynomial.natDegree_mul_le.trans (by rw [natDegree_X]; have := degreeZ3 a beta u; omega))
    (by simp) (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
                  rcases hz with rfl|rfl|rfl <;> simp [Z3])
  obtain ⟨Q2,deg2,eq2⟩ := D.masked_primitive (P:=X^2*Z3 a beta u) d3 (j:=5) (by decide) (by decide) zero3
    (Polynomial.natDegree_mul_le.trans (by rw [natDegree_X_pow]; have := degreeZ3 a beta u; omega))
    (by simp) (by intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
                  rcases hz with rfl|rfl|rfl <;> simp [Z3])
  have P0 (l : Fin s) (hl : i2 ≤ l) (n : D.base l≠0) :
      (D.clock l)^2*L2 a beta (D.clock l)=D.amp l*Q0.coeff 0 := by
    rw [←primitive2,eq0 l hl n,represent0 deg0]
  have B (l : Fin s) (hl : i3 ≤ l) (n : D.base l≠0) :
      B1 a beta u (D.clock l)=D.amp l*(Q1.coeff 1*(D.clock l)+Q1.coeff 0) ∧
      B2 a beta u (D.clock l)=D.amp l*(Q2.coeff 2*(D.clock l)^2+Q2.coeff 1*(D.clock l)+Q2.coeff 0) := by
    rw [←primitive31,←primitive32,eq1 l hl n,eq2 l hl n,represent1 deg1,represent2 deg2]; exact ⟨rfl,rfl⟩
  apply fourth_impossible (a:=a) (b:=beta) (u:=u) (v:=v) (wv:=D.amp i3)
    (l₁:=Q1.coeff 1) (l₀:=Q1.coeff 0) (q₂:=Q2.coeff 2) (q₁:=Q2.coeff 1) (q₀:=Q2.coeff 0)
    d0.nz d1.nz d2.nz d3.nz ba.symm au bu av bv uv (div_ne_zero wa d0.active) (div_ne_zero wb d1.active) (div_ne_zero wu d2.active) cut3' cut4'
    (P0 i0 h02.le d0.active) (P0 i1 h12.le d1.active) (P0 i2 le_rfl d2.active)
  intro x y h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact B i0 h03.le d0.active
  · exact B i1 h13.le d1.active
  · exact B i2 h23.le d2.active
  · exact B i3 le_rfl d3.active
end
end RKCert.Paired.LocalProjection.WeightedFour

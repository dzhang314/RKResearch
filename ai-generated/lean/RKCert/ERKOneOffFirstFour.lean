module

public import RKCert.ERKOneOffPrefixSelectors

@[expose] public section

/-! # Numbered first four physical rows in the one-off chart
The stage bound is used only to prohibit literal duplicate rows.
On and off stages can share a node; the defect selector distinguishes them. -/
namespace RKCert.Paired.OneOff
open Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s→Fin s→K}

omit [CharZero K] in
theorem firstChartBefore_cast {a d : K} (hs : 4≤s) (q : Fin 4)
    (h : ∀ l : Fin 4, l < q → nodes A (Fin.castLE hs l)=chartNode a d l ∧
      g A (Fin.castLE hs l)=chartDefect a l) :
    FirstChartBefore A a d (Fin.castLE hs q) := by
  intro r rq
  have lt : r.val < q.val := rq
  let l : Fin 4 := ⟨r.val,lt.trans q.isLt⟩
  have eq : Fin.castLE hs l=r := Fin.ext rfl
  exact ⟨l,rfl,eq ▸ h l lt⟩

structure FirstFour (A : Fin s→Fin s→K) (a d : K) (hs : 4≤s) : Prop where
  features : ∀ l : Fin 4,
    nodes A (Fin.castLE hs l)=chartNode a d l ∧
    g A (Fin.castLE hs l)=chartDefect a l ∧
    h A (Fin.castLE hs l)=chartH a d l

theorem first_four_at_uniform_floor {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (floor : max p ((3*p+1)/2-2)=s+1) (hs : 4≤s+1)
    (sep : Separated A 4) (rk3 : finrank K (zeroSpace A 3)=2)
    (rk4 : finrank K (zeroSpace A 4)=3)
    {a d : K} {i j : Fin (s+1)} (D : GlobalNormal A a d i j) :
    FirstFour A a d hs := by
  let e : Fin 4→Fin (s+1) := Fin.castLE hs
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have no_dup {x y : Fin (s+1)} (xy : x < y) (pr : FirstChartBefore A a d y)
      (cx : nodes A x=nodes A y) (gx : g A x=g A y) (hx : h A x=h A y) : False :=
    no_repeat_in_first_chart_at_floor ha ho floor an dn D.base.q2 xy pr cx gx hx
  have mat0 (v : Vec K (s+1)) : mat A v (e 0)=0 := by
    apply causal_mat ha
    intro k kh
    change k.val < 0 at kh
    omega
  have c0 : nodes A (e 0)=0 := by
    simpa [mat_apply,nodes] using mat0 (1:Vec K (s+1))
  have g0 : g A (e 0)=0 := by rw [g_apply,c0,mat0]; simp
  have h0 : h A (e 0)=0 := mat0 (g A)
  have pre1 : FirstChartBefore A a d (e 1) := by
    apply firstChartBefore_cast hs (1:Fin 4)
    intro l ll
    have eq : l=0 := Fin.ext (show l.val=0 by have : l.val < 1 := ll; omega)
    subst l
    simpa [e,chartNode,chartDefect] using And.intro c0 g0
  have i0 : i≠e 0 := by
    intro eq
    apply an
    calc a = nodes A i := D.base.origin.node.symm
         _ = 0 := by rw [eq,c0]
  have i1 : i=e 1 := by
    by_contra ne
    have gt : e 1 < i := by
      have nz : i.val≠0 := fun h=>i0 (Fin.ext h)
      have no : i.val≠1 := fun h=>ne (Fin.ext h)
      change 1 < i.val
      omega
    have c1 := D.base.origin.earlier_node (e 1) gt
    have g1 := D.base.origin.earlier_defect (e 1) gt
    have h1 : h A (e 1)=0 := by
      apply causal_mat ha
      intro k kk
      change k < e 1 at kk
      exact D.base.origin.earlier_defect k (kk.trans gt)
    exact no_dup (show e 0 < e 1 by change (0:ℕ) < 1; decide) pre1
      (c0.trans c1.symm) (g0.trans g1.symm) (h0.trans h1.symm)
  have c1 : nodes A (e 1)=a := i1 ▸ D.base.origin.node
  have g1 : g A (e 1)=baseAmp a := i1 ▸ D.base.origin.defect
  have h1 : h A (e 1)=0 := by
    apply causal_mat ha
    intro k kk
    change k < e 1 at kk
    exact D.base.origin.earlier_defect _ (i1.symm ▸ kk)
  have pre2 : FirstChartBefore A a d (e 2) := by
    apply firstChartBefore_cast hs (2:Fin 4)
    intro l ll
    have cases : l=0 ∨ l=1 := by
      have : l.val < 2 := ll
      rcases show l.val=0 ∨ l.val=1 by omega with eq|eq
      · exact Or.inl (Fin.ext eq)
      · exact Or.inr (Fin.ext eq)
    rcases cases with rfl|rfl
    · simpa [e,chartNode,chartDefect] using And.intro c0 g0
    · simpa [e,chartNode,chartDefect] using And.intro c1 g1
  have j2 : j=e 2 := by
    by_contra ne
    have j0 : j.val≠0 := fun eq=>D.base.first_h.nonzero (by rw [(Fin.ext eq : j=e 0),h0])
    have j1 : j.val≠1 := fun eq=>D.base.first_h.nonzero (by rw [(Fin.ext eq : j=e 1),h1])
    have j2 : j.val≠2 := fun eq=>ne (Fin.ext eq)
    have gt : e 2 < j := by change 2 < j.val; omega
    have hh := D.base.first_h.earlier (e 2) gt
    rcases D.base.first_h.prefix_features (e 2) gt with ⟨c,g⟩|⟨c,g⟩
    · exact no_dup (show e 0 < e 2 by change (0:ℕ) < 2; decide) pre2
        (c0.trans c.symm) (g0.trans g.symm) (h0.trans hh.symm)
    · exact no_dup (show e 1 < e 2 by change (1:ℕ) < 2; decide) pre2
        (c1.trans c.symm) (g1.trans g.symm) (h1.trans hh.symm)
  have c2 : nodes A (e 2)=d := j2 ▸ D.base.node
  have g2 : g A (e 2)=0 := j2 ▸ D.base.clean
  have h2 : h A (e 2)=twoHd a d := j2 ▸ D.base.hj
  have pre3 : FirstChartBefore A a d (e 3) := by
    apply firstChartBefore_cast hs (3:Fin 4)
    intro l ll
    fin_cases l
    · simpa [e,chartNode,chartDefect] using And.intro c0 g0
    · simpa [e,chartNode,chartDefect] using And.intro c1 g1
    · simpa [e,chartNode,chartDefect] using And.intro c2 g2
    · exact (lt_irrefl _ ll).elim
  obtain ⟨r,rg,rc,rh,hpre⟩ := first_doubled_clean_clock ha sep rk3 rk4 D
  have r3 : r=e 3 := by
    by_contra ne
    have Hr : h A r≠0 := by rw [rh]; exact mul_ne_zero an (pow_ne_zero 2 dn)
    have r0 : r.val≠0 := fun eq=>Hr (by rw [(Fin.ext eq : r=e 0),h0])
    have r1 : r.val≠1 := fun eq=>Hr (by rw [(Fin.ext eq : r=e 1),h1])
    have r2 : r.val≠2 := by
      intro eq
      have h : nodes A r=d := by rw [(Fin.ext eq : r=e 2),c2]
      apply dn
      linear_combination h-rc
    have r3 : r.val≠3 := fun eq=>ne (Fin.ext eq)
    have gt : e 3 < r := by change 3 < r.val; omega
    rcases hpre (e 3) gt with ⟨c,g,h⟩|⟨c,g,h⟩|⟨c,g,h⟩
    · exact no_dup (show e 0 < e 3 by change (0:ℕ) < 3; decide) pre3
        (c0.trans c.symm) (g0.trans g.symm) (h0.trans h.symm)
    · exact no_dup (show e 1 < e 3 by change (1:ℕ) < 3; decide) pre3
        (c1.trans c.symm) (g1.trans g.symm) (h1.trans h.symm)
    · exact no_dup (show e 2 < e 3 by change (2:ℕ) < 3; decide) pre3
        (c2.trans c.symm) (g2.trans g.symm) (h2.trans h.symm)
  subst r
  constructor
  intro l
  fin_cases l
  · simpa [e,chartNode,chartDefect,chartH] using And.intro c0 (And.intro g0 h0)
  · simpa [e,chartNode,chartDefect,chartH] using And.intro c1 (And.intro g1 h1)
  · simpa [e,chartNode,chartDefect,chartH] using And.intro c2 (And.intro g2 h2)
  · simpa [e,chartNode,chartDefect,chartH] using And.intro rc (And.intro rg rh)

theorem order9_first_four {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a d : K) (i j : Fin 12), GlobalNormal A a d i j ∧ FirstFour A a d (by decide) := by
  obtain ⟨a,d,i,j,D⟩ := order9_global_normal ha ho hN
  obtain ⟨_,h3,h4,_⟩ := order9_twelve_stage_chart ha ho
  exact ⟨a,d,i,j,D,first_four_at_uniform_floor ha ho (by decide) (by decide)
    (explicit_separated ha ho (by decide) (by decide)) h3 h4 D⟩

theorem order8_first_four {A : Fin 10→Fin 10→K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a d : K) (i j : Fin 10), GlobalNormal A a d i j ∧ FirstFour A a d (by decide) := by
  obtain ⟨a,d,i,j,D⟩ := order8_global_normal ha ho hN
  obtain ⟨_,_,_,_,_,h3,h4,_⟩ := order8_ten_stage_chart ha ho
  exact ⟨a,d,i,j,D,first_four_at_uniform_floor ha ho (by decide) (by decide)
    (explicit_separated ha ho (by decide) (by decide)) h3 h4 D⟩

end RKCert.Paired.OneOff

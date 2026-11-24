module
public import RKCert.FiveDebutPaidCut
@[expose] public section
namespace RKCert.FiveDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape RKCert.FourDebut Polynomial
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s}
open scoped Classical
noncomputable section

/-- A genuine grade-five invariant algebra cannot exhaust an active
numerical clock: its indicator at that clock has zero output mass. -/
theorem outer_five (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U) (inc : U≤zeroSpace A 5) :
    5≤(outerSites (nodes A) U).card := by
  classical
  obtain ⟨e,eu,ev⟩:=core_indicator alg
  have sub : RKCert.Endpoint.activeNonzero (nodes A) b ⊆ outerSites (nodes A) U := by
    intro z hz
    have ⟨_,hn,mass⟩:=Finset.mem_filter.mp hz
    by_contra miss
    apply mass
    have localU (i:Fin s) (clock:nodes A i=z) : Live U i := by
      by_contra no
      exact miss (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,no,clock ▸ hn⟩,clock⟩)
    have probe0:=probe_zeroSpace ho (show 0+5+1≤p by omega) (inc (fiber_mem inv z eu))
    have eqn:probe A b 0 (fiber (nodes A) z e)=RKCert.Endpoint.combinedMass (nodes A) b z := by
      rw [probe,row_apply,RKCert.Endpoint.combinedMass,Finset.sum_filter]
      apply Finset.sum_congr rfl;intro i _
      by_cases h:nodes A i=z <;> simp [fiber,h,ev,localU i]
    rwa [←eqn]
  have le:=Finset.card_le_card sub
  have rk:=RKCert.Endpoint.activeNonzero_card_of_treeOrder ho
  omega

/-- Index evidence for both physical rank cuts. The first three entries
are old, u is the fourth debut, v is the fifth and explicitly refunded. -/
structure FiveData (A : Fin s→Fin s→K) (U : Submodule K (Vec K s)) (w : Vec K s) where
  ix : Fin 3→Fin s
  u : Fin s
  v : Fin s
  before : ∀ k, ix k < u
  uv : u<v
  outside : ∀ k, ¬Live U (ix k)
  nz : ∀ k,nodes A (ix k)≠0
  wi : ∀ k,w (ix k)≠0
  inj : Function.Injective (fun k=>nodes A (ix k))
  d4 : Debut (nodes A) U (Finset.univ.image fun k=>nodes A (ix k)) u
  d5 : Debut (nodes A) U (insert (nodes A u) (Finset.univ.image fun k=>nodes A (ix k))) v
  diag5 : A v v=0

theorem original_five_data (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (f₆ : zeroSpace A 6≤chain (diag (nodes A)) U w 2)
    (f₇ : zeroSpace A 7≤chain (diag (nodes A)) U w 3) : Nonempty (FiveData A U w) := by
  classical
  have outside5:=outer_five ho hp inv alg inc
  obtain ⟨⟨i0,i1,i2,i3,d0,d1,d2,d3⟩⟩:=four_sites (by omega : 4≤(outerSites (nodes A) U).card)
  let a:=nodes A i0
  let b':=nodes A i1
  let c:=nodes A i2
  change Debut (nodes A) U {a} i1 at d1
  change Debut (nodes A) U {a,b'} i2 at d2
  change Debut (nodes A) U {a,b',c} i3 at d3
  have h01 : i0 < i1 := debut_before d0 d1 (by simp) (by simp [a])
  have h12 : i1 < i2 := debut_before d1 d2 (by simp) (by simp [b'])
  have h23 : i2 < i3 := debut_before d2 d3 (by intro z hz;simp only [Finset.mem_insert,Finset.mem_singleton] at *;exact hz.imp id Or.inl) (by simp [c])
  have ba:b'≠a:=fun e=>d1.fresh (by change b'∈{a};simp [e])
  have ac:a≠c:=fun e=>d2.fresh (by change c∈{a,b'};simp [e])
  have bc:b'≠c:=fun e=>d2.fresh (by change c∈{a,b'};simp [e])
  let ix:Fin 3→Fin s:=![i0,i1,i2]
  have old (l:Fin 3):ix l < i3:=by fin_cases l <;> first | exact h01.trans (h12.trans h23) | exact h12.trans h23 | exact h23
  have out (l:Fin 3):¬Live U (ix l):=by fin_cases l <;> first | exact d0.outsideU | exact d1.outsideU | exact d2.outsideU
  have nz (l:Fin 3):nodes A (ix l)≠0:=by fin_cases l <;> first | exact d0.nz | exact d1.nz | exact d2.nz
  have cap : ({a,b'}:Finset K).card≤2 := (Finset.card_insert_le a {b'}).trans (by simp)
  have wa:=early_three ha ho (by omega) inv alg inc f₆ f₇ d0 (by simp)
  have wb:=early_three ha ho (by omega) inv alg inc f₆ f₇ d1 (by simp)
  have wc:=early_three ha ho (by omega) inv alg inc f₆ f₇ d2 cap
  have nonzero (l:Fin 3):w (ix l)≠0:=by fin_cases l <;> first | exact wa | exact wb | exact wc
  have inj : Function.Injective (fun l=>nodes A (ix l)) := by
    intro k l e;fin_cases k <;> fin_cases l <;> first | rfl | exact (ba e).elim | exact (ba e.symm).elim | exact (ac e).elim | exact (ac e.symm).elim | exact (bc e).elim | exact (bc e.symm).elim
  let S:=Finset.univ.image (fun k=>nodes A (ix k))
  have sd : S={a,b',c} := by
    ext z
    simp [S,Finset.mem_image,Fin.exists_fin_succ,ix,a,b',c,eq_comm]
  have fourth : Debut (nodes A) U S i3 := sd ▸ d3
  let T:=insert (nodes A i3) S
  have cardS:S.card≤3 := Finset.card_image_le.trans (by simp)
  have cardT:T.card≤4 := (Finset.card_insert_le _ _).trans (by omega)
  obtain ⟨v,dv⟩:=next_debut T (by omega : T.card < (outerSites (nodes A) U).card)
  have last:i3<v:=debut_before fourth dv (Finset.subset_insert ..) (Finset.mem_insert_self ..)
  have vv:=refund_fifth ha ho (by omega) inv alg inc f₇ dv cardT ix (fun k=>(old k).trans last) out nonzero inj
  exact ⟨ix,i3,v,old,last,out,nz,nonzero,inj,fourth,dv,vv⟩

end
end RKCert.FiveDebut

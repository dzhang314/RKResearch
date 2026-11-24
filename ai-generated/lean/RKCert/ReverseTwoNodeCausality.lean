module
public import RKCert.ReverseTwoNodeScalars
public import RKCert.OrderTwelveReverseRows

@[expose] public section
/-! # Causal two-node confinement, with arbitrary repeated and zero-weight rows -/
namespace RKCert.ReverseTwoNode
open RKCert.Paired RKCert.Paired.OrderTwelve
variable {K : Type*} [Field K] {s : ℕ}

structure TwoNodeRows (N : Vec K s →ₗ[K] Vec K s) (y h g : Vec K s) : Prop where
  first : ∀i, N h i=y i*h i/2+2*g i
  second : ∃ b : K, ∀i, N (powerWeight y h 1) i=y i^2*h i/3+b*g i
  third : ∃ q l : K, ∀i, N (powerWeight y h 2) i=y i^3*h i/4+(q+l*y i)*g i
  advance : ∃ k e : K, ∀i, N g i=(k+e*y i)*g i
  shifted : ∃ m f r : K, ∀i, N (diag y g) i=(m+f*y i+r*y i^2)*g i

theorem earliest (ord : Fin s ≃ Fin s) (P : Fin s → Prop) (h : ∃i,P i) :
    ∃i, P i ∧ ∀ j, ord j < ord i → ¬P j := by
  classical
  let S := Finset.univ.filter P
  obtain ⟨i,hi⟩ := h
  obtain ⟨i,hi,hl⟩ := Finset.exists_min_image S ord ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  exact ⟨i,(Finset.mem_filter.mp hi).2,fun j hj hp=>(not_le_of_gt hj)
    (hl j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩))⟩

theorem prefix_same {ord : Fin s ≃ Fin s} {N : Vec K s →ₗ[K] Vec K s} (hN : Causal ord N)
    (i) (w z : Vec K s) (h : ∀ j, ord j<ord i → w j=z j) : N w i=N z i := by
  have e := hN i (w-z) (fun j hj=>sub_eq_zero.mpr (h j hj))
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using e

theorem prefix_one {ord : Fin s ≃ Fin s} {N : Vec K s →ₗ[K] Vec K s} (hN : Causal ord N)
    (i) (w h : Vec K s) (k : K) (he : ∀ j, ord j<ord i → w j=k*h j) : N w i=k*N h i := by
  simpa only [map_smul,Pi.smul_apply,smul_eq_mul] using prefix_same hN i w (k • h) he

theorem prefix_two {ord : Fin s ≃ Fin s} {N : Vec K s →ₗ[K] Vec K s} (hN : Causal ord N)
    (i) (w h₁ h₂ : Vec K s) (a b : K) (he : ∀ j, ord j<ord i → w j=a*h₁ j+b*h₂ j) :
    N w i=a*N h₁ i+b*N h₂ i := by
  simpa only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
    prefix_same hN i w (a • h₁+b • h₂) he

variable [CharZero K]
/-- If h vanishes on clock zero, an actual strictly causal solution cannot
have three distinct nonzero h sites. The first two distinct h sites are
treated uniformly whether either of them is the original localized site. -/
theorem two_node_confinement (ord : Fin s ≃ Fin s) (N : Vec K s →ₗ[K] Vec K s)
    (hN : Causal ord N) (y h g : Vec K s) (r : TwoNodeRows N y h g)
    (hz : ∀ i, y i=0 → h i=0)
    (hmany : ∀ t u : K, ∃i, h i≠0 ∧ y i≠t ∧ y i≠u) : False := by
  classical
  obtain ⟨b,e2⟩ := r.second
  obtain ⟨q,l,e3⟩ := r.third
  obtain ⟨k,e,e4⟩ := r.advance
  obtain ⟨m,f,z,e5⟩ := r.shifted
  obtain ⟨i,h₀,pre₀⟩ := earliest ord (fun i => h i≠0) (by obtain ⟨i,hh,_,_⟩:=hmany 0 0; exact ⟨i,hh⟩)
  let t := y i
  have ht : t≠0 := fun a=>h₀ (hz i a)
  have p0 (w) (hw : ∀j, ord j<ord i → w j=0) : N w i=0 := hN i w hw
  have htail (j) (hj : ord j < ord i) : h j=0 := not_not.mp (pre₀ j hj)
  have gtail (j) (hj : ord j < ord i) : g j=0 := by
    have he := r.first j
    rw [hN j h (fun j' hj'=>htail j' (lt_trans hj' hj)),htail j hj,mul_zero,zero_div,zero_add] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)
  have p₁ := r.first i
  have p₂ := e2 i
  have p₃ := e3 i
  have p₄ := e4 i
  rw [p0 h htail] at p₁
  rw [p0 _ (by intro j hj; simp [powerWeight,htail j hj])] at p₂ p₃
  rw [p0 g gtail] at p₄
  obtain ⟨_,_,b',ql,ke⟩ := head_first ht h₀ p₁ p₂ p₃ p₄
  change b=4*t/3 at b'
  obtain ⟨v,hv,pre⟩ := earliest ord (fun j => h j≠0 ∧ y j≠t) (by
    obtain ⟨j,hj,ht',_⟩:=hmany t t; exact ⟨j,hj,ht'⟩)
  let u := y v
  have hu : u≠0 := fun a=>hv.1 (hz v a)
  have hut : u≠t := hv.2
  have only_t (j) (hj : ord j < ord v) : y j=t ∨ h j=0 := by
    by_cases h' : h j=0
    · exact Or.inr h'
    · exact Or.inl (by by_contra h''; exact pre j hj ⟨h',h''⟩)
  have powers (j) (hj : ord j ≤ ord v) (n : ℕ) : N (powerWeight y h n) j=t^n*N h j := by
    apply prefix_one hN
    intro j' hj'
    rcases only_t j' (lt_of_lt_of_le hj' hj) with yy|hh <;> simp [powerWeight, *]
  have early (j) (hj : ord j ≤ ord v) : g j=gain t (y j)*h j := by
    apply previous_gain ht
    have w := e2 j
    rw [powers j hj 1,pow_one,r.first,b'] at w
    exact w
  have atV : N g v=gain t t*N h v := by
    apply prefix_one hN; intro j hj
    rw [early j hj.le]
    rcases only_t j hj with yy|hh <;> simp [*]
  have shiftedV : N (diag y g) v=t*N g v := by
    apply prefix_one hN; intro j hj
    change y j*g j=t*g j
    rcases only_t j hj with yy|hh
    · rw [yy]
    · rw [early j hj.le,hh]; ring
  have init₃ := e3 v
  rw [powers v le_rfl 2,r.first] at init₃
  have init₄ := (atV.symm.trans (e4 v))
  rw [r.first] at init₄
  obtain ⟨den,gu,es,ls⟩ := head_second ht hu hut hv.1 (early v le_rfl) ql ke init₃ init₄
  have coeff (x : K) : q+l*x=t^2+slope t u*(u-t)*(x-t) := by
    rw [←ls]; linear_combination ql
  have grow (x : K) : k+e*x=slope t u*(x-t) := by
    rw [←es]; linear_combination ke
  have repeat_coeff : m+f*u+z*u^2=t*(k+e*u) := by
    apply mul_right_cancel₀ gu
    calc (m+f*u+z*u^2)*g v = N (diag y g) v := (e5 v).symm
         _ = t*N g v := shiftedV
         _ = (t*(k+e*u))*g v := by rw [e4]; ring
  let Invariant (j : Fin s) : Prop := (y j=t ∨ y j=u ∨ h j=0) ∧ g j=gain t (y j)*h j
  have main (i : Fin s) : Invariant i := by
    apply (measure (fun j => (ord j).val)).wf.induction i
    intro j ih
    have prev (j' : Fin s) (hj : ord j' < ord j) : Invariant j' := ih j' hj
    let htVec : Vec K s := fun j' => if y j'=t then h j' else 0
    let huVec : Vec K s := fun j' => if y j'=u then h j' else 0
    let T := N htVec j
    let S := N huVec j
    have extval (w : Vec K s) (F : K→K) (hf : ∀j',ord j'<ord j→ w j'=F (y j')*h j') :
        N w j=F t*T+F u*S := by
      apply prefix_two hN j w htVec huVec (F t) (F u)
      intro j' hj; rw [hf j' hj]
      rcases (prev j' hj).1 with yt|yu|hh
      · simp [htVec,huVec,yt,hut.symm]
      · simp [htVec,huVec,yu,hut]
      · simp [htVec,huVec,hh]
    have o1 := (extval h (fun _=>1) (by simp)).symm.trans (r.first j)
    have o2 := (extval (powerWeight y h 1) id (by simp [powerWeight])).symm.trans (e2 j)
    have o3 := (extval (powerWeight y h 2) (fun x=>x^2) (by simp [powerWeight])).symm.trans (e3 j)
    have o4 := (extval g (gain t) (fun j' hj=>(prev j' hj).2)).symm.trans (e4 j)
    have o5 := (extval (diag y g) (fun x=>x*gain t x) (fun j' hj=>by
      change y j'*g j'=y j'*gain t (y j')*h j'; rw [(prev j' hj).2]; ring)).symm.trans (e5 j)
    have rep (he : y j=u) : (u-t)*gain t u*S=0 := by
      rw [he,repeat_coeff] at o5
      rw [he] at o4
      linear_combination o5-t*o4
    rw [b'] at o2
    rw [coeff] at o3
    rw [grow] at o4
    obtain ⟨gj,jzero⟩ := two_node_step ht hu hut den (by simpa only [one_mul] using o1) o2 o3 o4 rep
    refine ⟨?_,gj⟩
    rcases mul_eq_zero.mp jzero with hv|hv
    · rcases mul_eq_zero.mp hv with h0|h0
      · rcases mul_eq_zero.mp h0 with h0|h0
        · exact Or.inr (Or.inr (hz j h0))
        · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h0))
    · exact Or.inr (Or.inr hv)
  obtain ⟨j,hh,ht',hu'⟩ := hmany t u
  exact ((main j).1.elim ht' (fun e=>e.elim hu' hh))

end RKCert.ReverseTwoNode

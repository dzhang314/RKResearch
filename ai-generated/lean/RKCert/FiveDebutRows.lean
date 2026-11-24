module
public import RKCert.FiveDebutSites
public import RKCert.FiveDebutTwoCuts
@[expose] public section
namespace RKCert.FiveDebut.FiveData
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape RKCert.FourDebut Polynomial
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s}
open scoped Classical
noncomputable section

def i4 (h : FiveData A U w) : Fin 4→Fin s := Fin.snoc h.ix h.u
def i5 (h : FiveData A U w) : Fin 5→Fin s := Fin.snoc h.i4 h.v
def z3 (h : FiveData A U w) (i : Fin 3) : K := nodes A (h.ix i)
def z4 (h : FiveData A U w) (i : Fin 4) : K := nodes A (h.i4 i)
def z5 (h : FiveData A U w) (i : Fin 5) : K := nodes A (h.i5 i)
def W3 (h : FiveData A U w) (i : Fin 3) : K := w (h.ix i)
def W4 (h : FiveData A U w) (i : Fin 4) : K := w (h.i4 i)
def W5 (h : FiveData A U w) (i : Fin 5) : K := w (h.i5 i)

variable (h : FiveData A U w)

omit [CharZero K] in
theorem roots4 : Finset.univ.image h.z4=insert (nodes A h.u) (Finset.univ.image h.z3) := by
  ext x;constructor
  · rintro hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    refine Fin.lastCases ?_ (fun j=>?_) i
    · change nodes A ((Fin.snoc h.ix h.u : Fin 4→Fin s) (Fin.last 3))∈insert _ _;rw [Fin.snoc_last];exact Finset.mem_insert_self ..
    · apply Finset.mem_insert_of_mem;exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by simp only [z3,z4,i4,Fin.snoc_castSucc]⟩
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl|mem
    · exact Finset.mem_image.mpr ⟨Fin.last 3,Finset.mem_univ _,by simp only [z4,i4,Fin.snoc_last]⟩
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j.castSucc,Finset.mem_univ _,by simp only [z3,z4,i4,Fin.snoc_castSucc]⟩

omit [CharZero K] in
theorem snoc_inj {n : ℕ} {t : Fin n→Fin s} {new : Fin s}
    (inj : Function.Injective (fun i=>nodes A (t i)))
    (fresh : nodes A new∉Finset.univ.image (fun i=>nodes A (t i))) :
    Function.Injective (nodes A ∘ (Fin.snoc t new : Fin (n+1)→Fin s)) := by
  rw [Fin.comp_snoc]
  apply Fin.snoc_injective_of_injective inj
  rintro ⟨j,e⟩
  exact fresh (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e⟩)

omit [CharZero K] in
theorem inj4 : Function.Injective h.z4 := snoc_inj h.inj h.d4.fresh

omit [CharZero K] in
theorem inj5 : Function.Injective h.z5 :=
  snoc_inj h.inj4 (by change nodes A h.v∉Finset.univ.image h.z4;rw [h.roots4];exact h.d5.fresh)

omit [CharZero K] in
theorem nz4 (i:Fin 4) : h.z4 i≠0 :=
  Fin.lastCases (by simpa only [z4,i4,Fin.snoc_last,Fin.snoc_castSucc] using h.d4.nz) (fun k=>by simpa only [z4,i4,Fin.snoc_last,Fin.snoc_castSucc] using h.nz k) i

omit [CharZero K] in
theorem nz5 (i:Fin 5) : h.z5 i≠0 :=
  Fin.lastCases (by simpa only [z5,i5,Fin.snoc_last,Fin.snoc_castSucc] using h.d5.nz) (fun k=>by simpa only [z5,i5,z4,Fin.snoc_last,Fin.snoc_castSucc] using h.nz4 k) i

omit [CharZero K] in
theorem out4 (i:Fin 4) : ¬Live U (h.i4 i) :=
  Fin.lastCases (by simpa only [i4,Fin.snoc_last,Fin.snoc_castSucc] using h.d4.outsideU) (fun k=>by simpa only [i4,Fin.snoc_last,Fin.snoc_castSucc] using h.outside k) i

omit [CharZero K] in
theorem out5 (i:Fin 5) : ¬Live U (h.i5 i) :=
  Fin.lastCases (by simpa only [i5,Fin.snoc_last,Fin.snoc_castSucc] using h.d5.outsideU) (fun k=>by simpa only [i5,Fin.snoc_last,Fin.snoc_castSucc] using h.out4 k) i

omit [CharZero K] in
theorem before5 (i:Fin 4) : h.i4 i < h.v :=
  Fin.lastCases (by simpa only [i4,Fin.snoc_last,Fin.snoc_castSucc] using h.uv) (fun k=>by simpa only [i4,Fin.snoc_last,Fin.snoc_castSucc] using (h.before k).trans h.uv) i

omit [CharZero K] in
theorem pay5 (i:Fin 5) : h.i5 i < h.v ∨ h.i5 i=h.v ∧ A h.v h.v=0 :=
  Fin.lastCases (Or.inr ⟨by simp only [i5,Fin.snoc_last],h.diag5⟩) (fun k=>Or.inl (by simpa only [i5,Fin.snoc_last,Fin.snoc_castSucc] using h.before5 k)) i

/-- The first three actual sites give the singular initial Hankel matrix. -/
theorem third_singular (ha : LowerArray A) (inv : U.map (diag (nodes A))≤U)
    (alg : MulClosed U) (inc : U≤zeroSpace A 5) (f₅ : chain (diag (nodes A)) U w 1≤zeroSpace A 5)
    (f₆ : zeroSpace A 6≤chain (diag (nodes A)) U w 2) :
    let a:=fun i=>h.z3 i^2/h.W3 i
    sumPower h.z3 a 0*sumPower h.z3 a 2=(sumPower h.z3 a 1)^2 := by
  have cover (l:Fin s) (old:l<h.u) (out:¬Live U l) (nz:nodes A l≠0) :
      ∃k,nodes A l=nodes A (h.ix k) := by
    obtain ⟨k,_,e⟩:=Finset.mem_image.mp (h.d4.old l old out nz);exact ⟨k,e.symm⟩
  let used:Fin 1→Fin 3:=Fin.castLE (by decide)
  obtain ⟨P,Q,pn,dp,p0,dq,fit,got⟩:=paid_paired_cut h.ix h.ix ha inv alg inc f₅ f₆
    h.before h.outside cover (fun k=>Or.inl (h.before k)) h.outside used (fun k=>h.wi (used k))
    (h.inj.comp (Fin.castLE_injective _)) (by decide)
  exact three_cut_singular h.inj h.nz h.wi pn dp p0 dq fit got

/-- The fifth explicit row supplies one more primitive test than the four
input-matching sites. The fourth head being nonzero is a conclusion. -/
theorem fifth_kernel (ha : LowerArray A) (inv : U.map (diag (nodes A))≤U)
    (alg : MulClosed U) (inc : U≤zeroSpace A 6) (f₆ : chain (diag (nodes A)) U w 2≤zeroSpace A 6)
    (f₇ : zeroSpace A 7≤chain (diag (nodes A)) U w 3) :
    let a:=fun i=>h.z4 i^2/h.W4 i
    (∀i,h.W4 i≠0) ∧ sumPower h.z4 a 1=nodes A h.v*sumPower h.z4 a 0 ∧ sumPower h.z4 a 2=nodes A h.v*sumPower h.z4 a 1 := by
  have cover (l:Fin s) (old:l < h.v) (out:¬Live U l) (nz:nodes A l≠0) :
      ∃k,nodes A l=nodes A (h.i4 k) := by
    have mem:=h.d5.old l old out nz
    change nodes A l∈insert _ (Finset.univ.image h.z3) at mem
    rw [←h.roots4] at mem
    obtain ⟨k,_,e⟩:=Finset.mem_image.mp mem;exact ⟨k,e.symm⟩
  let used:Fin 2→Fin 4:=fun i=>(Fin.castLE (by decide : 2≤3) i).castSucc
  have nw (k:Fin 2):w (h.i4 (used k))≠0:=by change w ((Fin.snoc h.ix h.u : Fin 4→Fin s) (Fin.castLE (by decide : 2≤3) k).castSucc)≠0;rw [Fin.snoc_castSucc];exact h.wi _
  have inj : Function.Injective (fun i=>nodes A (h.i4 (used i))) :=
    h.inj4.comp ((Fin.castSucc_injective _).comp (Fin.castLE_injective _))
  obtain ⟨P,Q,pn,dp,p0,dq,fit,got⟩:=paid_paired_cut h.i4 h.i5 ha inv alg inc f₆ f₇
    h.before5 h.out4 cover h.pay5 h.out5 used nw inj (by decide)
  have fresh (i:Fin 4):nodes A h.v≠h.z4 i:=fun e=>h.d5.fresh (by
    change nodes A h.v∈insert _ (Finset.univ.image h.z3)
    rw [←h.roots4,e];exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
  exact five_cut_linear_kernel h.inj4 h.nz4 h.d5.nz fresh pn dp p0 dq fit
    (by simpa only [i5,Fin.snoc_last,Fin.snoc_castSucc] using got (Fin.last 4)) (fun k=>by simpa only [i5,z4,Fin.snoc_last,Fin.snoc_castSucc] using got k.castSucc)

end
end RKCert.FiveDebut.FiveData

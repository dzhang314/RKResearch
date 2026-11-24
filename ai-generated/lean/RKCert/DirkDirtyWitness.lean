module

public import RKCert.DirkClosedProjection
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace RKCert.Paired.Reduce
open RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s} {P : K[X]}

def Dirty (c w : Vec K s) (U : Submodule K (Vec K s)) (i : Fin s) : Prop :=
  Kept c w U i ∧ w i≠0

def Clean (c w : Vec K s) (U : Submodule K (Vec K s)) (i : Fin s) : Prop :=
  Kept c w U i ∧ w i=0

theorem clean_clock {c : Vec K s} {i : Fin s} (h : Clean c w U i) : c i≠0 :=
  h.1.1.2.resolve_right (not_not_intro h.2)

theorem dirty_distinct (h : Grade3Head A U w P) {i j : Fin s}
    (hi : Dirty (nodes A) w U i) (hj : Dirty (nodes A) w U j)
    (he : nodes A i=nodes A j) : i=j := by
  apply kept_unique hi.1 hj.1
  apply Prod.ext he
  change w i=w j
  rw [h.fits i hi.2,h.fits j hj.2,he]

theorem clean_distinct {c : Vec K s} {i j : Fin s}
    (hi : Clean c w U i) (hj : Clean c w U j) (he : c i=c j) : i=j :=
  kept_unique hi.1 hj.1 (Prod.ext he (hi.2.trans hj.2.symm))

theorem clean_or_dirty {c : Vec K s} {i : Fin s} (h : Kept c w U i) :
    Clean c w U i ∨ Dirty c w U i := by
  by_cases e : w i=0
  · exact Or.inl ⟨h,e⟩
  · exact Or.inr ⟨h,e⟩

theorem dirty_sites (h : Grade3Head A U w P) :
    headSites (nodes A) w =
      (Finset.univ.filter (Dirty (nodes A) w U)).image (nodes A) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hw : w i≠0 := (Finset.mem_filter.mp hi).2
    have he : Eligible (nodes A) w U i := ⟨(fun hh => hw (h.disjoint i hh)),Or.inr hw⟩
    let j := first (nodes A) w U i
    have hh := first_signature he
    have hn : w j≠0 := by
      have e : w j=w i := congrArg Prod.snd hh
      rwa [e]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,first_kept he,hn⟩,
      congrArg Prod.fst hh⟩
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact headSites_mem i (Finset.mem_filter.mp hi).2.2

/-- First n genuine retained dirty coordinates, sorted in original chronology. -/
theorem first_dirty_rows (h : Grade3Head A U w P) {n : ℕ} (hn : n≤5) :
    ∃ d : Fin n → Fin s, StrictMono d ∧ (∀ i, Dirty (nodes A) w U (d i)) ∧
      (∀ i : Fin s, Dirty (nodes A) w U i → ∀ j : Fin n, i≤d j →
        ∃ k : Fin n, d k=i ∧ k≤j) := by
  let S : Finset (Fin s) := Finset.univ.filter (Dirty (nodes A) w U)
  have hS := h.sites
  rw [dirty_sites h] at hS
  have cardinal := Finset.card_image_le (s:=S) (f:=nodes A)
  have hl : n≤S.card := by change 4<(S.image (nodes A)).card at hS; omega
  let e := S.orderEmbOfFin rfl
  let d : Fin n → Fin s := fun i => e (Fin.castLE hl i)
  refine ⟨d,e.strictMono.comp (Fin.strictMono_castLE hl),?_,?_⟩
  · intro i
    exact (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl (Fin.castLE hl i))).2
  · intro i hi j hij
    have hmem : i∈Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    obtain ⟨k,rfl⟩ := hmem
    have hk : k ≤ Fin.castLE hl j := e.le_iff_le.mp hij
    have hk' : k.val≤j.val := hk
    have hkn : k.val<n := hk'.trans_lt j.isLt
    exact ⟨⟨k.val,hkn⟩,rfl,hk'⟩

theorem head_polynomial_mem (h : Grade3Head A U w P) {k : ℕ} (hk : k≤3)
    (Q : K[X]) (hQ : Q.natDegree≤k) :
    (fun i => Q.eval (nodes A i)*w i)∈zeroSpace A (3+k) := by
  have ch := h.band k hk
  have pow (j : ℕ) (hj : j≤k) : (diag (nodes A)^j) w∈zeroSpace A (3+k) :=
    (chain_le_iff _).mp ch.ge |>.2 j (by omega)
  rw [show (fun i => Q.eval (nodes A i)*w i) =
      ∑ j ∈ Finset.range (k+1), Q.coeff j • (diag (nodes A)^j) w by
    ext i
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hQ),Finset.sum_mul,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply,smul_eq_mul,pow_diag_apply,mul_assoc]]
  exact (zeroSpace A (3+k)).sum_mem (fun j hj =>
    (zeroSpace A (3+k)).smul_mem _ (pow j (by have := Finset.mem_range.mp hj; omega)))

/-- Adjoining any genuine paid head polynomial to a scalar polynomial. -/
theorem head_trace (h : Grade3Head A U w P) {k : ℕ} (hk : k≤3)
    (f q : K[X]) (hf : f.natDegree≤3+k) (hq : q.natDegree≤k) :
    OrdinaryTrace A (3+k) (evalNodes A f+(fun i => q.eval (nodes A i)*w i)) f :=
  (OrdinaryTrace.scalar A hf).add_pure (head_polynomial_mem h hk q hq)

theorem realize_dirty (h : Grade3Head A U w P) {k : ℕ} (hk : k≤3)
    (V : K[X]) (hd : V.natDegree≤3+k) :
    ∃ f : K[X], f.eval 0=0 ∧ ∃ v : Vec K s,
      OrdinaryTrace A (3+k) v f ∧
      (∀ i, Dirty (nodes A) w U i → restrict (nodes A) w U v i=V.eval (nodes A i)) := by
  let t := V.eval 0 / P.eval 0
  let f := V-C t*P
  have zf : f.eval 0=0 := by simp [f,t,div_mul_cancel₀ _ h.constant_ne]
  have df : f.natDegree≤3+k :=
    (natDegree_sub_le _ _).trans (max_le hd ((natDegree_C_mul_le _ _).trans (by
      have := h.degree
      omega)))
  refine ⟨f,zf,_,head_trace h hk f (C t) df (by simp),?_⟩
  intro i hi
  rw [restrict_apply,ite_eq_left hi.1]
  simp [eval_sub,eval_mul,f,h.fits i hi.2]

theorem clean_contrast (h : Grade3Head A U w P) :
    ∃ θ : Vec K s, OrdinaryTrace A 3 θ P ∧ ∀ i,
      θ i=if Live U i ∨ w i≠0 then 0 else P.eval (nodes A i) := by
  obtain ⟨e,he,heval⟩ := core_indicator h.mulClosed
  let ep : Vec K s := fun i => P.eval (nodes A i)*e i
  have hep := h.core (poly_preserves h.invariant P e he)
  have hw : w∈zeroSpace A 3 := by
    have hb : zeroSpace A 3 = chain (diag (nodes A)) U w 1 := h.band 0 (by decide)
    have hm := (chain_le_iff _).mp hb.ge |>.2 0 (by decide)
    simpa using hm
  refine ⟨evalNodes A P-ep-w,((OrdinaryTrace.scalar A h.degree).sub_pure hep).sub_pure hw,?_⟩
  intro i
  by_cases hi : Live U i
  · simp [ep,heval,hi,h.disjoint i hi]
  · by_cases hz : w i=0
    · simp [ep,heval,hi,hz]
    · simp only [hi,false_or,ite_eq_left hz]
      simp [ep,heval,hi,h.fits i hz]

variable [CharZero K]

theorem exists_clean_nonroot (h : Grade3Head A U w P)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p) :
    ∃ i, Clean (nodes A) w U i ∧ P.eval (nodes A i)≠0 := by
  obtain ⟨θ,hθ,hval⟩ := clean_contrast h
  have hn : diag (nodes A) θ≠0 := by
    intro hz
    have hh := hθ.clock
    rw [hz] at hh
    have hp' := OrdinaryTrace.zero_numeric (k:=1) (by simpa only [pow_one] using hh) h.degree ho hp
    exact h.constant_ne (by rw [hp',eval_zero])
  obtain ⟨i,hi,_⟩ := exists_first_coordinate hn
  have hi' : nodes A i≠0 ∧ θ i≠0 := mul_ne_zero_iff.mp hi
  have hs : ¬ (Live U i ∨ w i≠0) := by
    intro ha
    exact hi'.2 (by simp [hval i,ha])
  have ew : w i=0 := by by_contra hne; exact hs (Or.inr hne)
  have he : Eligible (nodes A) w U i := ⟨(fun h => hs (Or.inl h)),Or.inl hi'.1⟩
  let j := first (nodes A) w U i
  have hn' : nodes A j=nodes A i := congrArg Prod.fst (first_signature he)
  have hw : w j=w i := congrArg Prod.snd (first_signature he)
  refine ⟨j,⟨first_kept he,hw.trans ew⟩,?_⟩
  rw [hn']
  simpa [hval i,hs] using hi'.2

/-- At a retained clean coordinate the reduced tableau has the original
formal primitive, even though it is not itself claimed to have RK order. -/
theorem fold_clean_value (h : Grade3Head A U w P) {n : ℕ} (hl : 3≤n) (hu : n≤5)
    {v : Vec K s} {f : K[X]} (ht : OrdinaryTrace A n v f) (hf0 : f.eval 0=0)
    {i : Fin s} (hi : Clean (nodes A) w U i) :
    mat (foldMatrix A w U) (restrict (nodes A) w U v) i=(formalPrimitive f).eval (nodes A i) := by
  obtain ⟨z,hz,hv⟩ := fold_primitive h hl (by omega) ht hf0
  have hp := hz.pure
  have he := h.band (n+1-3) (by omega)
  rw [show 3+(n+1-3)=n+1 by omega] at he
  rw [he] at hp
  obtain ⟨u,hu,Q,_,heq⟩ := exists_head_poly hp
  have huz : u i=0 := by by_contra hn; exact hi.1.1.1 ⟨u,hu,hn⟩
  have hzi : z i=(formalPrimitive f).eval (nodes A i) := by
    simpa [huz,hi.2,sub_eq_zero] using heq i
  rw [hv,restrict_apply,ite_eq_left hi.1,hzi]

theorem reduced_commutator_pattern (h : Grade3Head A U w P) {k : ℕ} (hk : k≤1)
    {v : Vec K s} {f : K[X]} (ht : OrdinaryTrace A (3+k) v f) (hf0 : f.eval 0=0) :
    ∃ Q : K[X], Q.natDegree≤k+2 ∧ ∀ i,
      commutatorR (mat (foldMatrix A w U)) (diag (nodes A))
        (restrict (nodes A) w U v) i =
          if Kept (nodes A) w U i then Q.eval (nodes A i)*w i else 0 := by
  obtain ⟨z,hz,eq⟩ := fold_commutator h (by omega) (by omega) ht hf0
  rw [show 3+k+2=3+(k+2) by omega] at hz
  obtain ⟨Q,hd,he⟩ := fold_defect_pattern h (by omega) hz
  exact ⟨Q,hd,fun i => (congrFun eq i).trans (he i)⟩

/-- A paid reduced commutator with too many distinct zero dirty samples
vanishes at every retained and discarded slot. -/
theorem reduced_commutator_zero (h : Grade3Head A U w P) {k : ℕ} (hk : k≤1)
    {v : Vec K s} {f : K[X]} (ht : OrdinaryTrace A (3+k) v f) (hf0 : f.eval 0=0)
    {r : ℕ} (d : Fin r → Fin s) (hinj : Function.Injective d) (hd : k+2<r)
    (dirty : ∀ j, Dirty (nodes A) w U (d j))
    (hz : ∀ j, commutatorR (mat (foldMatrix A w U)) (diag (nodes A))
      (restrict (nodes A) w U v) (d j)=0) :
    commutatorR (mat (foldMatrix A w U)) (diag (nodes A))
      (restrict (nodes A) w U v)=0 := by
  obtain ⟨Q,hdeg,hq⟩ := reduced_commutator_pattern h hk ht hf0
  have nInj : Function.Injective (fun j => nodes A (d j)) :=
    fun i j he => hinj (dirty_distinct h (dirty i) (dirty j) he)
  have h0 : Q=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q nInj
    · intro j
      have h' := (hq (d j)).symm.trans (hz j)
      rw [ite_eq_left (dirty j).1] at h'
      exact (mul_eq_zero.mp h').resolve_right (dirty j).2
    · simpa using (show Q.natDegree<r by omega)
  ext i
  simp [hq i,h0]

end
end RKCert.Paired.Reduce

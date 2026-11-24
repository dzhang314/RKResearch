module

public import RKCert.DirkTrace
public import RKCert.DirkSixHeads
public import RKCert.GradedOperators

@[expose] public section

/-! # Short clean traces and the grade-three head parameters -/

namespace RKCert.Paired
open Polynomial RKCert.Endpoint

variable {K : Type*} [Field K] {s p n d H : ℕ}
variable {A : Fin s → Fin s → K} {b v : Vec K s}
variable {P : K[X]}

def commutatorR (N D : Vec K s →ₗ[K] Vec K s) : Vec K s →ₗ[K] Vec K s :=
  D.comp N - N.comp D - N.comp N

theorem mat_zero_before {i : Fin s} (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (hpre : ∀ j < i, v j=0) (j : Fin s) (hj : j < i) : mat A v j=0 := by
  rw [mat_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : j<k
  · rw [ha j k hk,zero_mul]
  · rw [hpre _ ((le_of_not_gt hk).trans_lt hj),mul_zero]

theorem commutatorR_leading {c : Vec K s} {i : Fin s}
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (hpre : ∀ j < i, v j=0) :
    commutatorR (mat A) (diag c) v i = -(A i i)^2*v i := by
  have e := causalDiag_mat ha i v hpre
  have e' := causalDiag_mat ha i (diag c v) (fun j hj => by simp [hpre j hj])
  have e'' := causalDiag_mat ha i (mat A v) (fun j hj => mat_zero_before ha hpre j hj)
  change diag c (mat A v) i - mat A (diag c v) i - mat A (mat A v) i=_
  rw [diag_apply,e',e'',e,diag_apply]
  ring

theorem exists_first_coordinate (h : v≠0) :
    ∃ i : Fin s, v i≠0 ∧ ∀ j < i,v j=0 := by
  classical
  let S : Finset (Fin s) := Finset.univ.filter (fun i => v i≠0)
  have hS : S.Nonempty := by
    by_contra hzero
    apply h
    ext i
    by_contra hn
    exact hzero ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let i := S.min' hS
  refine ⟨i,(Finset.mem_filter.mp (S.min'_mem hS)).2,fun j hj => ?_⟩
  by_contra hnonzero
  exact (not_le.mpr hj) (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnonzero⟩))

namespace OrdinaryTrace
open RKCert.Paired.Clock

theorem clock_pow (h : OrdinaryTrace A n v P) (k : ℕ) :
    OrdinaryTrace A (n+k) ((diag (nodes A)^k) v) (X^k*P) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,pow_succ',mul_assoc,Nat.add_succ]
    exact ih.clock

/-- A short origin-cleared input, supported on genuine clean rows, cannot
have a nonzero polynomial profile when enough local moments remain. -/
theorem clean_short [CharZero K] (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (h : OrdinaryTrace A n v (X*P))
    (hd : P.natDegree≤d) (hp : H+1≤p) (hcap : n+2≤H) (hcap' : n+d+1≤H)
    (hclean : ∀ i : Fin s, v i≠0 → ∀ w∈zeroSpace A H, w i=0)
    (hclock : ∀ i : Fin s, v i≠0 → nodes A i≠0) : P=0 := by
  by_cases hv : v=0
  · subst v
    apply zero_numeric (k:=1) (by simpa only [pow_one] using h) hd ho (by omega)
  obtain ⟨i,hi,hpre⟩ := exists_first_coordinate hv
  have hca : commutatorR (mat A) (diag (nodes A)) v ∈ zeroSpace A (n+2) :=
    commutator_mem_zeroSpace ho n (by omega) h.stage
  have hf := hclean i hi _ (zeroSpace_mono A hcap hca)
  rw [commutatorR_leading ha hpre] at hf
  have hdiag : A i i=0 := sq_eq_zero_iff.mp
    (neg_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hi))
  apply primitive_shift_detect P hd _ (hclock i hi)
  intro k
  let w := (diag (nodes A)^k.val) v
  have hs : OrdinaryTrace A (n+k.val) w (X^(1+k.val)*P) := by
    simpa only [←mul_assoc,←pow_succ,pow_one,Nat.add_comm 1 k.val] using h.clock_pow k.val
  have hm := hs.primitive
  have hpre' : ∀ j < i, w j=0 := by
    intro j hj
    simp only [w,pow_diag_apply,hpre j hj,mul_zero]
  have hz : mat A w i=0 := by
    simpa only [hdiag,zero_mul] using causalDiag_mat ha i w hpre' 
  have hf' := hclean i hi _ (zeroSpace_mono A (by have := k.isLt; omega) hm.pure)
  simpa only [Pi.sub_apply,hz,evalNodes_apply,zero_sub,neg_eq_zero] using hf'

end OrdinaryTrace
end RKCert.Paired

namespace RKCert.Paired.Clock
open RKCert.OneEscape Polynomial RKCert.Endpoint

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

structure Grade3Head (A : Fin s → Fin s → K) (U : Submodule K (Vec K s)) (w : Vec K s)
    (P : K[X]) : Prop where
  invariant : U.map (diag (nodes A))≤U
  core : U≤zeroSpace A 3
  mulClosed : MulClosed U
  disjoint : ∀ i, Live U i → w i=0
  sites : 4<(headSites (nodes A) w).card
  band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) U w (1+k)
  degree : P.natDegree≤3
  constant_ne : P.eval 0≠0
  fits : ∀ i, w i≠0 → w i=P.eval (nodes A i)

theorem grade3_head_if_noninvariant (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (bad : ¬ Module.finrank K (zeroSpace A 3)+4≤Module.finrank K (zeroSpace A 6))
    (inv : ¬ (zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3) :
    ∃ U w P, Grade3Head A U w P := by
  classical
  obtain ⟨r,U,w,P,hr,hU,hUF,hmul,disjoint,sites,band,Pne,dP,fit⟩ :=
    dirk_six_head_starts_at_three ha ho hp bad inv
  have Pd : P.natDegree≤3 := by omega
  obtain ⟨e,he,evalE⟩ := core_indicator hmul
  let eP : Vec K s := fun i => P.eval (nodes A i)*e i
  let theta := evalNodes A P-eP-w
  have pis (k : ℕ) (hk : k<r) : (diag (nodes A)^k) w∈zeroSpace A 3 := by
    have hb : zeroSpace A 3=chain (diag (nodes A)) U w r := by simpa using band 0 (by decide)
    exact (chain_le_iff r).mp hb.ge |>.2 k hk
  have hw : w∈zeroSpace A 3 := by simpa using pis 0 hr
  have htheta : OrdinaryTrace A 3 theta P :=
    ((OrdinaryTrace.scalar A Pd).sub_pure (hUF (poly_preserves hU P e he))).sub_pure hw
  have ztheta (i : Fin s) : theta i =
      if Live U i ∨ w i≠0 then 0 else P.eval (nodes A i) := by
    by_cases hl : Live U i
    · simp [theta,eP,evalE,hl,disjoint i hl]
    · by_cases hn : w i=0
      · simp [theta,eP,evalE,hl,hn]
      · simp only [hl,false_or,ite_eq_left hn]
        simp [theta,eP,evalE,hl,fit i hn]
  have clean (i : Fin s) (h : theta i≠0) (v : Vec K s)
      (hv : v∈zeroSpace A 6) : v i=0 := by
    have hh : ¬(Live U i ∨ w i≠0) := by
      intro hn; exact h (by simp [ztheta i,hn])
    have hz : w i=0 := by by_contra hn; exact hh (Or.inr hn)
    have hb : zeroSpace A 6=chain (diag (nodes A)) U w (r+3) := band 3 (by decide)
    rw [hb] at hv
    obtain ⟨u,hu,Q,_,heq⟩ := exists_head_poly hv
    have h0 : u i=0 := by by_contra hn; exact hh (Or.inl ⟨u,hu,hn⟩)
    simpa [h0,hz] using heq i
  have eqr : r=1 := by
    by_contra hne
    have hdeg : P.natDegree≤2 := by omega
    let v := diag (nodes A) theta
    have hP : (X*P).natDegree≤3 := natDegree_mul_le.trans (by rw [natDegree_X]; omega)
    have heP : diag (nodes A) eP∈U := by
      exact hU (Submodule.mem_map_of_mem (poly_preserves hU P e he))
    have hdiag : diag (nodes A) w∈zeroSpace A 3 := by simpa using pis 1 (by omega)
    have eV : v=evalNodes A (X*P)-diag (nodes A) eP-diag (nodes A) w := by
      unfold v theta
      rw [map_sub,map_sub]
      congr 1; congr 1
      ext i; simp [eval_mul]
    obtain hz := OrdinaryTrace.clean_short (n:=3) (d:=2) (H:=6) ha ho
      (show OrdinaryTrace A 3 v (X*P) from eV.symm ▸
        (((OrdinaryTrace.scalar A hP).sub_pure (hUF heP)).sub_pure hdiag)) hdeg
      (by omega) (by decide) (by decide)
      (fun i h _ hw => clean i (fun e => h (by simp [v,e])) _ hw)
      (fun i h e => h (by simp [v,e]))
    exact Pne hz
  have P0 : P.eval 0≠0 := by
    intro hz
    have hX : X∣P := by rw [X_dvd_iff,coeff_zero_eq_eval_zero]; exact hz
    obtain ⟨Q,hQ⟩ := hX
    have qne : Q≠0 := by intro e; simp [hQ,e] at Pne
    have degQ : Q.natDegree≤2 := by
      rw [hQ,natDegree_mul X_ne_zero qne,natDegree_X] at Pd
      omega
    have ht : OrdinaryTrace A 3 theta (X*Q) := hQ ▸ htheta
    apply qne
    apply OrdinaryTrace.clean_short (n:=3) (d:=2) (H:=6) ha ho ht degQ
      (by omega) (by decide) (by decide) clean
    intro i hi h0
    by_cases hl : Live U i ∨ w i≠0
    · exact hi (by simp [ztheta i,hl])
    · exact hi (by simp [ztheta i,hl,h0,hz])
  subst r
  exact ⟨U,w,P,hU,hUF,hmul,disjoint,sites,band,Pd,P0,fit⟩

end RKCert.Paired.Clock

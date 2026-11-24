module
public import RKCert.ReviewedNative.FiniteOrderedSignWindows
import Mathlib.Tactic.Ring

@[expose] public section
/-! # One positive weight, separated by the actual finite sign runs

Adding an earlier nonzero sample of the same sign costs nothing.
An opposite sign adds one midpoint factor. The induction tracks the
existing sign on the entire prefix to the left of the first sample. -/
namespace RKCert.ReviewedNative.FiniteOrderedSigns
open Polynomial SignType
open RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem pos_mul_of_same_sign {a b v : K} (s : sign a = sign b)
    (p : 0 < b*v) : 0 < a*v := by
  rcases mul_pos_iff.mp p with ⟨bp,vp⟩ | ⟨bn,vn⟩
  · exact mul_pos (sign_eq_one_iff.mp (s.trans (sign_pos bp))) vp
  · exact mul_pos_of_neg_of_neg (sign_eq_neg_one_iff.mp (s.trans (sign_neg bn))) vn

private theorem neg_mul_of_other_sign {a b v : K} (an : a ≠ 0)
    (s : sign a ≠ sign b) (p : 0 < b*v) : a*v < 0 := by
  rcases mul_pos_iff.mp p with ⟨bp,vp⟩ | ⟨bn,vn⟩ <;>
    rcases lt_or_gt_of_ne an with aNeg | aPos
  · exact mul_neg_of_neg_of_pos aNeg vp
  · exact False.elim (s ((sign_pos aPos).trans (sign_pos bp).symm))
  · exact False.elim (s ((sign_neg aNeg).trans (sign_neg bn).symm))
  · exact mul_neg_of_pos_of_neg aPos vn

/-- An internal witness, without a separately constructed cut set. -/
private theorem separator_nonzero_list (p : K×K) (rest : List (K×K))
    (inc : (p::rest).Pairwise (fun a b => a.1<b.1))
    (live : ∀ a∈p::rest, a.2≠0) :
    ∃ T : K[X], T.natDegree ≤ ((p::rest).map Prod.snd).signVariations ∧
      (∀ a∈p::rest, 0<a.2*T.eval a.1) ∧
      (∀ y≤p.1, 0<p.2*T.eval y) := by
  induction rest generalizing p with
  | nil =>
      have pn := live p (by simp)
      refine ⟨C p.2, by simp, ?_, ?_⟩
      · intro a ha
        have eq : a=p := by simpa using ha
        subst a
        simpa only [eval_C] using (mul_self_pos.mpr pn)
      · intro y _
        simpa only [eval_C] using (mul_self_pos.mpr pn)
  | cons q qs ih =>
      have hpq : p.1<q.1 := (List.pairwise_cons.mp inc).1 q (by simp)
      have incQ := (List.pairwise_cons.mp inc).2
      have pn := live p (by simp)
      have qn := live q (by simp)
      obtain ⟨T,td,fit,left⟩ := ih q incQ
        (fun a ha => live a (List.mem_cons_of_mem _ ha))
      have count : ((p::q::qs).map Prod.snd).signVariations =
          ((q::qs).map Prod.snd).signVariations +
            (if sign p.2=sign q.2 then 0 else 1) := by
        simpa only [List.map_cons] using
          (List.signVariations_cons_cons_of_ne_zero (qs.map Prod.snd) pn qn)
      by_cases s : sign p.2=sign q.2
      · have hp (y : K) (hy : y≤p.1) : 0<p.2*T.eval y :=
          pos_mul_of_same_sign s (left y (hy.trans hpq.le))
        refine ⟨T, ?_, ?_, hp⟩
        · rw [count,ite_eq_left s,Nat.add_zero]; exact td
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hp _ le_rfl
          · exact fit _ ha
      · let z := (p.1+q.1)/2
        have pz : p.1<z := left_lt_add_div_two.mpr hpq
        have zq : z<q.1 := add_div_two_lt_right.mpr hpq
        have at_eval (v y : K) :
            v*((X-C z)*T).eval y = (v*T.eval y)*(y-z) := by
          simp only [eval_mul,eval_sub,eval_X,eval_C]
          ring
        have hp (y : K) (hy : y≤p.1) : 0<p.2*((X-C z)*T).eval y := by
          rw [at_eval]
          exact mul_pos_of_neg_of_neg (neg_mul_of_other_sign pn s (left y (hy.trans hpq.le)))
            (sub_neg.mpr (hy.trans_lt pz))
        refine ⟨(X-C z)*T, ?_, ?_, hp⟩
        · rw [count,ite_eq_right s]
          exact natDegree_mul_le.trans (by rw [natDegree_X_sub_C]; omega)
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hp _ le_rfl
          · have qa : q.1≤a.1 := by
              rcases List.mem_cons.mp ha with rfl | h
              · exact le_rfl
              · exact ((List.pairwise_cons.mp incQ).1 a h).le
            rw [at_eval]
            exact mul_pos (fit a ha) (sub_pos.mpr (zq.trans_le qa))

/-- A degree-bounded separator for a single finite sample family. -/
theorem exists_grid_separator {n : ℕ} {x a : Fin n → K}
    (inc : StrictMono x) (live : ∃ i, a i≠0) :
    ∃ T : K[X], T.natDegree ≤ (List.ofFn a).signVariations ∧
      ∀ i, a i≠0 → 0<a i*T.eval (x i) := by
  classical
  let ys := List.ofFn (fun i => (x i,a i))
  let nz := ys.filter (fun u => !decide (u.2=0))
  have ordered : ys.Pairwise (fun p q => p.1<q.1) :=
    List.pairwise_ofFn.mpr (fun _ _ ij => inc ij)
  have nzOrd : nz.Pairwise (fun p q => p.1<q.1) := ordered.filter _
  have nonzero (p : K×K) (hp : p∈nz) : p.2≠0 := by
    have h := (List.mem_filter.mp hp).2
    simpa using h
  have mem (i : Fin n) (hi : a i≠0) : (x i,a i)∈nz :=
    List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [hi]⟩
  have mapY : ys.map Prod.snd = List.ofFn a := by
    simp only [ys,List.map_ofFn,Function.comp_def]
  have mapN : nz.map Prod.snd =
      (ys.map Prod.snd).filter (fun u => !decide (u=0)) := by
    simp only [List.filter_map,nz,Function.comp_def]
  have count : (nz.map Prod.snd).signVariations = (List.ofFn a).signVariations := by
    rw [mapN,List.signVariations_filter_ne_zero,mapY]
  cases en : nz with
  | nil =>
      obtain ⟨i,hi⟩ := live
      have h := mem i hi
      rw [en] at h
      exact False.elim (List.not_mem_nil h)
  | cons p rest =>
      obtain ⟨T,d,fit,_⟩ := separator_nonzero_list p rest
        (by simpa only [en] using nzOrd)
        (fun u hu => nonzero u (by rwa [en]))
      refine ⟨T, d.trans_eq (by rw [←en,count]), ?_⟩
      intro i hi
      exact fit (x i,a i) (by simpa only [en] using mem i hi)

private theorem paid_polynomial_test {l r : K} {B T : K[X]} {m : ℕ}
    (td : T.natDegree<m) (paid : ∀ k : Fin m, integral l r (B*X^k.val)=0) :
    integral l r (B*T)=0 := by
  let L : K[X] →ₗ[K] K := (integral l r).comp (LinearMap.mulLeft K B)
  have hpaid (k : Fin m) : L (X^k.val)=0 := by
    simpa only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply] using paid k
  have h : L T=0 := by
    rw [T.as_sum_range' m td,map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    have p : L (X^k)=0 := hpaid ⟨k,Finset.mem_range.mp hk⟩
    rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul,p,smul_zero]
  simpa only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply] using h

/-- One strictly positive weight with m paid monomial moments forces m
changes on the common ordered grid. -/
theorem grid_variation_of_positive_moments {l r : K} {P U : K[X]} {m : ℕ}
    (lr : l<r) (pn : P≠0) (small : P.natDegree<19)
    (budget : U.natDegree+P.natDegree+(m-1)≤19)
    (uPos : ∀ x∈Set.Ioo l r, 0<U.eval x)
    (paid : ∀ k : Fin m, integral l r (U*P*X^k.val)=0) :
    m≤gridVariation P l r := by
  by_contra no
  have less : gridVariation P l r<m := lt_of_not_ge no
  have live := exists_nonzero_grid_sample lr pn small
  obtain ⟨T,td,fit⟩ := exists_grid_separator (intervalPoint_strictMono lr) live
  have tsmall : T.natDegree<m := td.trans_lt (by simpa only [gridVariation_eq] using less)
  have zero := paid_polynomial_test tsmall paid
  have integrand : (U*P*T).natDegree≤19 := by
    have u := natDegree_mul_le (p:=U) (q:=P)
    have v := natDegree_mul_le (p:=U*P) (q:=T)
    omega
  have strict (i : Fin 19) (ne : P.eval (intervalPoint l r i)≠0) :
      0<(U*P*T).eval (intervalPoint l r i) := by
    simp only [eval_mul,mul_assoc]
    exact mul_pos (uPos _ (intervalPoint_mem lr i)) (fit i ne)
  have nonneg (i : Fin 19) : 0≤(U*P*T).eval (intervalPoint l r i) := by
    by_cases z : P.eval (intervalPoint l r i)=0
    · simp [eval_mul,z]
    · exact (strict i z).le
  obtain ⟨i,hi⟩ := live
  exact (integral_pos_of_grid_samples lr integrand nonneg ⟨i,strict i hi⟩).ne' zero

end
end RKCert.ReviewedNative.FiniteOrderedSigns

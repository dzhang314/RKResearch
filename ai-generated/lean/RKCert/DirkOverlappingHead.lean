module
public import RKCert.CoreSupport
public import RKCert.DirkPolynomialMarked
@[expose] public section
namespace RKCert.Paired.Clock
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] {s n d:ℕ} {c w g:Vec K s} {U:Submodule K (Vec K s)}
noncomputable section

/-- A scalar head multiplier in the invariant core vanishes on every live
head knot, without choosing Euclidean complements or distinct rows. -/
theorem scalar_head_vanishes (invariant:U.map (diag c)≤U)
    (norm:∀a,fiber c a w∈U → fiber c a w=0) {P:K[X]}
    (inside:weightedEval c w P∈U) (a:K) (live:a∈headSites c w) :P.eval a=0:=by
  classical
  by_contra non
  apply nonzero_fiber live (norm a _)
  apply (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr non)).mp
  have eqn:P.eval a • fiber c a w=fiber c a (weightedEval c w P):=by
    ext i
    by_cases h:c i=a <;> simp [fiber,h]
  rw [eqn];exact fiber_mem invariant a inside

/-- In two overlapping real stage bands, successive cheap clock powers of
the early head bound its true polynomial coefficient in the later head.
No closure under coordinate products is needed for this linear step. -/
theorem overlapping_head_degree (invariant:U.map (diag c)≤U)
    (norm:∀a,fiber c a w∈U → fiber c a w=0) (count:n<(headSites c w).card)
    (band:∀k≤d,(diag c^k) g∈chain (diag c) U w n) :
    ∃u∈U,∃L:K[X], (L=0 ∨ L.natDegree+d<n) ∧
      ∀i,g i=u i+L.eval (c i)*w i:=by
  classical
  obtain ⟨u,hu,L,hd,rep⟩:=exists_head_poly (band 0 (Nat.zero_le _))
  have fitted(i:Fin s):g i=u i+ L.eval (c i)*w i:=by simpa using rep i
  have higher:∀k≤d,(X^k*L).degree<(n:WithBot ℕ):=by
    intro k
    induction k with
    | zero=>intro _;simpa using hd
    | succ k ih=>
      intro low
      have prev:=ih (by omega)
      obtain ⟨u',hu',T,dT,e⟩:=exists_head_poly (band (k+1) low)
      let P:=X^(k+1)*L-T
      have nz:weightedEval c w P∈U:=by
        have eqn:weightedEval c w P=u'-(diag c^(k+1)) u:=by
          ext i
          have z:=e i
          rw [pow_diag_apply,fitted] at z
          simp only [P,weightedEval_apply,eval_sub,eval_mul,eval_pow,eval_X,Pi.sub_apply,pow_diag_apply]
          linear_combination z
        rw [eqn];exact U.sub_mem hu' (pow_mem invariant hu _)
      have deg:(X^(k+1)*L).degree≤(n:WithBot ℕ):=by
        by_cases no:L=0
        · simp [no]
        have xn:X^k*L≠0:=mul_ne_zero (pow_ne_zero _ X_ne_zero) no
        have dx: (X^k*L).natDegree<n :=(natDegree_lt_iff_degree_lt xn).mpr prev
        have corr:X^(k+1)*L=X*(X^k*L):=by rw [pow_succ'];ring
        rw [corr,degree_eq_natDegree (mul_ne_zero X_ne_zero xn),natDegree_X_mul xn]
        exact_mod_cast (show (X^k*L).natDegree+1≤n by omega)
      have equal:P=0:=eq_zero_of_degree_lt_of_eval_finset_eq_zero (headSites c w)
        ((degree_sub_le _ _).trans_lt ((max_le deg dT.le).trans_lt (by exact_mod_cast count)))
        (scalar_head_vanishes invariant norm nz)
      have e0:X^(k+1)*L=T:=sub_eq_zero.mp equal
      rw [e0];exact dT
  refine ⟨u,hu,L,?_,fitted⟩
  by_cases l0:L=0
  · exact Or.inl l0
  · right
    have de:=(natDegree_lt_iff_degree_lt (mul_ne_zero (pow_ne_zero d X_ne_zero) l0)).mpr (higher d le_rfl)
    rw [natDegree_mul (pow_ne_zero d X_ne_zero) l0,natDegree_X_pow] at de
    omega
end
end RKCert.Paired.Clock


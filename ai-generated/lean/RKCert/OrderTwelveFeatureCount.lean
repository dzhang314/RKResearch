module
public import RKCert.StagePrimitives
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.LinearCombination
@[expose] public section

/-! # The multiplicity-sensitive physical feature count at explicit order 12

Two stage rows at the same numerical knot can have different head values.
A shared zero of the mesh and the terminal multiplier pays for both values.
The knot zero always pays one unused multiplicity, even when a nonzero head
feature is at zero. No splitting, real ordering, or simple-root assumption. -/
namespace RKCert.Paired.OrderTwelve
open Polynomial
variable {K:Type*} [Field K]

private def slice [DecidableEq K] (S:Finset (K×K)) (x:K) : Finset (K×K) :=
  S.filter (fun w=>w.1=x)

omit [Field K] in
private theorem slice_mem [DecidableEq K] {S:Finset (K×K)} {x:K} {w:K×K} :
    w∈slice S x ↔ w∈S ∧ w.1=x := by simp [slice]

omit [Field K] in
private theorem slice_le_one [DecidableEq K] {S:Finset (K×K)} {x:K} {q:K}
    (h:∀ w∈S,w.1=x→w.2=q) : (slice S x).card≤1 := by
  apply Finset.card_le_one.mpr
  intro w hw w' hw'
  obtain ⟨hw,e⟩:=slice_mem.mp hw
  obtain ⟨hw',e'⟩:=slice_mem.mp hw'
  exact Prod.ext (e.trans e'.symm) ((h w hw e).trans (h w' hw' e').symm)

private theorem slice_le_two [DecidableEq K] (S:Finset (K×K)) (x a b:K)
    (h:∀ w∈S,w.1=x→w.2^2-a*w.2-b=0) : (slice S x).card≤2 := by
  classical
  let P:K[X]:=X^2-C a*X-C b
  have hdeg:P.natDegree≤2 := by
    unfold P
    apply (natDegree_sub_le _ _).trans
    apply max_le _ (by simp)
    apply (natDegree_sub_le _ _).trans
    apply max_le (by simp)
    exact natDegree_mul_le.trans (by simp)
  have hne:P≠0 := by
    intro hh
    have he:=congrArg (fun Q:K[X]=>Q.coeff 2) hh
    norm_num [P,Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X] at he
  apply (Finset.card_le_card_of_injOn Prod.snd (s:=slice S x) (t:=P.roots.toFinset) ?_ ?_).trans
    ((Multiset.toFinset_card_le P.roots).trans ((Polynomial.card_roots' P).trans hdeg))
  · intro w hw
    obtain ⟨hh,e⟩:=slice_mem.mp hw
    change w.2∈P.roots.toFinset
    rw [Multiset.mem_toFinset,Polynomial.mem_roots hne,Polynomial.IsRoot.def]
    simpa [P] using h w hh e
  · intro p hp q hq e
    exact Prod.ext ((slice_mem.mp hp).2.trans (slice_mem.mp hq).2.symm) e

private theorem multiplicity_packet [DecidableEq K] {P:K[X]} {S:Finset (K×K)} {z:K}
    (h:∀ x, (slice S x).card+(if x=z then 1 else 0)≤rootMultiplicity x P) :
    S.card+1≤P.natDegree := by
  let M : Multiset K := S.val.map Prod.fst+{z}
  have hm : M≤P.roots := by
    apply Multiset.le_iff_count.mpr
    intro x
    rw [show M=S.val.map Prod.fst+{z} from rfl,Multiset.count_add,
      Multiset.count_singleton,Multiset.count_map,Polynomial.count_roots]
    have e : (S.val.filter (fun w => x=w.1)).card=(slice S x).card := by
      unfold slice
      change _ = ((S.filter (fun w => w.1=x)).val).card
      rw [Finset.filter_val]
      congr 1
      exact Multiset.filter_congr (fun a _ => eq_comm)
    rw [e]
    exact h x
  have hc := (Multiset.card_le_card hm).trans (card_roots' P)
  simpa only [M,Multiset.card_add,Multiset.card_map,Multiset.card_singleton,Finset.card] using hc

/-- In the nonzero ghost case of the final rank-two chart there are at most
eleven head features. The actual terminal multiplier may be the zero polynomial. -/
theorem head_feature_bound (S:Finset (K×K)) (D H Q R:K[X])
    (hD:D.natDegree=5) (hH:H.natDegree≤6) (hQ:Q.natDegree≤2) (hR:R.natDegree≤4)
    (hcop:IsCoprime D H) (h0:H.eval 0=0)
    (hS:∀ w∈S,w.2≠0 ∧ (X*D).eval w.1=w.2*Q.eval w.1 ∧
      w.2^2=H.eval w.1+w.2*R.eval w.1) : S.card≤11 := by
  classical
  let F:=X*D
  let P:=F^2-F*Q*R-H*Q^2
  have hd : D≠0 := by intro h; simp [h] at hD
  have hf : F≠0 := mul_ne_zero X_ne_zero hd
  have hfdeg : F.natDegree=6 := by rw [show F=X*D from rfl,natDegree_mul X_ne_zero hd,natDegree_X,hD]
  have hp : P≠0 := by
    intro hz
    by_cases q:Q=0
    · have h := pow_ne_zero 2 hf
      apply h
      simpa [P,q] using hz
    · have eq : F^2-F*Q*R=H*Q^2 := sub_eq_zero.mp hz
      have lhs : D∣F^2-F*Q*R := by
        have hh : D∣F := dvd_mul_left D X
        exact dvd_sub (hh.trans (dvd_pow_self _ (by decide))) ((hh.trans (dvd_mul_right F Q)).trans
          (dvd_mul_right (F*Q) R))
      rw [eq,mul_comm] at lhs
      have hh := natDegree_le_of_dvd (hcop.dvd_of_dvd_mul_right lhs) (pow_ne_zero 2 q)
      rw [hD,natDegree_pow] at hh
      omega
  have hdeg : P.natDegree≤12 := by
    unfold P
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans (natDegree_sub_le _ _)
      apply max_le
      · rw [natDegree_pow,hfdeg]
      · have u := natDegree_mul_le (p:=F*Q) (q:=R)
        have v := natDegree_mul_le (p:=F) (q:=Q)
        omega
    · have u := natDegree_mul_le (p:=H) (q:=Q^2)
      rw [natDegree_pow] at u
      omega
  have hroot (w:K×K) (hw:w∈S) : P.eval w.1=0 := by
    obtain ⟨_,ha,hb⟩:=hS w hw
    have he : P.eval w.1=(F.eval w.1)^2-F.eval w.1*(Q.eval w.1)*(R.eval w.1)-
        H.eval w.1*(Q.eval w.1)^2 := by simp [P]
    rw [he]
    change F.eval w.1=w.2*Q.eval w.1 at ha
    rw [ha]
    linear_combination (Q.eval w.1)^2*hb
  have hroot0 : P.eval 0=0 := by simp [P,F,h0]
  have hdbl {x:K} (xF:F.eval x=0) (xQ:Q.eval x=0) : 2≤rootMultiplicity x P := by
    apply (le_rootMultiplicity_iff hp).mpr
    have a : X-C x∣F := dvd_iff_isRoot.mpr xF
    have b : X-C x∣Q := dvd_iff_isRoot.mpr xQ
    exact dvd_sub (dvd_sub (pow_dvd_pow_of_dvd a 2)
      ((by rw [pow_two]; exact mul_dvd_mul a b : (X-C x)^2∣F*Q).trans (dvd_mul_right _ R)))
      ((pow_dvd_pow_of_dvd b 2).trans (dvd_mul_left _ H))
  have hcard := multiplicity_packet (P:=P) (S:=S) (z:=(0:K)) (by
    intro x
    by_cases e:x=0
    · subst x
      simp only [ite_true]
      have slice0 : (slice S 0).card≤1 := by
        apply slice_le_one (q:=R.eval 0)
        intro w hw hz
        have h:= (hS w hw).2.2
        rw [hz,h0,zero_add] at h
        apply (mul_left_cancel₀ (hS w hw).1)
        simpa [pow_two] using h
      by_cases hq:Q.eval 0=0
      · exact (by omega : (slice S 0).card+1≤2) |>.trans
          (hdbl (by simp [F]) hq)
      · have hh : slice S 0=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hw,he⟩:=slice_mem.mp hw
          have h:=(hS w hw).2.1
          rw [he,eval_mul,eval_X,zero_mul] at h
          exact (mul_ne_zero (hS w hw).1 hq) h.symm
        rw [hh,Finset.card_empty,zero_add]
        exact (rootMultiplicity_pos hp).mpr hroot0
    · simp only [ite_eq_right e,add_zero]
      by_cases n:(slice S x).Nonempty
      · obtain ⟨w,hw⟩:=n
        obtain ⟨hw,he⟩:=slice_mem.mp hw
        have hh (y:K×K) (hy:y∈S) (h:y.1=x) :
            y.2^2-R.eval x*y.2-H.eval x=0 := by
          have he := (hS y hy).2.2
          rw [h] at he
          linear_combination he
        by_cases hq:Q.eval x=0
        · have hx := (hS w hw).2.1
          rw [he,hq,mul_zero] at hx
          exact (slice_le_two S x (R.eval x) (H.eval x) hh).trans (hdbl hx hq)
        · have hle : (slice S x).card≤1 := by
            apply slice_le_one (q:=F.eval x/Q.eval x)
            intro y hy hz
            apply (eq_div_iff hq).mpr
            have hh := (hS y hy).2.1
            rwa [hz,eq_comm] at hh
          apply hle.trans
          apply (rootMultiplicity_pos hp).mpr
          simpa only [Polynomial.IsRoot.def,he] using hroot w hw
      · simp [Finset.not_nonempty_iff_eq_empty.mp n])
  omega

end RKCert.Paired.OrderTwelve


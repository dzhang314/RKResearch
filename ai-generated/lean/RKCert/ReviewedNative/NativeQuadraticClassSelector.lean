module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Singleton exclusion on a saturated quadratic complete intersection

The finite set consists of distinct literal (clock, amplitude) pairs.
The clock multiset retains both members of a genuinely double fibre.
No quadrature, positivity, tableau, or chronology is required here. -/
namespace RKResearch.Certified.Graded.NativeQuadraticClassSelector

open Polynomial
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
variable {G Q R P H J : K[X]}

/-- Eliminate the amplitude from G(a)=Q(a)z and z²=R(a)z+P(a). -/
def eliminant (G Q R P : K[X]) : K[X] := (G-R*Q)*G-P*Q^2

def clockFiber (S : Finset (K×K)) (a : K) : Finset (K×K) :=
  S.filter (fun p => a=p.1)

theorem mem_clockFiber {S : Finset (K×K)} {a : K} {p : K×K} :
    p∈clockFiber S a ↔ p∈S ∧ a=p.1 := by
  simp only [clockFiber,Finset.mem_filter]

private theorem count_clock (S : Finset (K×K)) (a : K) :
    (S.val.map Prod.fst).count a=(clockFiber S a).card := by
  simpa only [clockFiber,Finset.card_def,Finset.filter_val] using
    (Multiset.count_map Prod.fst S.val a)

private theorem fst_match {S : Finset (K×K)} {a : K} {p q : K×K}
    (hp : p∈clockFiber S a) (hq : q∈clockFiber S a) : p.1=q.1 :=
  (mem_clockFiber.mp hp).2.symm.trans (mem_clockFiber.mp hq).2

private theorem snd_ne {S : Finset (K×K)} {a : K} {p q : K×K}
    (hp : p∈clockFiber S a) (hq : q∈clockFiber S a) (ne : p≠q) : p.2≠q.2 :=
  fun same => ne (Prod.ext (fst_match hp hq) same)

/-- A genuine quadratic fibre contains at most two distinct amplitudes. -/
theorem clockFiber_card_le_two (S : Finset (K×K))
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1) (a : K) :
    (clockFiber S a).card≤2 := by
  by_cases le : (clockFiber S a).card≤1
  · omega
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (by omega : 1<(clockFiber S a).card)
  have write (v : K×K) (hv : v∈clockFiber S a) : v.2^2=R.eval a*v.2+P.eval a := by
    obtain ⟨h,e⟩ := mem_clockFiber.mp hv
    simpa only [←e] using square v h
  have wp := write p hp
  have wq := write q hq
  have diff : (p.2-q.2)*(p.2+q.2-R.eval a)=0 := by
    linear_combination wp - wq
  have sum : p.2+q.2=R.eval a :=
    sub_eq_zero.mp ((mul_eq_zero.mp diff).resolve_left (sub_ne_zero.mpr (snd_ne hp hq ne)))
  have cover : clockFiber S a⊆{p,q} := by
    intro v hv
    have wv := write v hv
    have fact : (v.2-p.2)*(v.2-q.2)=0 := by
      rw [←sum] at wv wp
      linear_combination wv - wp
    rcases mul_eq_zero.mp fact with e|e
    · have eq : v=p := Prod.ext (fst_match hv hp) (sub_eq_zero.mp e)
      exact Finset.mem_insert.mpr (Or.inl eq)
    · have eq : v=q := Prod.ext (fst_match hv hq) (sub_eq_zero.mp e)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr eq))
  exact (Finset.card_le_card cover).trans Finset.card_le_two

private theorem mesh_at {S : Finset (K×K)} {a : K} {p : K×K}
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2) (hp : p∈clockFiber S a) :
    G.eval a=Q.eval a*p.2 := by
  obtain ⟨h,e⟩ := mem_clockFiber.mp hp
  simpa only [←e] using mesh p h

private theorem mesh_zero_of_two {S : Finset (K×K)} {a : K} {p q : K×K}
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (hp : p∈clockFiber S a) (hq : q∈clockFiber S a) (ne : p≠q) :
    G.eval a=0 ∧ Q.eval a=0 := by
  have e₁ := mesh_at mesh hp
  have e₂ := mesh_at mesh hq
  have eq : (p.2-q.2)*Q.eval a=0 := by
    linear_combination e₂ - e₁
  have q0 := (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr (snd_ne hp hq ne))
  exact ⟨by rw [e₁,q0,zero_mul],q0⟩

private theorem vanish_at {S : Finset (K×K)} {a : K} {p : K×K}
    (vanish : ∀ p∈S, H.eval p.1+J.eval p.1*p.2=0) (hp : p∈clockFiber S a) :
    H.eval a+J.eval a*p.2=0 := by
  obtain ⟨h,e⟩ := mem_clockFiber.mp hp
  simpa only [←e] using vanish p h

private theorem test_zero_of_two {S : Finset (K×K)} {a : K} {p q : K×K}
    (vanish : ∀ p∈S, H.eval p.1+J.eval p.1*p.2=0)
    (hp : p∈clockFiber S a) (hq : q∈clockFiber S a) (ne : p≠q) :
    H.eval a=0 ∧ J.eval a=0 := by
  have e₁ := vanish_at vanish hp
  have e₂ := vanish_at vanish hq
  have eq : J.eval a*(p.2-q.2)=0 := by
    linear_combination e₁ - e₂
  have j0 := (mul_eq_zero.mp eq).resolve_right (sub_ne_zero.mpr (snd_ne hp hq ne))
  exact ⟨by simpa only [j0,zero_mul,add_zero] using e₁,j0⟩

private theorem eliminant_zero {a z : K}
    (mesh : G.eval a=Q.eval a*z) (square : z^2=R.eval a*z+P.eval a) :
    (eliminant G Q R P).eval a=0 := by
  simp only [eliminant,eval_sub,eval_mul,eval_pow,mesh]
  linear_combination (Q.eval a)^2 * square

private theorem eliminant_factor {a : K} {g q : K[X]}
    (hg : G=(X-C a)*g) (hq : Q=(X-C a)*q) :
    eliminant G Q R P=(X-C a)^2*eliminant g q R P := by
  simp only [eliminant,hg,hq]
  ring

private theorem square_dvd_eliminant {a : K}
    (g0 : G.eval a=0) (q0 : Q.eval a=0) :
    (X-C a)^2∣eliminant G Q R P := by
  obtain ⟨g,hg⟩ := (dvd_iff_isRoot (a:=a)).mpr g0
  obtain ⟨q,hq⟩ := (dvd_iff_isRoot (a:=a)).mpr q0
  exact ⟨eliminant g q R P,eliminant_factor hg hq⟩

private theorem eliminant_factors (S : Finset (K×K))
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1) (a : K) :
    (X-C a)^(clockFiber S a).card∣eliminant G Q R P := by
  have cap := clockFiber_card_le_two S square a
  by_cases e₀ : (clockFiber S a).card=0
  · rw [e₀,pow_zero]
    exact one_dvd _
  by_cases e₁ : (clockFiber S a).card=1
  · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(clockFiber S a).card)
    obtain ⟨h,e⟩ := mem_clockFiber.mp hp
    have wp : p.2^2=R.eval a*p.2+P.eval a := by simpa only [←e] using square p h
    rw [e₁,pow_one]
    exact dvd_iff_isRoot.mpr (eliminant_zero (mesh_at mesh hp) wp)
  have e₂ : (clockFiber S a).card=2 := by omega
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (by omega : 1<(clockFiber S a).card)
  obtain ⟨g0,q0⟩ := mesh_zero_of_two mesh hp hq ne
  rw [e₂]
  exact square_dvd_eliminant g0 q0

private theorem test_factors (S : Finset (K×K))
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (vanish : ∀ p∈S, H.eval p.1+J.eval p.1*p.2=0)
    (cap : ∀ a,(clockFiber S a).card≤2) (a : K) :
    (X-C a)^(clockFiber S a).card∣H*Q+J*G := by
  have capA := cap a
  by_cases e₀ : (clockFiber S a).card=0
  · rw [e₀,pow_zero]
    exact one_dvd _
  by_cases e₁ : (clockFiber S a).card=1
  · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(clockFiber S a).card)
    have e := mesh_at mesh hp
    have w := vanish_at vanish hp
    rw [e₁,pow_one]
    apply dvd_iff_isRoot.mpr
    change (H*Q+J*G).eval a=0
    calc
      _ = Q.eval a*(H.eval a+J.eval a*p.2) := by
        simp only [eval_add,eval_mul,e]
        ring
      _ = 0 := by rw [w,mul_zero]
  have e₂ : (clockFiber S a).card=2 := by omega
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (by omega : 1<(clockFiber S a).card)
  obtain ⟨g0,q0⟩ := mesh_zero_of_two mesh hp hq ne
  obtain ⟨h0,j0⟩ := test_zero_of_two vanish hp hq ne
  obtain ⟨g,hg⟩ := (dvd_iff_isRoot (a:=a)).mpr g0
  obtain ⟨q',hq'⟩ := (dvd_iff_isRoot (a:=a)).mpr q0
  obtain ⟨h,hh⟩ := (dvd_iff_isRoot (a:=a)).mpr h0
  obtain ⟨j,hj⟩ := (dvd_iff_isRoot (a:=a)).mpr j0
  rw [e₂]
  refine ⟨h*q'+j*g,?_⟩
  rw [hg,hq',hh,hj]
  ring

private theorem clocks_le_roots (S : Finset (K×K)) {F : K[X]} (fn : F≠0)
    (paid : ∀ a,(X-C a)^(clockFiber S a).card∣F) :
    S.val.map Prod.fst≤F.roots := by
  apply Multiset.le_iff_count.mpr
  intro a
  rw [count_clock,count_roots]
  exact (le_rootMultiplicity_iff fn).mpr (paid a)

/-- Literal product with one linear factor per pair. Mathlib's
`prod_X_sub_C_dvd_iff_le_roots` is the factorization theorem for
pairwise-coprime distinct linear factors, grouping repeated clocks. -/
theorem counted_clock_product_dvd (S : Finset (K×K)) {F : K[X]} (fn : F≠0)
    (paid : ∀ a,(X-C a)^(clockFiber S a).card∣F) :
    (S.val.map (fun z => X-C z.1)).prod∣F := by
  have h := (Multiset.prod_X_sub_C_dvd_iff_le_roots fn (S.val.map Prod.fst)).mpr
    (clocks_le_roots S fn paid)
  simpa only [Multiset.map_map,Function.comp_def] using h

/-- Exact multiset of eliminant roots when the pair count spends the
entire degree. This rules out a hidden extra copy of any clock. -/
theorem eliminant_roots_eq (S : Finset (K×K))
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (fn : eliminant G Q R P≠0) (sat : (eliminant G Q R P).natDegree=S.card) :
    (eliminant G Q R P).roots=S.val.map Prod.fst := by
  have paid := eliminant_factors S mesh square
  have prod := counted_clock_product_dvd S fn paid
  have cover : S.val.map Prod.fst≤(eliminant G Q R P).roots := by
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots fn (S.val.map Prod.fst)).mp
    simpa only [Multiset.map_map,Function.comp_def] using prod
  apply (Multiset.eq_of_le_of_card_le cover ?_).symm
  rw [Multiset.card_map,Finset.card_val,←sat]
  exact card_roots' _

private theorem eq_zero_of_counted_clocks (S : Finset (K×K)) {T : K[X]}
    (cap : T.natDegree<S.card) (paid : ∀ a,(X-C a)^(clockFiber S a).card∣T) : T=0 := by
  by_contra tn
  have prod := counted_clock_product_dvd S tn paid
  have cover : S.val.map Prod.fst≤T.roots := by
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots tn (S.val.map Prod.fst)).mp
    simpa only [Multiset.map_map,Function.comp_def] using prod
  have deg := (Multiset.card_le_card cover).trans (card_roots' T)
  rw [Multiset.card_map,Finset.card_val] at deg
  omega

/-- One erased pair removes exactly one root credit, not an entire
clock. At the surviving double fibres both test coefficients vanish. -/
theorem transport_test_eq_zero {S : Finset (K×K)}
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (small : (H*Q+J*G).natDegree+1<S.card)
    {target : K×K} (inside : target∈S)
    (vanish : ∀ p∈S, p≠target → H.eval p.1+J.eval p.1*p.2=0) :
    H*Q+J*G=0 := by
  let S' := S.erase target
  have size : S'.card+1=S.card := Finset.card_erase_add_one inside
  have sub : S'⊆S := Finset.erase_subset target S
  have mesh' (p : K×K) (hp : p∈S') : G.eval p.1=Q.eval p.1*p.2 := mesh p (sub hp)
  have square' (p : K×K) (hp : p∈S') : p.2^2=R.eval p.1*p.2+P.eval p.1 := square p (sub hp)
  have vanish' (p : K×K) (hp : p∈S') : H.eval p.1+J.eval p.1*p.2=0 :=
    vanish p (sub hp) (Finset.mem_erase.mp hp).1
  exact eq_zero_of_counted_clocks S' (T:=H*Q+J*G) (by omega)
    (test_factors S' mesh' vanish' (clockFiber_card_le_two S' square'))

private theorem transport_value_eq_zero {a z : K} (mesh : G.eval a=Q.eval a*z)
    (qn : Q.eval a≠0) (tz : H*Q+J*G=0) :
    H.eval a+J.eval a*z=0 := by
  have e : H.eval a*Q.eval a+J.eval a*(Q.eval a*z)=0 := by
    simpa only [eval_add,eval_mul,eval_zero,mesh] using congrArg (eval a) tz
  have prod : Q.eval a*(H.eval a+J.eval a*z)=0 := by linear_combination e
  exact (mul_eq_zero.mp prod).resolve_left qn

private theorem degree_nine_test_small {S : Finset (K×K)} (size : 14≤S.card)
    (gd : G.natDegree≤7) (qd : Q.natDegree≤3) (hd : H.natDegree≤6) (jd : J.natDegree≤5) :
    (H*Q+J*G).natDegree+1<S.card := by
  have b₁ : (H*Q).natDegree≤12 := by have := natDegree_mul_le (p:=H) (q:=Q); omega
  have b₂ : (J*G).natDegree≤12 := by have := natDegree_mul_le (p:=J) (q:=G); omega
  have dg := (natDegree_add_le (H*Q) (J*G)).trans (max_le b₁ b₂)
  omega

/-- Only this shorter branch is needed at the supported reflected-zero
stage: the paid G(1)≠0 implies Q(1)≠0. Saturation of the eliminant is
unnecessary when the selected pair has nonzero mesh value. -/
theorem no_grade_nine_selector_of_mesh_nonzero {S : Finset (K×K)}
    (size : 14≤S.card)
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (gd : G.natDegree≤7) (qd : Q.natDegree≤3) (hd : H.natDegree≤6) (jd : J.natDegree≤5)
    {target : K×K} (inside : target∈S) (live : G.eval target.1≠0) :
    ¬ ∀ p∈S, H.eval p.1+J.eval p.1*p.2=(if p=target then 1 else 0) := by
  intro indicator
  have mz := mesh target inside
  have qn : Q.eval target.1≠0 := by
    intro e
    exact live (by rw [mz,e,zero_mul])
  have small := degree_nine_test_small size gd qd hd jd
  have van (p : K×K) (hp : p∈S) (ne : p≠target) :
      H.eval p.1+J.eval p.1*p.2=0 := by simpa only [if_neg ne] using indicator p hp
  have tz := transport_test_eq_zero mesh square small inside van
  have zero := transport_value_eq_zero mz qn tz
  have one := indicator target inside
  rw [if_pos rfl,zero] at one
  exact zero_ne_one one

/-- Under exact complete-intersection saturation, a function
H(a)+J(a)z whose resultant test is small enough cannot be supported
at a single pair. Both singleton and two-amplitude clock fibres,
and even the case Q=0, are included. -/
theorem no_singleton_of_saturation {S : Finset (K×K)}
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (sat : (eliminant G Q R P).natDegree=S.card)
    (small : (H*Q+J*G).natDegree+1<S.card)
    {target : K×K} (inside : target∈S)
    (vanish : ∀ p∈S, p≠target → H.eval p.1+J.eval p.1*p.2=0) :
    H.eval target.1+J.eval target.1*target.2=0 := by
  let F := eliminant G Q R P
  let T := H*Q+J*G
  have tz : T=0 := transport_test_eq_zero mesh square small inside vanish
  let a := target.1
  have targetMesh : G.eval a=Q.eval a*target.2 := mesh target inside
  by_cases q0 : Q.eval a=0
  · have g0 : G.eval a=0 := by rw [targetMesh,q0,zero_mul]
    obtain ⟨g,hg⟩ := (dvd_iff_isRoot (a:=a)).mpr g0
    obtain ⟨q,hq⟩ := (dvd_iff_isRoot (a:=a)).mpr q0
    have fact : F=(X-C a)^2*eliminant g q R P := eliminant_factor hg hq
    have fn : F≠0 := by
      intro z
      change F.natDegree=S.card at sat
      rw [z,natDegree_zero] at sat
      omega
    have roots : F.roots=S.val.map Prod.fst := eliminant_roots_eq S mesh square fn sat
    have mult : rootMultiplicity a F=(clockFiber S a).card := by
      rw [←count_roots,roots,count_clock]
    have two : 2≤rootMultiplicity a F :=
      (le_rootMultiplicity_iff fn).mpr ⟨eliminant g q R P,fact⟩
    have cap := clockFiber_card_le_two S square a
    obtain ⟨v,hv,ne⟩ := Finset.exists_mem_ne (by omega : 1<(clockFiber S a).card) target
    obtain ⟨vS,va⟩ := mem_clockFiber.mp hv
    have other : H.eval a+J.eval a*v.2=0 := by simpa only [←va] using vanish v vS ne
    have vSq : v.2^2=R.eval a*v.2+P.eval a := by simpa only [←va] using square v vS
    have nonzero : (eliminant g q R P).eval a≠0 := by
      intro z
      obtain ⟨u,hu⟩ := (dvd_iff_isRoot (a:=a)).mpr z
      have threeDvd : (X-C a)^3∣F := by
        refine ⟨u,?_⟩
        rw [fact,hu]
        ring
      have three : 3≤rootMultiplicity a F := (le_rootMultiplicity_iff fn).mpr threeDvd
      omega
    have cof : T=(X-C a)*(H*q+J*g) := by dsimp only [T]; rw [hg,hq]; ring
    have z : H*q+J*g=0 :=
      (mul_eq_zero.mp (cof.symm.trans tz)).resolve_left (X_sub_C_ne_zero a)
    have e : H.eval a*q.eval a+J.eval a*g.eval a=0 := by
      simpa only [eval_add,eval_mul,eval_zero] using congrArg (eval a) z
    have det : g.eval a-q.eval a*v.2≠0 := by
      intro dz
      exact nonzero (eliminant_zero (sub_eq_zero.mp dz) vSq)
    have prod : J.eval a*(g.eval a-q.eval a*v.2)=0 := by
      linear_combination e - q.eval a * other
    have j0 := (mul_eq_zero.mp prod).resolve_right det
    have h0 : H.eval a=0 := by simpa only [j0,zero_mul,add_zero] using other
    change H.eval a+J.eval a*target.2=0
    rw [h0,j0,zero_mul,add_zero]
  · exact transport_value_eq_zero targetMesh q0 tz

/-- In the earning branch the un-cancelled degree-seven coefficient of
G−RQ multiplies the leading coefficient of G, so the eliminant degree is 14. -/
theorem eliminant_degree_fourteen (gd : G.natDegree=7) (qd : Q.natDegree≤3)
    (rd : R.natDegree≤4) (pd : P.natDegree≤6) (top : (G-R*Q).coeff 7≠0) :
    (eliminant G Q R P).natDegree=14 := by
  have rq : (R*Q).natDegree≤7 := by
    have := natDegree_mul_le (p:=R) (q:=Q)
    omega
  have delta : (G-R*Q).natDegree=7 := le_antisymm
    ((natDegree_sub_le G (R*Q)).trans (max_le gd.le rq)) (le_natDegree_of_ne_zero top)
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have dn : G-R*Q≠0 := fun z => top (by rw [z,coeff_zero])
  have first : ((G-R*Q)*G).natDegree=14 := by rw [natDegree_mul dn gn,delta,gd]
  have tail : (P*Q^2).natDegree≤12 := by
    have h := natDegree_mul_le (p:=P) (q:=Q^2)
    have p2 : (Q^2).natDegree≤2*Q.natDegree := natDegree_pow_le
    omega
  have under : (P*Q^2).natDegree<((G-R*Q)*G).natDegree := by omega
  rw [eliminant,natDegree_sub_eq_left_of_natDegree_lt under,first]

/-- The ordinary grade-nine polynomial band cannot be the indicator
of a single noncore class among 14 distinct original pairs. -/
theorem no_grade_nine_selector {S : Finset (K×K)}
    (size : S.card=14)
    (mesh : ∀ p∈S, G.eval p.1=Q.eval p.1*p.2)
    (square : ∀ p∈S, p.2^2=R.eval p.1*p.2+P.eval p.1)
    (gd : G.natDegree=7) (qd : Q.natDegree≤3) (rd : R.natDegree≤4) (pd : P.natDegree≤6)
    (top : (G-R*Q).coeff 7≠0) (hd : H.natDegree≤6) (jd : J.natDegree≤5)
    {target : K×K} (inside : target∈S) :
    ¬ ∀ p∈S, H.eval p.1+J.eval p.1*p.2=(if p=target then 1 else 0) := by
  intro indicator
  have small := degree_nine_test_small size.ge gd.le qd hd jd
  have sat := (eliminant_degree_fourteen gd qd rd pd top).trans size.symm
  have van (p : K×K) (hp : p∈S) (ne : p≠target) :
      H.eval p.1+J.eval p.1*p.2=0 := by simpa only [if_neg ne] using indicator p hp
  have zero := no_singleton_of_saturation mesh square sat small inside van
  have one := indicator target inside
  rw [if_pos rfl,zero] at one
  exact zero_ne_one one

end
end RKResearch.Certified.Graded.NativeQuadraticClassSelector

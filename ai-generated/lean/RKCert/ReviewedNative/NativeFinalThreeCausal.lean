module

public import RKCert.ReviewedNative.NativeFinalThreeScalar
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Filter
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Final three physical classes in a strict finite transpose chart

The matrix on classes is not required to be an RK tableau. Only its lower
triangular chronology, three folded rows, and two transpose profiles are used.
The wider interface pays possible active zero-λ coordinates by five moments. -/

namespace RKResearch.Certified.Graded.NativeFinalThree

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def reverseSum (B : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (i : Fin n) : K :=
  ∑ j, B j i * u j

def foldedRow (B : Matrix (Fin n) (Fin n) K) (b y : Fin n → K) (k : ℕ) (i : Fin n) : K :=
  ((k + 1 : ℕ) : K) * reverseSum B (fun j => b j * y j ^ k) i - b i * y i ^ (k + 1)

noncomputable def unionSupport (b y l : Fin n → K) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => l i ≠ 0 ∨ b i * y i ≠ 0)

@[simp] theorem mem_unionSupport {b y l : Fin n → K} {i : Fin n} :
    i ∈ unionSupport b y l ↔ l i ≠ 0 ∨ b i * y i ≠ 0 := by
  classical
  simp [unionSupport]

structure CausalRows (B : Matrix (Fin n) (Fin n) K) (b y l : Fin n → K) : Prop where
  first : ∃ a : K, a ≠ 0 ∧ ∀ i, foldedRow B b y 1 i = l i * a
  second : ∃ a : K, ∀ i, foldedRow B b y 2 i = l i * a
  third : ∃ a d : K, ∀ i, foldedRow B b y 3 i = l i * (a + d * y i)
  affine : ∃ a d : K, ∀ i, reverseSum B l i = l i * (a + d * y i)
  /-- A quadratic-in-y output suffices. Only equality on equal clocks is used. -/
  shiftClock : ∀ Y : K, ∃ g : K → K,
    ∀ i, reverseSum B (fun j => (y j - Y) * l j) i = l i * g (y i)

def DistinguishedRatios (b y l : Fin n → K) : Prop :=
  ∀ i j, i ≠ j → l i ≠ 0 → l j ≠ 0 → y i = y j → y i ≠ 0 →
    b i * y i / l i ≠ 0 → b i * y i / l i ≠ b j * y j / l j

/-- Two arbitrarily signed nodes, including a padded zero-weight node,
cannot integrate the first five positive monomials. -/
theorem two_node_moments_impossible (u v a b : K)
    (h1 : a*u + b*v = 1/2)
    (h2 : a*u^2 + b*v^2 = 1/3)
    (h3 : a*u^3 + b*v^3 = 1/4)
    (h4 : a*u^4 + b*v^4 = 1/5)
    (h5 : a*u^5 + b*v^5 = 1/6) : False := by
  have t1 : (1/4 : K) - (u+v)/3 + u*v/2 = 0 := by
    linear_combination -h3 + (u+v)*h2 - (u*v)*h1
  have t2 : (1/5 : K) - (u+v)/4 + u*v/3 = 0 := by
    linear_combination -h4 + (u+v)*h3 - (u*v)*h2
  have t3 : (1/6 : K) - (u+v)/5 + u*v/4 = 0 := by
    linear_combination -h5 + (u+v)*h4 - (u*v)*h3
  have z : (1/60 : K) = 0 := by linear_combination 3*t1 - 12*t2 + 10*t3
  exact (by norm_num : (1/60 : K) ≠ 0) z

private structure LastThree (S : Finset (Fin n)) where
  top : Fin n
  mid : Fin n
  low : Fin n
  top_mem : top ∈ S
  mid_mem : mid ∈ S
  low_mem : low ∈ S
  mid_lt_top : mid < top
  low_lt_mid : low < mid
  later : ∀ j ∈ S, low < j → j = top ∨ j = mid

private theorem lastThree_of_card {S : Finset (Fin n)} (hc : 3 ≤ S.card) :
    Nonempty (LastThree S) := by
  classical
  have s0 : S.Nonempty := Finset.card_pos.mp (by omega)
  let i0 := S.max' s0
  have hi0 : i0 ∈ S := S.max'_mem s0
  let S1 := S.erase i0
  have c1 : S1.card = S.card - 1 := Finset.card_erase_of_mem hi0
  have s1 : S1.Nonempty := Finset.card_pos.mp (by omega)
  let i1 := S1.max' s1
  have hi1 : i1 ∈ S1 := S1.max'_mem s1
  let S2 := S1.erase i1
  have c2 : S2.card = S1.card - 1 := Finset.card_erase_of_mem hi1
  have s2 : S2.Nonempty := Finset.card_pos.mp (by omega)
  let i2 := S2.max' s2
  have hi2 : i2 ∈ S2 := S2.max'_mem s2
  have e1 := Finset.mem_erase.mp hi1
  have e2 := Finset.mem_erase.mp hi2
  refine ⟨⟨i0, i1, i2, hi0, e1.2, Finset.mem_of_mem_erase e2.2,
    lt_of_le_of_ne (S.le_max' _ e1.2) e1.1,
    lt_of_le_of_ne (S1.le_max' _ e2.2) e2.1, ?_⟩⟩
  intro j hj hj2
  by_cases e0 : j = i0
  · exact Or.inl e0
  by_cases e : j = i1
  · exact Or.inr e
  have j2 : j ∈ S2 := Finset.mem_erase.mpr ⟨e, Finset.mem_erase.mpr ⟨e0, hj⟩⟩
  exact (not_le_of_gt hj2 (S2.le_max' _ j2)).elim

private theorem LastThree.reverse_eq_two {S : Finset (Fin n)} (t : LastThree S)
    {B : Matrix (Fin n) (Fin n) K} (strict : ∀ i j, i ≤ j → B i j = 0)
    {u : Fin n → K} (out : ∀ j, j ∉ S → u j = 0) {i : Fin n} (hi : t.low ≤ i) :
    reverseSum B u i = B t.top i * u t.top + B t.mid i * u t.mid := by
  classical
  let U : Finset (Fin n) := {t.top, t.mid}
  have e : reverseSum B u i = ∑ j ∈ U, B j i * u j := by
    unfold reverseSum
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro j _ hj
    by_cases le : j ≤ i
    · rw [strict j i le, zero_mul]
    · have outS : j ∉ S := by
        intro hs
        rcases t.later j hs (hi.trans_lt (lt_of_not_ge le)) with h | h
        · exact hj (by simp [U,h])
        · exact hj (by simp [U,h])
      rw [out j outS, mul_zero]
  rw [e]
  dsimp only [U]
  rw [Finset.sum_insert (by simp [ne_of_gt t.mid_lt_top]), Finset.sum_singleton]

private theorem zero_off_union_l {b y l : Fin n → K} {j : Fin n}
    (h : j ∉ unionSupport b y l) : l j = 0 := by
  classical
  by_contra z
  exact h ((mem_unionSupport (b := b) (y := y) (l := l)).mpr (Or.inl z))

private theorem zero_off_union_weight {b y l : Fin n → K} {j : Fin n}
    (h : j ∉ unionSupport b y l) {k : ℕ} (hk : 0 < k) : b j * y j ^ k = 0 := by
  classical
  have z : b j * y j = 0 := by
    by_contra nz
    exact h ((mem_unionSupport (b := b) (y := y) (l := l)).mpr (Or.inr nz))
  rcases mul_eq_zero.mp z with bz | yz
  · rw [bz, zero_mul]
  · rw [yz, zero_pow (Nat.ne_of_gt hk), mul_zero]

set_option maxHeartbeats 900000 in
private theorem quiet_tail_impossible {B : Matrix (Fin n) (Fin n) K} {b y l : Fin n → K}
    (strict : ∀ i j, i ≤ j → B i j = 0) (t : LastThree (unionSupport b y l))
    {i : Fin n} (hi : t.low ≤ i) (live : b i * y i ≠ 0)
    (quiet : ∀ k : ℕ, 1 ≤ k → k ≤ 5 → foldedRow B b y k i = 0) : False := by
  have bi := (mul_ne_zero_iff.mp live).1
  have yi := (mul_ne_zero_iff.mp live).2
  let w (j : Fin n) : K := B j i * b j / (b i * y i)
  let x (j : Fin n) : K := y j / y i
  have moments (k : ℕ) (lo : 1 ≤ k) (up : k ≤ 5) :
      w t.top * x t.top ^ k + w t.mid * x t.mid ^ k = 1 / ((k+1:ℕ):K) := by
    let D := b i * y i ^ (k+1)
    have d0 : D ≠ 0 := mul_ne_zero bi (pow_ne_zero _ yi)
    have k0 : ((k+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have term (j : Fin n) : (w j * x j ^ k) * D = B j i * (b j * y j ^ k) := by
      dsimp only [w,x,D]
      rw [div_pow, pow_succ (y i) k]
      field_simp [live, yi, bi, pow_ne_zero k yi] <;> ring
    have q := quiet k lo up
    unfold foldedRow at q
    rw [t.reverse_eq_two strict (fun j hj => zero_off_union_weight hj (by omega : 0 < k)) hi] at q
    have sum :
        (w t.top * x t.top ^ k + w t.mid * x t.mid ^ k) * D =
          B t.top i * (b t.top * y t.top ^ k) + B t.mid i * (b t.mid * y t.mid ^ k) := by
      rw [add_mul, term t.top, term t.mid]
    apply (eq_div_iff k0).2
    apply mul_right_cancel₀ d0
    change (w t.top * x t.top ^ k + w t.mid * x t.mid ^ k) * ((k+1:ℕ):K) * D = 1 * D
    change ((k+1:ℕ):K) *
      (B t.top i * (b t.top * y t.top ^ k) + B t.mid i * (b t.mid * y t.mid ^ k)) - D = 0 at q
    linear_combination q + (((k+1:ℕ):K))*sum
  apply two_node_moments_impossible (x t.top) (x t.mid) (w t.top) (w t.mid)
  · simpa only [pow_one, Nat.reduceAdd, Nat.cast_ofNat] using moments 1 (by decide) (by decide)
  · simpa only [Nat.reduceAdd, Nat.cast_ofNat] using moments 2 (by decide) (by decide)
  · simpa only [Nat.reduceAdd, Nat.cast_ofNat] using moments 3 (by decide) (by decide)
  · simpa only [Nat.reduceAdd, Nat.cast_ofNat] using moments 4 (by decide) (by decide)
  · simpa only [Nat.reduceAdd, Nat.cast_ofNat] using moments 5 (by decide) (by decide)

private theorem normalized_tail_impossible (s h v xi p q a g : K)
    (h21 : 2*a*(s-1)-s*h = -1)
    (h22 : 3*a*(s-1)-s^2*h = -1)
    (h23 : 4*a*(s-1)-s^3*h = -1+g*(s-1))
    (h31 : p+q = a*(v-1))
    (h32 : 2*(p+q*h)-v*xi = -1)
    (h33 : 3*(p+q*(s*h))-v^2*xi = -1)
    (h34 : 4*(p+q*(s^2*h))-v^3*xi = -1+g*(v-1))
    (repeatQ : v=1 ∨ v=s → q=0)
    (repeat21 : s=1 → h≠1) (repeat31 : v=1 → xi≠1)
    (repeat32 : v=s → h≠0 → xi≠h) : False := by
  have s0 : s ≠ 0 := by
    intro hs
    rw [hs] at h21 h22
    have no : (1:K)=0 := by linear_combination 3*h21-2*h22
    exact one_ne_zero no
  have s1 : s ≠ 1 := by
    intro hs
    rw [hs] at h21
    exact repeat21 hs (by linear_combination -h21)
  have sh : s*h = a := by
    have m : (s-1)*(a-s*h)=0 := by linear_combination h22-h21
    exact (sub_eq_zero.mp ((mul_eq_zero.mp m).resolve_left (sub_ne_zero.mpr s1))).symm
  let D : K := 3-2*s
  have da : D*a=1 := by
    dsimp only [D]
    linear_combination -h21-sh
  have a0 : a ≠ 0 := by
    intro az
    exact (zero_ne_one : (0 : K) ≠ 1) (by simpa [az] using da)
  have hn : h ≠ 0 := by
    intro hz
    exact a0 (by simpa [hz] using sh.symm)
  have gn : g = -a*(s-1) := by
    have m : (s-1)*(g+a*(s-1))=0 := by
      dsimp only [D] at da
      linear_combination -h23-s^2*sh-da
    simpa only [neg_mul] using
      (eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp m).resolve_left (sub_ne_zero.mpr s1)))
  have dg : D*g = -(s-1) := by linear_combination D*gn-(s-1)*da
  let Q : K := q/s
  have qn : s*Q=q := by rw [mul_comm]; exact div_mul_cancel₀ q s0
  have hh : D*h=1/s := (eq_div_iff s0).mpr (by linear_combination D*sh+da)
  have dqh : D*(q*h)=Q := by
    calc
      D*(q*h) = q*(D*h) := by ring
      _ = Q := by change q*(D*h)=q/s; rw [hh, mul_one_div]
  have z0 : D*p+D*s*Q=v-1 := by linear_combination D*h31+D*qn+(v-1)*da
  have z1 : 2*(D*p+Q)-v*(D*xi) = -D := by linear_combination D*h32-2*dqh
  have z2 : 3*(D*p+s*Q)-v^2*(D*xi) = -D := by linear_combination D*h33-3*s*dqh
  have z3 : 4*(D*p+s^2*Q)-v^3*(D*xi) = -D-(s-1)*(v-1) := by
    linear_combination D*h34-4*s^2*dqh+(v-1)*dg
  have pair := clock_eq_first_or_second s v (D*p) Q (D*xi) z0 z1 z2 z3
  have q0 := repeatQ pair
  rcases pair with hv | hv
  · have p0 : p=0 := by simpa [q0,hv] using h31
    rw [q0,hv,p0] at h32
    exact repeat31 hv (by linear_combination -h32)
  · rw [q0,hv] at h31 h32
    have m : s*(xi-h)=0 := by linear_combination h21-h32+2*h31
    exact repeat32 hv hn (sub_eq_zero.mp ((mul_eq_zero.mp m).resolve_left s0))

set_option maxHeartbeats 1600000 in
private theorem causal_tail {B : Matrix (Fin n) (Fin n) K} {b y l : Fin n → K}
    (strict : ∀ i j, i ≤ j → B i j = 0) (rows : CausalRows B b y l)
    (ratios : DistinguishedRatios b y l) (t : LastThree (unionSupport b y l))
    (ll : ∀ i, t.low ≤ i → i ∈ unionSupport b y l → l i ≠ 0) : False := by
  classical
  let i0 := t.top
  let i1 := t.mid
  let i2 := t.low
  have h10 : i1 < i0 := t.mid_lt_top
  have h21 : i2 < i1 := t.low_lt_mid
  have h20 : i2 < i0 := lt_trans h21 h10
  have l0 := ll i0 h20.le t.top_mem
  have l1 := ll i1 h21.le t.mid_mem
  have l2 := ll i2 le_rfl t.low_mem
  obtain ⟨r1, r10, row1⟩ := rows.first
  obtain ⟨r2, row2⟩ := rows.second
  obtain ⟨r30, r31, row3⟩ := rows.third
  obtain ⟨a0, a, affine⟩ := rows.affine
  have pair {u : Fin n → K} (out : ∀ j, j ∉ unionSupport b y l → u j = 0)
      {i : Fin n} (hi : i2 ≤ i) :
      reverseSum B u i = B i0 i*u i0 + B i1 i*u i1 :=
    t.reverse_eq_two strict out hi
  have wt (k : ℕ) (hk : 0 < k) {i : Fin n} (hi : i2 ≤ i) :
      reverseSum B (fun j => b j*y j^k) i =
        B i0 i*(b i0*y i0^k) + B i1 i*(b i1*y i1^k) :=
    pair (fun _ hj => zero_off_union_weight hj hk) hi
  have b00 := strict i0 i0 le_rfl
  have b10 := strict i1 i0 h10.le
  have b11 := strict i1 i1 le_rfl
  have alive : b i0 * y i0 ^ 2 ≠ 0 := by
    intro bad
    have h := row1 i0
    unfold foldedRow at h
    rw [wt 1 (by decide) h20.le, b00, b10, bad] at h
    exact (mul_ne_zero l0 r10) (by simpa using h.symm)
  let Y := y i0
  have Y0 : Y ≠ 0 := by
    intro z
    exact alive (by change y i0=0 at z; rw [z]; simp)
  have bm0 : b i0 ≠ 0 := by
    intro z
    exact alive (by rw [z, zero_mul])
  let F := (b i0 * y i0) / l i0
  have F0 : F ≠ 0 := div_ne_zero (mul_ne_zero bm0 Y0) l0
  let x (i : Fin n) := y i / Y
  let f (i : Fin n) := (b i * y i / l i) / F
  let tau (j i : Fin n) := (B j i * l j) / (Y*l i)
  have xY (i : Fin n) : x i * Y = y i := div_mul_cancel₀ _ Y0
  have fF (i : Fin n) : f i * F = b i * y i / l i := div_mul_cancel₀ _ F0
  have x0 : x i0 = 1 := div_self Y0
  have f0 : f i0 = 1 := div_self F0
  have t00 : tau i0 i0=0 := by simp [tau,b00]
  have t10 : tau i1 i0=0 := by simp [tau,b10]
  have t11 : tau i1 i1=0 := by simp [tau,b11]
  have aff0 : a0 + a*Y = 0 := by
    have h := affine i0
    rw [pair (fun _ hj => zero_off_union_l hj) h20.le, b00, b10] at h
    have z : l i0 * (a0 + a*Y) = 0 := by simpa using h.symm
    exact (mul_eq_zero.mp z).resolve_left l0
  have sumTau (i : Fin n) (hi : i2 ≤ i) (li : l i ≠ 0) :
      tau i0 i + tau i1 i = a*(x i-1) := by
    have h := affine i
    rw [pair (fun _ hj => zero_off_union_l hj) hi] at h
    have den : Y*l i ≠ 0 := mul_ne_zero Y0 li
    apply mul_right_cancel₀ den
    simp only [add_mul,tau,div_mul_cancel₀ _ den]
    linear_combination h-(a*l i)*xY i+l i*aff0
  have normRow (k : ℕ) (r : K → K) (hr : ∀ i, foldedRow B b y (k+1) i = l i*r (y i))
      (i : Fin n) (hi : i2 ≤ i) (li : l i ≠ 0) :
      ((k+2:ℕ):K) * (tau i0 i*(x i0^k*f i0) + tau i1 i*(x i1^k*f i1)) -
          x i^(k+1)*f i = r (y i)/(F*Y^(k+1)) := by
    let D := l i * F * Y^(k+1)
    have den : D ≠ 0 := mul_ne_zero (mul_ne_zero li F0) (pow_ne_zero _ Y0)
    have term (j : Fin n) (lj : l j ≠ 0) :
        (tau j i*(x j^k*f j))*D = B j i*(b j*y j^(k+1)) := by
      dsimp only [tau,x,f,D]
      rw [div_pow,pow_succ Y k,pow_succ (y j) k]
      field_simp [Y0,F0,li,lj,pow_ne_zero k Y0] <;> ring
    have self : (x i^(k+1)*f i)*D = b i*y i^(k+2) := by
      dsimp only [x,f,D]
      rw [div_pow,show k+2=(k+1)+1 by omega,pow_succ (y i) (k+1)]
      field_simp [Y0,F0,li,pow_ne_zero (k+1) Y0] <;> ring
    have sum : (tau i0 i*(x i0^k*f i0)+tau i1 i*(x i1^k*f i1))*D =
        B i0 i*(b i0*y i0^(k+1)) + B i1 i*(b i1*y i1^(k+1)) := by
      rw [add_mul,term i0 l0,term i1 l1]
    have h := hr i
    unfold foldedRow at h
    rw [wt (k+1) (by omega) hi] at h
    calc
      _ = (l i*r (y i))/D := by
        apply (eq_div_iff den).2
        linear_combination h+(((k+2:ℕ):K))*sum-self
      _ = r (y i)/(F*Y^(k+1)) := by
        dsimp only [D]
        field_simp [F0,li,pow_ne_zero (k+1) Y0]
  have n1 := normRow 0 (fun _ => r1) row1
  have n2 := normRow 1 (fun _ => r2) row2
  have n3 := normRow 2 (fun z => r30+r31*z) row3
  have c1 : r1/(F*Y) = -1 := by simpa [x0,f0,t00,t10] using (n1 i0 h20.le l0).symm
  have c2 : r2/(F*Y^2) = -1 := by simpa [x0,f0,t00,t10] using (n2 i0 h20.le l0).symm
  have c3 : (r30+r31*Y)/(F*Y^3) = -1 := by
    simpa [Y,x0,f0,t00,t10] using (n3 i0 h20.le l0).symm
  let g := (r31*Y)/(F*Y^3)
  have aff3 (i : Fin n) : (r30+r31*y i)/(F*Y^3) = -1+g*(x i-1) := by
    have h : r30+r31*y i = (r30+r31*Y)+(r31*Y)*(x i-1) := by
      linear_combination -r31*xY i
    rw [h,add_div,mul_div_right_comm,c3]
  have R1 (i : Fin n) (hi : i2 ≤ i) (li : l i ≠ 0) :
      2*(tau i0 i+tau i1 i*f i1)-x i*f i = -1 := by
    simpa [x0,f0,c1] using n1 i hi li
  have R2 (i : Fin n) (hi : i2 ≤ i) (li : l i ≠ 0) :
      3*(tau i0 i+tau i1 i*(x i1*f i1))-x i^2*f i = -1 := by
    simpa [x0,f0,c2] using n2 i hi li
  have R3 (i : Fin n) (hi : i2 ≤ i) (li : l i ≠ 0) :
      4*(tau i0 i+tau i1 i*(x i1^2*f i1))-x i^3*f i = -1+g*(x i-1) := by
    simpa [x0,f0,aff3 i] using n3 i hi li
  have t01 : tau i0 i1=a*(x i1-1) := by simpa [t11] using sumTau i1 h21.le l1
  obtain ⟨G, hg⟩ := rows.shiftClock Y
  have shifted (i : Fin n) (hi : i2 ≤ i) :
      B i0 i*((y i0-Y)*l i0)+B i1 i*((y i1-Y)*l i1) = l i*G (y i) := by
    have eq := hg i
    rw [pair (fun j hj => by rw [zero_off_union_l hj,mul_zero]) hi] at eq
    exact eq
  have G0 : G (y i0) = 0 := by
    have e := shifted i0 h20.le
    rw [b00,b10] at e
    have z : l i0*G (y i0)=0 := by simpa using e.symm
    exact (mul_eq_zero.mp z).resolve_left l0
  have G1 : G (y i1) = 0 := by
    have e := shifted i1 h21.le
    change B i0 i1*((y i0-y i0)*l i0)+B i1 i1*((y i1-Y)*l i1)=_ at e
    rw [b11] at e
    have z : l i1*G (y i1)=0 := by simpa using e.symm
    exact (mul_eq_zero.mp z).resolve_left l1
  have y_same {i j : Fin n} (h : x i = x j) : y i = y j := by
    rw [←xY i, ←xY j, h]
  have repeat_tau (eq : x i2=1 ∨ x i2=x i1) (fresh : x i1 ≠ 1) :
      tau i1 i2=0 := by
    have G2 : G (y i2)=0 := by
      rcases eq with zz | zz
      · rw [y_same (zz.trans x0.symm),G0]
      · rw [y_same zz,G1]
    have e := shifted i2 le_rfl
    change B i0 i2*((y i0-y i0)*l i0)+B i1 i2*((y i1-Y)*l i1) = _ at e
    rw [G2] at e
    have gap : y i1-Y ≠ 0 := by
      intro g0
      apply fresh
      change y i1/Y=1
      rw [sub_eq_zero.mp g0,div_self Y0]
    have prod : B i1 i2*((y i1-Y)*l i1)=0 := by simpa using e
    have h : B i1 i2=0 := (mul_eq_zero.mp prod).resolve_right (mul_ne_zero gap l1)
    simp [tau,h]
  have frep (i j : Fin n) (nij : i≠j) (li : l i≠0) (lj : l j≠0)
      (xe : x i=x j) (fnz : f i≠0) (fe : f i=f j) : False := by
    have hye := y_same xe
    have ratio0 : b i*y i/l i≠0 := by
      rw [←fF i]
      exact mul_ne_zero fnz F0
    have yi : y i≠0 := by
      intro yz
      exact ratio0 (by simp [yz])
    exact ratios i j nij li lj hye yi ratio0 (by rw [←fF i,←fF j,fe])
  have hsecond : x i1≠1 := by
    intro eq
    have h := R1 i1 h21.le l1
    rw [t11,t01,eq] at h
    have ff : f i1=1 := by linear_combination -h
    exact frep i1 i0 h10.ne l1 l0 (eq.trans x0.symm) (by rw [ff]; exact one_ne_zero) (ff.trans f0.symm)
  refine normalized_tail_impossible (x i1) (f i1) (x i2) (f i2) (tau i0 i2)
    (tau i1 i2) a g ?_ ?_ ?_ (sumTau i2 le_rfl l2) (R1 i2 le_rfl l2)
    (R2 i2 le_rfl l2) (R3 i2 le_rfl l2) (fun h => repeat_tau h hsecond)
    (fun h => (hsecond h).elim) ?_ ?_
  · have h := R1 i1 h21.le l1
    rw [t11,t01] at h
    linear_combination h
  · have h := R2 i1 h21.le l1
    rw [t11,t01] at h
    linear_combination h
  · have h := R3 i1 h21.le l1
    rw [t11,t01] at h
    linear_combination h
  · intro h hf
    exact frep i2 i0 h20.ne l2 l0 (h.trans x0.symm)
      (by rw [hf]; exact one_ne_zero) (hf.trans f0.symm)
  · intro h hn hf
    exact frep i2 i1 h21.ne l2 l1 h (by rw [hf]; exact hn) hf

/-- The physical tail union is retained. An active zero-λ class is excluded
only when it is in the final three, by the five paid positive moments. -/
theorem causal_impossible {B : Matrix (Fin n) (Fin n) K} {b y l : Fin n → K}
    (strict : ∀ i j, i ≤ j → B i j = 0) (card : 3 ≤ (unionSupport b y l).card)
    (rows : CausalRows B b y l)
    (quiet45 : ∀ i, l i = 0 → foldedRow B b y 4 i = 0 ∧ foldedRow B b y 5 i = 0)
    (ratios : DistinguishedRatios b y l) : False := by
  classical
  obtain ⟨t⟩ := lastThree_of_card card
  apply causal_tail strict rows ratios t
  intro i hi hm zero
  have live := (mem_unionSupport.mp hm).resolve_left (not_not.mpr zero)
  apply quiet_tail_impossible strict t hi live
  intro k lo up
  have fork : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases fork with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_,_,h⟩ := rows.first
    simp [h,zero]
  · obtain ⟨_,h⟩ := rows.second
    simp [h,zero]
  · obtain ⟨_,_,h⟩ := rows.third
    simp [h,zero]
  · exact (quiet45 i zero).1
  · exact (quiet45 i zero).2

/-- Three rows suffice if the support inclusion has already been paid by
the actual class geometry. -/
theorem causal_impossible_of_mass_support {B : Matrix (Fin n) (Fin n) K} {b y l : Fin n → K}
    (strict : ∀ i j, i ≤ j → B i j = 0) (card : 3 ≤ (unionSupport b y l).card)
    (rows : CausalRows B b y l) (mass_support : ∀ i, l i=0 → b i*y i=0)
    (ratios : DistinguishedRatios b y l) : False := by
  classical
  obtain ⟨t⟩ := lastThree_of_card card
  apply causal_tail strict rows ratios t
  intro i _ hm zero
  have live := (mem_unionSupport.mp hm).resolve_left (not_not.mpr zero)
  exact live (mass_support i zero)

end RKResearch.Certified.Graded.NativeFinalThree

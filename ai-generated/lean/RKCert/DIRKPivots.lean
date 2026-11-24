module
public import RKCert.GradedOperators
public import RKCert.SDIRKCommutator
public import RKCert.EndpointPhysical

@[expose] public section
/-! Transfer from genuine tree stages at an actual chronological pivot to
formal polynomial moments.  A genuine zero-profile flag, not a weighted norm
or a purported stage-deletion rule, certifies the clean row. -/
namespace RKCert.Paired.Pivot
open RKCert RKCert.Paired
variable {K : Type*} [Field K] [CharZero K]
variable {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- All zero-profile features through this grade vanish at this physical row. -/
def Clean (A : Fin s → Fin s → K) (i : Fin s) (d : ℕ) : Prop :=
  ∀ x, x ∈ zeroSpace A d → x i = 0

/-- Entire strict prefix vanishes; the pivot need not be a new numerical clock. -/
def PrefixZero (v : Vec K s) (i : Fin s) : Prop := ∀ j, j < i → v j = 0

omit [CharZero K] in
theorem clean_down {i : Fin s} {m n : ℕ} (h : Clean A i n) (hm : m ≤ n) :
    Clean A i m := fun _ hx => h _ (zeroSpace_mono A hm hx)

omit [CharZero K] in
theorem mat_at_prefix (ha : SDIRK.lower A) (i : Fin s) (v : Vec K s)
    (hp : PrefixZero v i) : mat A v i = A i i*v i := by
  rw [mat_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_cases hj : j < i
    · rw [hp j hj,mul_zero]
    · rw [ha i j (lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hji)),zero_mul]
  · simp

omit [CharZero K] in
/-- Actual diagonal refund on a clean first-surviving coordinate. -/
theorem refund {i : Fin s} {v : Vec K s} {j : ℕ} (ha : SDIRK.lower A)
    (ho : HasTreeOrderAtLeast A b p) (hp : j+2 ≤ p)
    (hv : v ∈ treeSpace A j) (hpre : PrefixZero v i) (hn : v i ≠ 0)
    (hc : Clean A i (j+2)) : A i i = 0 := by
  have hx : SDIRK.R A v ∈ zeroSpace A (j+2) := commutator_mem_zeroSpace ho j hp hv
  have hg := hc _ hx
  rw [SDIRK.commutator_lead ha i v hpre] at hg
  have hz := (mul_eq_zero.mp hg).resolve_right hn
  exact sq_eq_zero_iff.mp (neg_eq_zero.mp hz)

/-- Numerical vector of the monomial shift x^k P(x). -/
noncomputable def evalShift (A : Fin s → Fin s → K) {n : ℕ} (f : Fin n → K) (k : ℕ) : Vec K s :=
  ∑ j : Fin n, f j • (fun i => nodes A i^(j.val+k))

/-- The primitive of a matched physical input has the formal value at a clean row.
The input's difference from the displayed scalar polynomial really belongs
to the genuine graded space F_g, as opposed to merely having zero output. -/
theorem primitive_value {g k n : ℕ} {v : Vec K s} {f : Fin n → K} {i : Fin s}
    (ho : HasTreeOrderAtLeast A b p) (hp : g+1 ≤ p)
    (hdeg : ∀ j : Fin n, j.val+k ≤ g)
    (hv : v-evalShift A f k ∈ zeroSpace A g) (hc : Clean A i (g+1)) :
    mat A v i = Endpoint.moment f (nodes A i) k := by
  have hd := hc _ (mat_zeroSpace ho g hp hv)
  have hvv : mat A v i = mat A (evalShift A f k) i := by
    simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using hd
  rw [hvv]
  have mon (j : Fin n) :
      mat A (fun l => nodes A l^(j.val+k)) i = nodes A i^(j.val+k+1)/((j.val+k+1:ℕ):K) := by
    let e := j.val+k
    have hx := primitive_mem_zeroSpace A e
    have hcj := hc _ (zeroSpace_mono A (by dsimp [e]; have := hdeg j; omega) hx)
    have hu := (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho)
      (by omega : 0<j.val+k+1) (by have := hdeg j; omega)).ne_zero
    apply (eq_div_iff hu).mpr
    change (((e+1:ℕ):K) * mat A (fun l => nodes A l^e) i - nodes A i^(e+1))=0 at hcj
    rw [mul_comm]
    exact sub_eq_zero.mp hcj
  simp only [evalShift, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Endpoint.moment,mon]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Once the physical diagonal has been refunded, any later mask of the
same zero prefix gives a genuine zero formal primitive at that pivot. -/
theorem masked_moment_vanish {g k n : ℕ} {i : Fin s} {v : Vec K s} {f : Fin n → K}
    (ha : SDIRK.lower A) (ho : HasTreeOrderAtLeast A b p) (hp : g+1≤p)
    (hdeg : ∀ j : Fin n, j.val+k≤g) (hv : v-evalShift A f k ∈ zeroSpace A g)
    (hc : Clean A i (g+1)) (hs : PrefixZero v i) (hz : A i i=0) :
    Endpoint.moment f (nodes A i) k = 0 := by
  rw [← primitive_value ho hp hdeg hv hc,mat_at_prefix ha i v hs,hz,zero_mul]


/-- The numerical monomial mask of a physical stage column. -/
def clockPow (A : Fin s → Fin s → K) (k : ℕ) (v : Vec K s) : Vec K s :=
  fun i => nodes A i ^ k * v i

omit [CharZero K] in
theorem clockPow_zero (v : Vec K s) : clockPow A 0 v = v := by
  ext i; simp [clockPow]

omit [CharZero K] in
theorem clockPow_succ (v : Vec K s) (k : ℕ) :
    clockPow A (k+1) v = diag (nodes A) (clockPow A k v) := by
  ext i; simp only [clockPow,diag_apply,pow_succ]; ring

omit [CharZero K] in
theorem evalShift_succ {n : ℕ} (f : Fin n → K) (k : ℕ) :
    evalShift A f (k+1) = diag (nodes A) (evalShift A f k) := by
  rw [evalShift,evalShift,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  congr 1
  ext i
  simp only [diag_apply,Nat.add_succ,pow_succ]
  ring

omit [CharZero K] in
/-- Repeated clock masking is paid one grade at a time. -/
theorem shifted_match {g n : ℕ} {v : Vec K s} {f : Fin n → K}
    (hm : v-evalShift A f 0 ∈ zeroSpace A g) (k : ℕ) :
    clockPow A k v-evalShift A f k ∈ zeroSpace A (g+k) := by
  induction k with
  | zero => simpa only [clockPow_zero,Nat.add_zero] using hm
  | succ k ih =>
    rw [clockPow_succ,evalShift_succ,←map_sub]
    exact diag_zeroSpace A (g+k) ih

omit [CharZero K] in
theorem evalShift_tree {g k n : ℕ} (f : Fin n → K) (deg : ∀ j : Fin n, j.val+k ≤ g) :
    evalShift A f k ∈ treeSpace A g := by
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  change (fun i => nodes A i^(j.val+k)) ∈ treeSpace A g
  have e (i : Fin s) := stageWeight_bush A (j.val+k) i
  rw [←(show stageWeight A (Tree.bush (j.val+k)) = (fun i => nodes A i^(j.val+k)) from funext e)]
  exact stageWeight_mem_space A _ (by rw [Tree.order_bush]; have := deg j; omega)

omit [CharZero K] in
theorem shifted_tree {g n : ℕ} {v : Vec K s} {f : Fin n → K}
    (deg : ∀ j : Fin n, j.val ≤ g) (hm : v-evalShift A f 0 ∈ zeroSpace A g) (k : ℕ) :
    clockPow A k v ∈ treeSpace A (g+k) := by
  have h := zeroSpace_le_treeSpace A _ (shifted_match hm k)
  have e : evalShift A f k ∈ treeSpace A (g+k) :=
    evalShift_tree f (fun j => Nat.add_le_add_right (deg j) k)
  simpa only [sub_add_cancel] using (treeSpace A (g+k)).add_mem h e

/-- The second physical input after killing the first nonzero abscissa. -/
def secondMask (A : Fin s → Fin s → K) (u : K) (k : ℕ) (v : Vec K s) : Vec K s :=
  clockPow A (k+1) v - u • clockPow A k v

/-- At the two original physical pivots, true flag agreement and chronology alone
supply the exact absolute first and second endpoint tests. No primitive
integrals or refunds are assumed in the premises. -/
theorem extract_two {g n d : ℕ} {f : Fin n → K} {v : Vec K s} {i l : Fin s}
    (ha : SDIRK.lower A) (ho : HasTreeOrderAtLeast A b p)
    (hd : 3 ≤ d) (hp : g+d+1 ≤ p)
    (deg : ∀ j : Fin n, j.val ≤ g) (hm : v-evalShift A f 0 ∈ zeroSpace A g)
    (hci : Clean A i (g+d+1)) (hcl : Clean A l (g+d+1))
    (pi : PrefixZero (clockPow A 1 v) i) (ni : clockPow A 1 v i ≠ 0)
    (pl : PrefixZero (secondMask A (nodes A i) 1 v) l)
    (nl : secondMask A (nodes A i) 1 v l ≠ 0) :
    EndpointPhysical.tests f (nodes A i) (nodes A l) d := by
  let u := nodes A i
  let z := nodes A l
  have zero_i : A i i=0 := refund ha ho (by omega) (shifted_tree deg hm 1) pi ni
    (clean_down hci (by omega))
  have mx (k : ℕ) : secondMask A u k v ∈ treeSpace A (g+k+1) := by
    apply Submodule.sub_mem _ (shifted_tree deg hm (k+1))
    exact (treeSpace A (g+k+1)).smul_mem _ (treeSpace_mono A (by omega : g+k≤g+k+1) (shifted_tree deg hm k))
  have zero_l : A l l=0 := refund ha ho (by omega) (mx 1) pl nl (clean_down hcl (by omega))
  have firstShift (k : ℕ) (hkd : k≤d) (ik : Fin s) (hclean : Clean A ik (g+d+1)) :
      mat A (clockPow A k v) ik = Endpoint.moment f (nodes A ik) k :=
    primitive_value ho (by omega) (fun j => Nat.add_le_add_right (deg j) k)
      (shifted_match hm k) (clean_down hclean (by omega))
  have first (j : Fin d) : Endpoint.moment f u (j.val+1)=0 := by
    rw [←firstShift _ (by omega : j.val+1≤d) i hci,mat_at_prefix ha i _ _,zero_i,zero_mul]
    intro t ht
    have h := pi t ht
    change nodes A t^1 * v t=0 at h
    change nodes A t^(j.val+1)*v t=0
    rw [pow_one] at h
    rw [pow_succ,mul_assoc,h,mul_zero]
  have second (k : ℕ) (hk : 1≤k) (hk' : k≤2) :
      Endpoint.moment f z (k+1) - u*Endpoint.moment f z k=0 := by
    have hz : mat A (secondMask A u k v) l =0 := by
      rw [mat_at_prefix ha l _ _,zero_l,zero_mul]
      intro t ht
      have h := pl t ht
      change nodes A t^2*v t-u*(nodes A t^1*v t)=0 at h
      change nodes A t^(k+1)*v t-u*(nodes A t^k*v t)=0
      have eqk : k=1 ∨ k=2 := by omega
      rcases eqk with rfl|rfl
      · exact h
      · linear_combination nodes A t*h
    change mat A (clockPow A (k+1) v - u • clockPow A k v) l = 0 at hz
    rw [map_sub,map_smul] at hz
    change mat A (clockPow A (k+1) v) l - u * mat A (clockPow A k v) l =0 at hz
    rwa [firstShift _ (by omega) l hcl,firstShift _ (by omega) l hcl] at hz
  exact ⟨first,second 1 (by decide) (by decide),second 2 (by decide) (by decide)⟩

end RKCert.Paired.Pivot


module

public import RKCert.ReviewedNative.GradedPrimitives
public import RKCert.ReviewedNative.RowAnnihilator
public import RKCert.ReviewedNative.OrderedAlternationDegree
import RKCert.ReviewedNative.GradedSeparation
import RKCert.ReviewedNative.OrderedNodalGain
import RKCert.ReviewedNative.OneWeightOrderedSigns
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A paid live coordinate at clock one forces interior clean clocks

This does not assume a stage count, a reverse rank, or a formula for the
forward defect space. The nineteen-point rule is used only at degree at
most nineteen. A sign change is never used to assert a root.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped BigOperators Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The literal clock component of an original paid coordinate, after
removing the initial factor X. Simplicity is stated by square divisibility. -/
structure PaidEndpointClock {s : ℕ} (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1) → K) (q : ℕ) (t : Fin (s+1)) (J : K[X]) : Prop where
  nonzero : J≠0
  degree : J.natDegree=q-1
  decomposition : ∃ f∈zeroSpace A q, evalNodes A (X*J)+f=coordinate (K:=K) t
  moment : ∀ T : K[X], T.natDegree≤q-1 → integral 0 1 (X*J*T)=b t*T.eval 1
  variation : HasAlternationsOn J (Set.Ioo (0:K) 1) (q-1)
  rootsInside : ∀ x, J.eval x=0 → x∈Set.Ioo (0:K) 1
  simple : ∀ x : K, ¬((X-C x)^2 ∣ J)
  endpointSign : 0<b t*J.eval 1

private theorem unitSquarePositive {U S : K[X]} (sn : S≠0) (small : S.natDegree<19)
    (budget : (U*S^2).natDegree≤19) (pos : ∀ x∈Set.Ioo (0:K) 1, 0<U.eval x) :
    0 < integral 0 1 (U*S^2) := by
  have lr : (0:K)<1 := zero_lt_one
  obtain ⟨i,hi⟩ := exists_nonzero_grid_sample lr sn small
  refine integral_pos_of_grid_samples lr budget ?_ ⟨i,?_⟩
  · intro j
    simp only [eval_mul,eval_pow]
    exact mul_nonneg (pos _ (intervalPoint_mem lr j)).le (sq_nonneg _)
  · simp only [eval_mul,eval_pow]
    exact mul_pos (pos _ (intervalPoint_mem lr i)) (sq_pos_iff.mpr hi)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem squareBudget {U S : K[X]} {u d : ℕ}
    (bu : U.natDegree≤u) (bd : S.natDegree≤d) (budget : u+2*d≤19) :
    (U*S^2).natDegree≤19 := by
  have h := natDegree_mul_le (p:=U) (q:=S^2)
  rw [natDegree_pow] at h
  omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem endpointWeight_degree : ((1-X) : K[X]).natDegree≤1 :=
  natDegree_sub_le_of_le (p:=(1 : K[X])) (q:=X) (by rw [natDegree_one]) (natDegree_X (R:=K)).le

private theorem momentFromMonomials {m : ℕ} {P T : K[X]} {b₀ : K}
    (td : T.natDegree≤m) (paid : ∀ k≤m, integral 0 1 (P*X^k)=b₀) :
    integral 0 1 (P*T)=b₀*T.eval 1 := by
  let L : K[X] →ₗ[K] K := (integral 0 1).comp (LinearMap.mulLeft K P)
  let R : K[X] →ₗ[K] K := b₀ • Polynomial.leval 1
  have mono (k : ℕ) (km : k≤m) : L (X^k)=R (X^k) := by
    change integral 0 1 (P*X^k)=b₀*(X^k : K[X]).eval 1
    simpa only [eval_pow,eval_X,one_pow,mul_one] using paid k km
  have e : L T=R T := by
    rw [T.as_sum_range' (m+1) (by omega),map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have km : k≤m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul,map_smul,mono k km]
  exact e

private theorem scalarEndpointGeometry {q : ℕ} {J : K[X]} {b₀ : K}
    (q₂ : 2≤q) (q₁₀ : q≤10) (jn : J≠0) (jd : J.natDegree≤q-1)
    (paid : ∀ T : K[X], T.natDegree≤q-1 → integral 0 1 (X*J*T)=b₀*T.eval 1) :
    J.natDegree=q-1 ∧ HasAlternationsOn J (Set.Ioo (0:K) 1) (q-1) ∧
      (∀ x, J.eval x=0 → x∈Set.Ioo (0:K) 1) ∧ (∀ x : K, ¬((X-C x)^2 ∣ J)) ∧
      0<b₀*J.eval 1 := by
  let W : K[X] := X*(1-X)
  have wd : W.natDegree≤2 := natDegree_mul_le_of_le
    (natDegree_X (R:=K)).le (endpointWeight_degree (K:=K))
  have wp (x : K) (hx : x∈Set.Ioo (0:K) 1) : 0<W.eval x := by
    simpa only [W,eval_mul,eval_sub,eval_one,eval_X] using mul_pos hx.1 (sub_pos.mpr hx.2)
  have orth (T : K[X]) (td : T.natDegree≤q-2) : integral 0 1 (W*J*T)=0 := by
    have hm : ((1-X)*T).natDegree≤q-1 :=
      (natDegree_mul_le_of_le (endpointWeight_degree (K:=K)) td).trans (by omega)
    have p := paid ((1-X)*T) hm
    have eq : X*J*((1-X)*T)=W*J*T := by dsimp [W]; ring
    have ez : ((1-X)*T).eval (1:K)=0 := by simp
    rwa [eq,ez,mul_zero] at p
  have alt : HasAlternationsOn J (Set.Ioo (0:K) 1) (q-1) := by
    refine HasAlternationsOn.of_grid zero_lt_one
      (grid_variation_of_positive_moments (U:=W) (m:=q-1) zero_lt_one jn
        (by omega) (by omega) wp ?_)
    intro k
    have hk := k.isLt
    exact orth (X^k.val) (by rw [natDegree_X_pow]; omega)
  have jdExact : J.natDegree=q-1 := Nat.le_antisymm jd alt.le_natDegree
  refine ⟨jdExact,alt,?_,?_,?_⟩
  · intro x xr
    obtain ⟨S,fac⟩ := (dvd_iff_isRoot (p:=J) (a:=x)).mpr xr
    have sn : S≠0 := fun h=>jn (by rw [fac,h,mul_zero])
    have sd : S.natDegree≤q-2 := by
      have je := jdExact
      rw [fac,natDegree_mul (X_sub_C_ne_zero x) sn,natDegree_X_sub_C] at je
      omega
    let U : K[X] := W*(X-C x)
    have ud : U.natDegree≤3 := natDegree_mul_le_of_le wd (natDegree_X_sub_C x).le
    have z : integral 0 1 (U*S^2)=0 := by
      have p := orth S sd
      have eq : W*J*S=U*S^2 := by rw [fac]; dsimp [U]; ring
      rwa [eq] at p
    have budget : (U*S^2).natDegree≤19 := squareBudget ud sd (by omega)
    by_cases x0 : x≤0
    · exfalso
      have pos (y : K) (hy : y∈Set.Ioo (0:K) 1) : 0<U.eval y := by
        simp only [U,eval_mul,eval_sub,eval_X,eval_C]
        exact mul_pos (wp y hy) (sub_pos.mpr (x0.trans_lt hy.1))
      exact (unitSquarePositive sn (by omega) budget pos).ne' z
    by_cases x1 : x<1
    · exact ⟨lt_of_not_ge x0,x1⟩
    · exfalso
      have nBudget : ((-U)*S^2).natDegree≤19 := by
        rw [neg_mul,natDegree_neg]
        exact budget
      have nz : integral 0 1 ((-U)*S^2)=0 := by rw [neg_mul,map_neg,z,neg_zero]
      have pos (y : K) (hy : y∈Set.Ioo (0:K) 1) : 0<(-U).eval y := by
        simp only [U,eval_neg,eval_mul,eval_sub,eval_X,eval_C]
        exact neg_pos.mpr (mul_neg_of_pos_of_neg (wp y hy)
          (sub_neg.mpr (hy.2.trans_le (le_of_not_gt x1))))
      exact (unitSquarePositive sn (by omega) nBudget pos).ne' nz
  · intro x h
    obtain ⟨S,fac⟩ := h
    have sn : S≠0 := fun h=>jn (by rw [fac,h,mul_zero])
    have xn : (X-C x : K[X])≠0 := X_sub_C_ne_zero x
    have degS : S.natDegree+2=q-1 := by
      have e := jdExact
      rw [fac,natDegree_mul (pow_ne_zero _ xn) sn,natDegree_pow,natDegree_X_sub_C] at e
      omega
    let Z : K[X] := (X-C x)*S
    have zn : Z≠0 := mul_ne_zero xn sn
    have zd : Z.natDegree≤q-2 := by
      have h := natDegree_mul_le (p:=X-C x) (q:=S)
      rw [natDegree_X_sub_C] at h
      dsimp only [Z]
      omega
    have z : integral 0 1 (W*Z^2)=0 := by
      have p := orth S (by omega)
      have eq : W*J*S=W*Z^2 := by rw [fac]; dsimp [Z]; ring
      rwa [eq] at p
    exact (unitSquarePositive zn (by omega) (squareBudget wd zd (by omega)) wp).ne' z
  · have eq : X*J*J=X*J^2 := by ring
    have mass := paid J jd
    rw [eq] at mass
    rw [←mass]
    apply unitSquarePositive jn (by omega)
      (squareBudget (natDegree_X (R:=K)).le jd (by omega))
    intro x hx
    simpa only [eval_X] using hx.1

/-- A live original coordinate at clock one in the paid even midpoint
has an exact endpoint polynomial. The argument does not use a width cap. -/
theorem paid_endpoint_clock_of_coordinate {s p q : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K} {t : Fin (s+1)}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (q₂ : 2≤q) (q₁₀ : q≤10) (pay : 2*q≤p)
    (atOne : nodes A t=1) (live : b t≠0)
    (hcoord : coordinate (K:=K) t∈treeSpace A q) :
    ∃ J : K[X], PaidEndpointClock A b q t J := by
  classical
  rw [treeSpace_coeff_sup ho (by omega)] at hcoord
  obtain ⟨v,hv,f,hf,eq⟩ := Submodule.mem_sup.mp hcoord
  obtain ⟨a,rfl⟩ := hv
  let P : K[X] := ∑ j : Fin (q+1), monomial j.val (a j)
  have pd : P.natDegree≤q := by
    dsimp only [P]
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ j.isLt)
  have evalP : evalNodes A P=coeffEval A q a := by
    ext i
    simp only [P,evalNodes_apply,eval_finsetSum,eval_monomial,coeffEval_apply,
      Finset.sum_apply,normTree_clockTree,Pi.smul_apply,smul_eq_mul]
  have eP : evalNodes A P+f=coordinate (K:=K) t := by rw [evalP]; exact eq
  have c0 : nodes A 0=0 := by
    simp only [nodes,Matrix.mulVec,dotProduct]
    exact Finset.sum_eq_zero (fun i _=>by rw [ha 0 i (Fin.zero_le i),zero_mul])
  have nt : (0:Fin (s+1))≠t := fun e=>zero_ne_one (c0.symm.trans (e.symm ▸ atOne))
  have startZero : coordinate (K:=K) t 0=0 := by simp [coordinate,nt]
  have p₀ : P.eval 0=0 := by
    have e := congrFun eP 0
    have f0 : f 0=0 := origin_zeroSpace ha q hf
    rwa [Pi.add_apply,evalNodes_apply,c0,f0,add_zero,startZero] at e
  have monomials (k : ℕ) (kq : k≤q-1) : integral 0 1 (P*X^k)=b t := by
    have e := congrArg (probe A b k) eP
    have hf0 : probe A b k f=0 := probe_zeroSpace ho (by omega) hf
    have ht : probe A b k (coordinate (K:=K) t)=b t := by
      change row _ (coordinate (K:=K) t)=b t
      rw [row_coordinate,atOne,one_pow,mul_one]
    rw [map_add,hf0,add_zero,ht,probe_evalNodes ho P k (by omega)] at e
    rw [integral_zero_left,formalPrimitive_eq_native,mul_comm P (X^k)]
    exact e
  have pn : P≠0 := by
    intro h
    have z : 0=b t := by simpa only [h,zero_mul,map_zero] using monomials 0 (by omega)
    exact live z.symm
  have xdvd : (X : K[X]) ∣ P := by rw [X_dvd_iff,coeff_zero_eq_eval_zero,p₀]
  obtain ⟨J,fac⟩ := xdvd
  have jn : J≠0 := fun h=>pn (by rw [fac,h,mul_zero])
  have jd : J.natDegree≤q-1 := by
    rw [fac,natDegree_X_mul jn] at pd
    omega
  have mom (T : K[X]) (td : T.natDegree≤q-1) : integral 0 1 (X*J*T)=b t*T.eval 1 := by
    rw [←fac]
    exact momentFromMonomials td monomials
  obtain ⟨jdExact,alt,inside,simple,sign⟩ := scalarEndpointGeometry q₂ q₁₀ jn jd mom
  exact ⟨J,⟨jn,jdExact,⟨f,hf,by simpa only [fac] using eP⟩,mom,alt,inside,simple,sign⟩⟩

variable {s q : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
    {t : Fin (s+1)} {J : K[X]}

theorem PaidEndpointClock.root_at_clean (H : PaidEndpointClock A b q t J)
    {i : Fin (s+1)} (off : i≠t) (cn : nodes A i≠0)
    (clean : ∀ f∈zeroSpace A q, f i=0) : J.eval (nodes A i)=0 := by
  classical
  obtain ⟨f,hf,eq⟩ := H.decomposition
  have h := congrFun eq i
  have iz : coordinate (K:=K) t i=0 := by simp [coordinate,off,Ne.symm off]
  rw [Pi.add_apply,evalNodes_apply,eval_mul,eval_X,clean f hf,add_zero,iz] at h
  exact (mul_eq_zero.mp h).resolve_left cn

/-- In particular a single exterior nonzero clean clock off the paid
coordinate contradicts the endpoint geometry. -/
theorem PaidEndpointClock.clean_clock_interior (H : PaidEndpointClock A b q t J)
    {i : Fin (s+1)} (off : i≠t) (cn : nodes A i≠0)
    (clean : ∀ f∈zeroSpace A q, f i=0) : nodes A i∈Set.Ioo (0:K) 1 :=
  H.rootsInside _ (H.root_at_clean off cn clean)

/-- The count is of distinct numerical clocks, not physical rows. -/
theorem PaidEndpointClock.clean_clock_card_le (H : PaidEndpointClock A b q t J)
    (S : Finset K)
    (actual : ∀ x∈S, x≠0 ∧ ∃ i : Fin (s+1), i≠t ∧ nodes A i=x ∧
      ∀ f∈zeroSpace A q, f i=0) : S.card≤q-1 := by
  classical
  have sub : S ⊆ J.roots.toFinset := by
    intro x hx
    obtain ⟨xn,i,off,cx,clean⟩ := actual x hx
    have cn : nodes A i≠0 := fun e=>xn (cx.symm.trans e)
    rw [Multiset.mem_toFinset,Polynomial.mem_roots H.nonzero]
    change J.eval x=0
    rw [←cx]
    exact H.root_at_clean off cn clean
  calc
    S.card ≤ J.roots.toFinset.card := Finset.card_le_card sub
    _ ≤ J.roots.card := Multiset.toFinset_card_le _
    _ ≤ J.natDegree := Polynomial.card_roots' J
    _ = q-1 := H.degree

end
end RKResearch.Certified.Graded.Reverse

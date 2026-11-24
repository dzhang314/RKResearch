module

public import RKCert.ReviewedNative.ERK17HiddenFrame

@[expose] public section

/-! # Signed contrast count on the actual width-26 zero-seed rows

The scalar gate is a fixed eight-moment Radau first-primitive condition;
it does not refer to a tableau, row order, or RK order. The geometry
pays all of its inputs on the reviewed matrix. -/
namespace RKResearch.Certified.ERK17
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKResearch.Certified.Graded.NativeMoments
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

def RadauFirstGate (K : Type*) [Field K] : Prop :=
  ∀ (Q N : K[X]) (u : K), Q≠0 → Q.natDegree≤5 →
    N≠0 → N.natDegree=3 → N.eval u=0 → u≠0 →
    (∀ k : Fin 8, (primitive (X^k.val*(X*(Q*N)))).eval 1=0) →
    (primitive (X*Q)).eval u≠0

/-- A moment-annihilating signed physical vector pays twice for each of its
numerically distinct knots, unless there are already enough distinct knots.
This counts actual coordinates, never aggregate atoms or nominal nodes. -/
theorem signed_fiber_payment (y v:(Fin s→K)) (k:ℕ) (hk:k≤(weightedSites y v).card)
    (mom:∀P:K[X],P.natDegree+2≤2*k → (∑i:Fin s,v i*P.eval (y i))=0) :
    2*k≤(Finset.univ.filter fun i=>v i≠0).card := by
  classical
  let I:=Finset.univ.filter fun i=>v i≠0
  let S:=I.image y
  change k≤S.card at hk
  change 2*k≤I.card
  by_cases big:2*k≤S.card
  · exact big.trans (Finset.card_image_le)
  have fiber (a:K) (ha:a∈S) : 2≤(I.filter fun t=>y t=a).card := by
    by_contra! small
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    have hvi:v i≠0:=(Finset.mem_filter.mp hi).2
    let T:=S.erase (y i)
    let P:=Lagrange.nodal T id
    have ndeg:P.natDegree+2≤2*k := by
      rw [show P.natDegree=T.card from Lagrange.natDegree_nodal,show T.card=S.card-1 from Finset.card_erase_of_mem ha]
      have pos:S.card≠0 := Finset.card_ne_zero.mpr ⟨_,ha⟩
      omega
    have pvi:P.eval (y i)≠0 := Lagrange.eval_nodal_not_at_node (fun z hz e=>by
      have ne:z≠y i:=(Finset.mem_erase.mp hz).1; exact ne e.symm)
    have zero (j:Fin s) (ne:j≠i) : v j*P.eval (y j)=0 := by
      by_cases vj:v j=0
      · simp [vj]
      have hIj:j∈I:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,vj⟩
      have yne:y j≠y i:=by
        intro eqn
        apply ne
        exact Finset.card_le_one.mp (by omega : (I.filter fun t=>y t=y i).card≤1)
          j (Finset.mem_filter.mpr ⟨hIj,eqn⟩) i (Finset.mem_filter.mpr ⟨hi,rfl⟩)
      have hT:y j∈T:=Finset.mem_erase.mpr ⟨yne,Finset.mem_image_of_mem y hIj⟩
      rw [show P.eval (y j)=0 from Lagrange.eval_nodal_at_node (v:=id) hT,mul_zero]
    have eqn:=mom P ndeg
    rw [Finset.sum_eq_single i (fun j _ h=>zero j h) (fun h=>False.elim (h (Finset.mem_univ _)))] at eqn
    exact mul_ne_zero hvi pvi eqn
  calc
    2*k≤2*S.card := by omega
    _ = ∑ _a∈S,2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a∈S,(I.filter fun t=>y t=a).card := Finset.sum_le_sum fiber
    _ = I.card := (Finset.card_eq_sum_card_image y I).symm

variable [CharZero K]

set_option maxRecDepth 3500 in
set_option maxHeartbeats 950000 in
theorem width26_contrast_four_sites_of_radau (gate : RadauFirstGate K)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (Z : Width26QuadraticCover A b) (Q P : K[X]) (qn : Q≠0)
    (qd : Q.natDegree≤5) (pd : P.natDegree≤4)
    (off : ∀ i, reverseContrast A b Q P i≠0 → quadraticSeed A b i=0) :
    4≤(weightedSites (reflectedClock A) (reverseContrast A b Q P)).card := by
  classical
  let W := reverseContrast A b Q P
  let Y := reflectedClock A
  let T := weightedSites Y W
  let N := nodalHull T
  have nn : N≠0 := (monic_nodalHull T).ne_zero
  have deg : N.natDegree=T.card := natDegree_nodalHull T
  have root (a : K) (ha : a∈T) : N.eval a=0 := nodalHull_eval_of_mem ha
  change 4≤T.card
  by_contra! small
  have three : T.card=3 := by
    by_contra neq
    have lim : T.card≤2 := by omega
    let H := Q*N
    have hdeg : H.natDegree≤7 := by
      have e := natDegree_mul_le (p:=Q) (q:=N)
      dsimp [H]
      omega
    have tests (k : Fin 8) : (primitive (X^k.val*(X*H))).eval 1=0 := by
      let R : K[X] := X^k.val*N
      have rdeg : R.natDegree ≤ k.val+T.card := by
        dsimp only [R]
        exact natDegree_mul_le_of_le (natDegree_X_pow _).le deg.le
      have z : (∑ i,weightedEval Y W R i)=0 :=
        reverse_contrast_vanishes W R (fun a ha => by simp [R,root a ha])
      have m := reverse_contrast_moment ho Q P R (by have := k.isLt; omega)
        (by have := k.isLt; omega)
      rw [z] at m
      rw [show X^k.val*(X*H)=R*(X*Q) by dsimp [R,H];ring]
      exact m.symm
    exact (mul_ne_zero qn nn) (x_moments_detect hdeg tests)
  have tests (k : Fin 8) : (primitive (X^k.val*(X*(Q*N)))).eval 1=0 := by
    let R : K[X] := X^k.val*N
    have rdeg : R.natDegree ≤ k.val+T.card := by
      dsimp only [R]
      exact natDegree_mul_le_of_le (natDegree_X_pow _).le deg.le
    have z : (∑ i,weightedEval Y W R i)=0 :=
      reverse_contrast_vanishes W R (fun a ha => by simp [R,root a ha])
    have m := reverse_contrast_moment ho Q P R (by have := k.isLt; omega)
      (by have := k.isLt; omega)
    rw [z] at m
    rw [show X^k.val*(X*(Q*N))=R*(X*Q) by dsimp [R];ring]
    exact m.symm
  let I := Hidden.activeRows W
  have ne : I.Nonempty := by
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0<T.card)
    obtain ⟨i,ni,_⟩ := mem_weightedSites.mp ha
    exact ⟨i,Hidden.mem_activeRows i |>.mpr ni⟩
  let i := I.max' ne
  have wi : W i≠0 := (Hidden.mem_activeRows i).mp (I.max'_mem ne)
  have pre (j : Fin 26) (hj : i<j) : W j=0 := by
    by_contra nz
    exact (not_le_of_gt hj) (I.le_max' _ ((Hidden.mem_activeRows j).mpr nz))
  have un : Y i≠0 := by
    intro z
    apply wi
    simp [W,reverseContrast,show reflectedClock A i=0 from z,off i wi]
  have bi : b i≠0 := by
    intro z
    apply wi
    simp [W,reverseContrast,z,off i wi]
  let t := Fin.last 25
  have y0 : Y t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have col (j : Fin 26) : A j t=0 := ha j t (Fin.le_last j)
  have cov : SupportsComplement A b 8 t := supportsComplement_of_cover Z.pointwise
  have e := true_port_eval ho y0 col cov Q P (1:K[X]) (by simp only [natDegree_one]; omega) (by simp only [natDegree_one]; omega) (off i wi)
  have z : mat A.transpose (weightedEval Y W (1:K[X])) i=0 := by
    apply causal_transpose ha
    intro j hj
    simp [pre j (Fin.rev_lt_rev.mp hj)]
  rw [z,one_mul] at e
  exact gate Q N (Y i) qn qd nn (deg.trans three) (root _ (mem_weightedSites.mpr ⟨i,wi,rfl⟩)) un tests
    ((mul_eq_zero.mp e.symm).resolve_right bi)

end
end RKResearch.Certified.ERK17

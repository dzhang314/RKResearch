module

public import RKCert.ReviewedNative.ERKOrder16WeakHead
public import RKCert.ReviewedNative.ERKOrder16WeakFiveAdmission
public import RKCert.ReviewedNative.PhysicalEndpointMomentPorts
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical Matrix

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
variable {U : Submodule K (Fin 24 → K)} {w θ : Fin 24 → K}
variable {q Q P : K[X]}

/-- The grade-four source admits an exact forward evaluation at
every contrast row. The off-contrast origin is explicitly retained. -/
structure Width24RankThreeWeakMask (A : Matrix (Fin 24) (Fin 24) K)
    (b : Fin 24 → K) (q Q P : K[X]) (θ : Fin 24 → K) : Prop where
  degree : q.natDegree ≤ 4
  reflected : ∀ x, q.eval x = Q.eval (1-x)
  originValue : θ 0 = q.eval 0
  outside : ∀ i, i ∉ weakFiveRows A b Q P → i ≠ 0 → i ≠ Fin.last 23 → θ i = 0
  contrastValue : ∀ i ∈ weakFiveRows A b Q P, θ i = q.eval (nodes A i)
  active : ∀ i ∈ weakFiveRows A b Q P, q.eval (nodes A i) ≠ 0
  paid : ∀ (R : K[X]), R.natDegree ≤ 2 → ∀ i ∈ weakFiveRows A b Q P,
    mat A (weightedEval (nodes A) θ R) i = (primitive (R*q)).eval (nodes A i)

theorem Width24OrdinaryWeakHead.rank_three_forward_mask
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (rankThree : finrank K (width24WeakFiveCarrier A b) = 3) :
    ∃ (q : K[X]) (θ : Fin 24 → K), Width24RankThreeWeakMask A b q Q P θ := by
  classical
  let c := nodes A
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let V := weakFiveRows A b Q P
  let H := width24WeakFiveCarrier A b
  let G := Hidden.blindRows c b d 0 t
  have base := L.flat.baseRank
  have low := grade_five_surplus_of_reviewed_order ha ho (by decide : 10 ≤ 16)
  have HU : finrank K H ≤ finrank K U := by
    change finrank K (width24WeakFiveCarrier A b) ≤ finrank K U
    omega
  have eqH : U = H := Submodule.eq_of_le_of_finrank_le L.coreInside HU
  have seventh : zeroSpace A 7 = chain (diag c) H w 4 := by
    rw [← eqH]
    exact L.flat.flags 2 (by decide)
  have unpaid : ((diag c)^4) w ∉ zeroSpace A 7 := L.flat.unpaid
  obtain ⟨_, shape⟩ := weak_five_grade_four_of_strip ha ho rankThree seventh unpaid
  have H4 : H ≤ zeroSpace A 4 := le_sup_left.trans shape.ge
  have w4 : w ∈ zeroSpace A 4 := shape.ge
    ((show (K ∙ w : Submodule K (Fin 24 → K)) ≤ H ⊔ K ∙ w from le_sup_right) (Submodule.mem_span_singleton_self w))
  have F := width24_paid_frame ha ho
  have dt : d t = 0 := (width24_quadratic_cover ha ho).lastSeed
  have c0 : c 0 = 0 := by
    change (∑ j, A 0 j * (1 : K)) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j), zero_mul]
  have contrast (i : Fin 24) (hi : i ∈ V) :
      d i = 0 ∧ y i ≠ 0 ∧ b i ≠ 0 ∧ Q.eval (y i) ≠ 0 ∧ w i = 0 :=
    reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp hi)
  have f7 (x : Fin 24 → K) (hx : x ∈ zeroSpace A 7) (i : Fin 24) (hi : i ∈ V) :
      x i = 0 := by
    obtain ⟨_, yi, bi, _, wi⟩ := contrast i hi
    obtain ⟨u, hu, R, _, rfl⟩ := HeadFiber.exists_poly (seventh.le hx)
    have ui : u i = 0 := (mul_eq_zero.mp
      (Hidden.carrier_mirror_weight_zero F.lastClock hu i)).resolve_left (mul_ne_zero yi bi)
    simp only [Pi.add_apply, weightedEval_apply, ui, wi, mul_zero, add_zero]
  let q := Q.comp (1-X)
  have aff : (1-X : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have qd : q.natDegree ≤ 4 := natDegree_comp_le.trans
    (by simpa only [mul_one] using Nat.mul_le_mul L.qDegree aff)
  have refl (x : K) : q.eval x = Q.eval (1-x) := by simp [q, eval_comp]
  obtain ⟨g, hg, gval⟩ := Hidden.carrier_filler (f := evalNodes A q-w) F.lastLive.live
  let z := w+g
  let θ := evalNodes A q-z
  have z4 : z ∈ zeroSpace A 4 := (zeroSpace A 4).add_mem w4 (H4 hg)
  have z0 : z 0 = 0 := origin_zeroSpace ha 4 z4
  refine ⟨q,θ,⟨qd,refl,?_,?_,?_,?_,?_⟩⟩
  · change q.eval (c 0)-z 0 = q.eval 0
    rw [c0,z0,sub_zero]
  · intro i ni io it
    change i ≠ t at it
    change q.eval (c i)-(w i+g i)=0
    by_cases ig : i ∈ G
    · have e : g i = q.eval (c i)-w i := gval i ig
      rw [e]
      ring
    · by_cases di : d i = 0
      · have yb : y i*b i ≠ 0 := by
          intro e
          exact ig ((Hidden.mem_blindRows i).mpr ⟨io,it,di,e⟩)
        have wp : (y i*b i)*w i = 0 := by
          have e := L.pFit i
          change (y i*b i)*w i = P.eval (y i)*d i at e
          simpa only [di,mul_zero] using e
        have wi := (mul_eq_zero.mp wp).resolve_left yb
        have gi : g i = 0 := (mul_eq_zero.mp
          (Hidden.carrier_mirror_weight_zero F.lastClock hg i)).resolve_left yb
        have v0 : reverseContrast A b Q P i = 0 := by
          by_contra nz
          exact ni ((mem_weakFiveRows i).mpr nz)
        have fact : (y i*b i)*Q.eval (y i) = 0 := by
          calc
            _ = reverseContrast A b Q P i := by
              simp only [reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X]
              change y i*b i*Q.eval (y i) =
                y i*Q.eval (y i)*b i - P.eval (y i)*d i
              rw [di]
              ring
            _ = 0 := v0
        have qi : q.eval (c i) = 0 := (refl (c i)).trans
          ((mul_eq_zero.mp fact).resolve_left yb)
        rw [qi,wi,gi,add_zero,sub_zero]
      · have eq := L.qFit i
        change d i*w i = Q.eval (y i)*d i at eq
        rw [mul_comm (Q.eval (y i)) (d i)] at eq
        have wi := mul_left_cancel₀ di eq
        have gi := Hidden.carrier_zero_on_active dt hg di
        rw [wi,gi,refl (c i),add_zero]
        change Q.eval (y i)-Q.eval (y i)=0
        exact sub_self _
  · intro i hi
    obtain ⟨_, yi, bi, _, wi⟩ := contrast i hi
    have gi : g i = 0 := (mul_eq_zero.mp
      (Hidden.carrier_mirror_weight_zero F.lastClock hg i)).resolve_left (mul_ne_zero yi bi)
    change q.eval (c i)-(w i+g i)=q.eval (c i)
    rw [wi,gi,add_zero,sub_zero]
  · intro i hi
    exact (refl (c i)).symm ▸ (contrast i hi).2.2.2.1
  · intro R rd i hi
    have feed : weightedEval c θ R = evalNodes A (R*q)-z*evalNodes A R := by
      ext j
      simp only [θ,weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.mul_apply,eval_mul]
      ring
    have work : z*evalNodes A R ∈ zeroSpace A 6 :=
      zeroSpace_mul_treeSpace ho (by decide : 2+1≤16) z4 (evalNodes_mem_treeSpace A R rd)
    have zm := f7 _ (mat_zeroSpace_charZero A 6 work) i hi
    have fact := f7 _ (primitive_defect A (R*q) (natDegree_mul_le_of_le rd qd)) i hi
    change mat A (evalNodes A (R*q)) i-(primitive (R*q)).eval (c i)=0 at fact
    rw [feed,map_sub,Pi.sub_apply,zm,sub_zero,sub_eq_zero.mp fact]

/-- Physical prefix, allowing the one possible off-contrast origin
term. The true terminal is never a predecessor. -/
theorem Width24RankThreeWeakMask.forward_prefix
    (W : Width24RankThreeWeakMask A b q Q P θ)
    (ha : ∀ i j, i ≤ j → A i j = 0) (R : K[X]) (rd : R.natDegree ≤ 2)
    (killOrigin : R.eval 0 = 0 ∨ q.eval 0 = 0)
    {i : Fin 24} (vi : i ∈ weakFiveRows A b Q P)
    (pre : ∀ j < i, j ∈ weakFiveRows A b Q P → R.eval (nodes A j) = 0) :
    (primitive (R*q)).eval (nodes A i) = 0 := by
  classical
  have z : mat A (weightedEval (nodes A) θ R) i = 0 := by
    apply causal_mat ha
    intro j ji
    by_cases vj : j ∈ weakFiveRows A b Q P
    · simp only [weightedEval_apply,pre j ji vj,zero_mul]
    · by_cases j0 : j = 0
      · subst j
        have c0 : nodes A (0 : Fin 24) = 0 := by
          change (∑ j, A 0 j * (1 : K)) = 0
          exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j),zero_mul]
        rw [weightedEval_apply,c0,W.originValue]
        rcases killOrigin with e | e
        · rw [e,zero_mul]
        · rw [e,mul_zero]
      · have jt : j ≠ Fin.last 23 :=
          fun eq => not_lt_of_ge (Fin.le_last i) (eq ▸ ji)
        rw [weightedEval_apply,W.outside j vj j0 jt,mul_zero]
  exact (W.paid R rd i vi).symm.trans z

/-- The rank-three weak strip excludes a reflected endpoint root
of the true fitting polynomial, without a simple-clock assumption. -/
theorem Width24OrdinaryWeakHead.reflected_origin_live_of_carrier_three
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (rankThree : finrank K (width24WeakFiveCarrier A b) = 3) :
    Q.eval 1 ≠ 0 := by
  classical
  intro endpoint
  obtain ⟨q,θ,W⟩ := L.rank_three_forward_mask ha ho rankThree
  have q0 : q.eval 0 = 0 := by rw [W.reflected, sub_zero, endpoint]
  let V := weakFiveRows A b Q P
  let c := nodes A
  have many := reverse_contrast_many ho Q P L.qNonzero
    (by have := L.qDegree; omega) (by have := L.qDegree; have := L.pDegree; omega)
  have nonempty : V.Nonempty := by
    obtain ⟨k,hk,_⟩ := many 0
    exact ⟨k,(mem_weakFiveRows k).mpr hk⟩
  let i := V.min' nonempty
  have vi : i ∈ V := V.min'_mem nonempty
  let N := V.filter (fun k => c k ≠ c i)
  have next : N.Nonempty := by
    obtain ⟨k,hk,apart⟩ := many (reflectedClock A i)
    refine ⟨k,Finset.mem_filter.mpr ⟨(mem_weakFiveRows k).mpr hk,?_⟩⟩
    intro e
    apply apart
    change 1-c k = 1-c i
    rw [e]
  let j := N.min' next
  obtain ⟨vj,apart⟩ := Finset.mem_filter.mp (N.min'_mem next)
  have live (k : Fin 24) (vk : k ∈ V) : c k ≠ 0 :=
    fun e => W.active k vk (by change q.eval (c k) = 0; rw [e]; exact q0)
  have qn : q ≠ 0 := fun e => W.active i vi (by rw [e,eval_zero])
  have dvd : (X : K[X]) ∣ q := by rw [X_dvd_iff,coeff_zero_eq_eval_zero,q0]
  obtain ⟨J,factor⟩ := dvd
  have Jn : J ≠ 0 := fun e => qn (by rw [factor,e,mul_zero])
  have Jd : J.natDegree ≤ 3 := by
    have deg := W.degree
    rw [factor,natDegree_X_mul Jn] at deg
    omega
  apply Jn (RKCert.EndpointPhysical.cubic_eq_zero_of_primitives Jd
    (live i vi) (live j vj) apart ⟨?_,?_⟩)
  · intro R rd
    rw [formalPrimitive_eq_native,← factor]
    apply W.forward_prefix ha R rd (Or.inr q0) vi
    intro k ki vk
    exact False.elim ((not_le_of_gt ki) (V.min'_le k vk))
  · intro R rd
    let T := R*(X-C (c i))
    have td : T.natDegree ≤ 2 := by
      have d := natDegree_mul_le (p:=R) (q:=X - C (c i))
      rw [natDegree_X_sub_C] at d
      change (R * (X - C (c i))).natDegree ≤ 2
      omega
    have pv := W.forward_prefix ha T td (Or.inr q0) vj (by
      intro k kj vk
      have same : c k = c i := by
        by_contra ne
        exact (not_le_of_gt kj) (N.min'_le k (Finset.mem_filter.mpr ⟨vk,ne⟩))
      simp [T,c,same])
    rw [formalPrimitive_eq_native,show R*(X*(X-C (c i))*J) = T*q by
      dsimp [T]
      rw [factor]
      ring]
    exact pv

end
end RKResearch.Certified.ERK16

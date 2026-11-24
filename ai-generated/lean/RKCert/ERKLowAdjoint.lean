module

public import RKCert.ERKOrderEightLobatto

@[expose] public section

/-! # Unreflected adjoint rows and their precise late-column budget -/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p : ℕ}

/-- The weak primitive relation (b^T C^k A-b^T(1-C^{k+1})/(k+1)). -/
def orderAdjoint (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ) : Vec K s :=
  transMat A (fun i => b i*nodes A i^k) -
    (((k+1:ℕ):K)⁻¹ : K) • (fun i => b i*(1-nodes A i^(k+1)))

theorem orderAdjoint_pair (A : Fin s → Fin s → K) (b v : Vec K s) (k : ℕ) :
    row (orderAdjoint A b k) v = probe A b k (mat A v) -
      ((k+1:ℕ):K)⁻¹*(probe A b 0 v-probe A b (k+1) v) := by
  rw [orderAdjoint,row_sub_col,row_smul_col,row_flip_mat]
  have h :
      row (fun i => b i*(1-nodes A i^(k+1))) v = probe A b 0 v-probe A b (k+1) v := by
    simp only [row_apply,probe,←Finset.sum_sub_distrib,pow_zero,mul_one]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  rfl

theorem orderAdjoint_annih {A : Fin s → Fin s → K} {b : Vec K s} {k j : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hpay : j+k+2≤p) :
    orderAdjoint A b k ∈ annih (treeSpace A j) := by
  apply annih_of_norm ho (by omega)
  intro t ht
  have h1 := probe_mat_norm_inv ho t k (by omega)
  have h0 := probe_norm_inv ho t 0 (by omega)
  have h2 := probe_norm_inv ho t (k+1) (by omega)
  have hm := cast_ne_zero_of_budget ho t.order_pos (by omega)
  have hk := cast_ne_zero_of_budget ho (n:=k+1) (by omega) (by omega)
  have hn : ((t.order:K)+(k:K)+1)≠0 := by
    rw [←Nat.cast_one,←Nat.cast_add,←Nat.cast_add]
    exact cast_ne_zero_of_budget ho (by omega) (by omega)
  let d : K := t.order
  let r : K := (k:K)+1
  have hd : d≠0 := hm
  have hr : r≠0 := by simpa [r] using hk
  have hdr : d+r≠0 := by simpa [d,r,add_assoc] using hn
  have h : (d+r)⁻¹/d - r⁻¹*(d⁻¹-(d+r)⁻¹)=0 := by
    field_simp [hd,hr,hdr]
    ring
  rw [orderAdjoint_pair,h1,h0,h2,add_right_comm (t.order:K) (1:K) (k:K)]
  simpa only [d,r,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero,add_assoc] using h

/-- When D(1) holds, the kth residual has exactly the signed prefix
column expression used in the low-order endpoint geometry. -/
theorem orderAdjoint_of_D1 {A : Fin s → Fin s → K} {b : Vec K s}
    (hD : backSeed1 A b=0) (k : ℕ) :
    orderAdjoint A b k =
      -transMat A (fun i => b i*(1-nodes A i^k)) +
        (fun i => b i*((1-nodes A i)-
          (1-nodes A i^(k+1))/((k+1:ℕ):K))) := by
  have hB : transMat A b = diag (mirror A) b := sub_eq_zero.mp hD
  have hA : (fun i => b i*nodes A i^k) = b-(fun i => b i*(1-nodes A i^k)) := by
    ext i
    simp only [Pi.sub_apply]
    ring
  rw [orderAdjoint,hA,map_sub,hB]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
    diag_apply,mirror,Pi.one_apply,div_eq_mul_inv]
  ring

theorem orderAdjoint_zero_eq_D1 (A : Fin s → Fin s → K) (b : Vec K s) :
    orderAdjoint A b 0=backSeed1 A b := by
  rw [orderAdjoint,backSeed1]
  simp only [pow_zero,mul_one,zero_add,pow_one,Nat.cast_one,inv_one,one_smul]
  congr 1
  ext i
  simp [mirror,mul_comm]

theorem orderAdjoint_one_eq_backward_two {A : Fin s → Fin s → K} {b : Vec K s}
    (hD : backSeed1 A b=0) (h2 : (2:K)≠0) :
    orderAdjoint A b 1=-((2:K)⁻¹ : K) • backSeed2 A b := by
  have hA : (fun i => b i*(1-nodes A i^1)) = diag (mirror A) b := by
    ext i; simp [mirror,mul_comm]
  rw [orderAdjoint_of_D1 hD,hA,backSeed2]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
    diag_apply,mirror,Pi.one_apply,Nat.reduceAdd,Nat.cast_ofNat,div_eq_mul_inv]
  field_simp
  ring

end RKCert.Paired


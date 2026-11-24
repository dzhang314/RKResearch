module

public import RKCert.StagePrimitives
public import RKCert.UniformERK

@[expose] public section

/-! # Turning the grade-five excess into a numerical lower bound -/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- One extra forward rank at grade five propagates to the even midpoint
and adds one stage to the uniform paired lower count. -/
theorem stage_surplus_of_five_rank {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (h5 : 5≤finrank K (zeroSpace A 5)) :
    (3*p+1)/2-1 ≤ s := by
  have hs := explicit_order_le_stages ha ho
  let q := p/2
  have hq : 5≤q := by dsimp [q]; omega
  have hsep : Separated A q := explicit_separated ha ho (by dsimp [q]; omega) (by omega)
  have grow (n : ℕ) (hn : n+5≤q) : n+5≤finrank K (zeroSpace A (n+5)) := by
    induction n with
    | zero => simpa using h5
    | succ n ih =>
      have he : n+1+5 = n+5+1 := by omega
      rw [he] at hn ⊢
      have hr := Submodule.finrank_lt_finrank_of_lt
        (zeroSpace_strict_of_separated ha hsep (j:=n+5) (by omega) hn)
      have hn' := ih (by omega)
      omega
  have fq : q≤finrank K (zeroSpace A q) := by
    have he : (q-5)+5=q := by omega
    have aux : (fun k : ℕ => k≤finrank K (zeroSpace A k)) ((q-5)+5) := grow (q-5) (by omega)
    exact he ▸ aux
  have fr := explicit_treeSpace_rank ha ho (q:=q) (by dsimp [q]; omega) (by omega)
  by_cases hpar : p%2=0
  · have h := backward_count ha ho q (q-2) (by dsimp [q]; omega)
    dsimp [q] at *
    omega
  · have h := backward_endpoint_count ha ho q (q-1) (by dsimp [q]; omega) (by dsimp [q]; omega)
    dsimp [q] at *
    omega

end RKCert.Paired

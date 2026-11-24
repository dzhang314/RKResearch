module
public import RKCert.DirkLocalProjection
@[expose] public section
namespace RKCert.Paired.LocalProjection
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

/-- Comparing two commutators only needs the one-step leakage space,
its clock image and its next primitive image. The identity is a linear
calculation valid for any projections that intertwine the clock. -/
theorem commutator_leak {N D Q N' : Vec K s→ₗ[K]Vec K s} {Z0 Z : Submodule K (Vec K s)}
    (comm:∀z,Q (D z)=D (Q z)) (leak:∀z,N' (Q z)-Q (N z)∈Z0)
    (incl:Z0≤Z) (hD:∀z∈Z0,D z∈Z) (hN:∀z∈Z0,N' z∈Z) (x:Vec K s) :
    commutatorR N' D (Q x)-Q (commutatorR N D x) ∈Z := by
  let e:=fun z=>N' (Q z)-Q (N z)
  have eq:commutatorR N' D (Q x)-Q (commutatorR N D x) =
      D (e x)-e (D x)-N' (e x)-e (N x) := by
    change D (N' (Q x))-N' (D (Q x))-N' (N' (Q x)) -
       Q (D (N x)-N (D x)-N (N x))=_
    dsimp only [e]
    rw [map_sub,map_sub,map_sub,map_sub,comm,comm]
    abel
  rw [eq]
  exact Z.sub_mem (Z.sub_mem (Z.sub_mem (hD _ (leak x)) (incl (leak (D x))))
    (hN _ (leak x))) (incl (leak (N x)))

theorem map_primitive_closed {A:Fin s→Fin s→K} {b:Vec K s} {d:Vec K s} (h:Fin s)
    (dh: d∈dirkBack A b 1) {r:ℕ} (hr:1≤r) :
    ∀x∈(dirkBack A b r).map (kill d h),
    (kill d h).comp (transMat A) x∈(dirkBack A b (r+1)).map (kill d h) := by
  rintro _ ⟨z,hz,rfl⟩
  have hN (k:ℕ) : (dirkBack A b k).map (transMat A)≤dirkBack A b (k+1) :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hd':d∈dirkBack A b r := twoOrbit_mono _ _ _ _ _ hr dh
  have H : (kill d h).comp (transMat A) (kill d h z)-kill d h (transMat A z)
      ∈(dirkBack A b (r+1)).map (kill d h) := by
    rw [primitive_leak]
    exact Submodule.smul_mem _ _ ⟨_,hN r ⟨_,hd',rfl⟩,rfl⟩
  simpa only [sub_add_cancel] using
    ((dirkBack A b (r+1)).map (kill d h)).add_mem H ⟨_,hN r ⟨_,hz,rfl⟩,rfl⟩

theorem local_leak_bound {A:Fin s→Fin s→K} {b:Vec K s} {d:Vec K s} (h:Fin s)
    (dh:d∈dirkBack A b 1) (x:Vec K s) :
    (kill d h).comp (transMat A) (kill d h x)-kill d h (transMat A x)∈
      (dirkBack A b 2).map (kill d h) := by
  rw [primitive_leak]
  have inc:(dirkBack A b 1).map (transMat A)≤dirkBack A b 2 :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  exact Submodule.smul_mem _ _ ⟨_,inc ⟨_,dh,rfl⟩,rfl⟩

theorem local_commutator_bound {A:Fin s→Fin s→K} {b:Vec K s} {d:Vec K s} (h:Fin s)
    (dh:d∈dirkBack A b 1) (loc:∀i,d i≠0→mirror A i=mirror A h) (x:Vec K s) :
    commutatorR ((kill d h).comp (transMat A)) (diag (mirror A)) (kill d h x)-
      kill d h (commutatorR (transMat A) (diag (mirror A)) x)∈(dirkBack A b 3).map (kill d h) := by
  apply commutator_leak (kill_clock _ _ _ loc) (local_leak_bound h dh)
    (Submodule.map_mono (twoOrbit_le_succ _ _ _ _ _ 2)) _ (map_primitive_closed h dh (by decide))
  rintro _ ⟨z,hz,rfl⟩
  rw [← kill_clock _ _ _ loc]
  have inc:(dirkBack A b 2).map (diag (mirror A))≤dirkBack A b 3 :=
    le_sup_right.trans le_sup_left
  exact ⟨_,inc ⟨_,hz,rfl⟩,rfl⟩

end
end RKCert.Paired.LocalProjection

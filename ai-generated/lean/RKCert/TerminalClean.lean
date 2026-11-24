module
public import RKCert.HeadChart
public import RKCert.GradedProducts
@[expose] public section
namespace RKCert.Paired.Terminal
variable {K : Type*} [Field K] {s p j m : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- Exact-order multiplication of a genuine stage cardinal by lower defect
columns puts their terminal coordinate in the scalar probe's kernel. -/
theorem cardinal_clean_lower (ho : HasTreeOrderAtLeast A b p) (hpay : j+m+1≤p)
    (t:Fin s) (wt:b t≠0) (card:Pi.single t (1:K)∈treeSpace A m) :
    ∀ f∈zeroSpace A j, f t=0 := by
  classical
  intro f hf
  have ph:=zeroSpace_mul_treeSpace ho (by omega) hf card
  have h : probe A b 0 (f*Pi.single t (1:K))=0 := probe_zeroSpace ho (by omega) ph
  have hh : b t * f t=0 := by
    simpa [probe,row,dotProduct,Pi.single_apply,mul_ite] using h
  exact (mul_eq_zero.mp hh).resolve_left wt

/-- A genuine unit clock escape propagates the zero at the same physical
coordinate one grade further, without assuming the next defect space is
itself orthogonal to the cardinal. -/
theorem clean_next_of_escape (i:Fin s) (clean:∀f∈zeroSpace A j,f i=0)
    (one : Module.finrank K (zeroSpace A (j+1))≤Module.finrank K (zeroSpace A j)+1)
    (out : ¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j) :
    ∀ f∈zeroSpace A (j+1),f i=0 := by
  intro f h
  rw [Clock.ordinary_step one out] at h
  obtain ⟨u,hu,_,⟨v,hv,rfl⟩,rfl⟩ := Submodule.mem_sup.mp h
  simp [diag_apply,clean _ hu,clean _ hv]

end RKCert.Paired.Terminal

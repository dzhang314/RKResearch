module

public import RKCert.DirkRanks

@[expose] public section
namespace RKCert.Paired
variable {K : Type*} [Field K] {s p m : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- A polynomial vanishing at the origin cannot reproduce a nonzero common
endpoint mass under all the available probes. Subtracting the zeroth row
reduces the endpoint-weighted test to an ordinary shifted Cauchy system. -/
theorem constant_moments_origin_zero (ho : HasTreeOrderAtLeast A b p) (hp : 2*m+1≤p)
    (a : Fin (m+1) → K) (ha : a 0=0) (B : K)
    (he : ∀ k : Fin (m+1), probe A b k.val (polyEval A m a) = B) : B=0 := by
  have mom (k : Fin (m+1)) :
      (∑ j : Fin m, a j.succ / ((k.val+j.val+2:ℕ):K))=B := by
    have h := he k
    rw [probe_polyEval ho (by omega), Fin.sum_univ_succ, ha, zero_div, zero_add] at h
    simpa only [Fin.val_succ, Nat.add_assoc] using h
  let w : Fin m → K := fun j => a j.succ / ((j.val+2:ℕ):K)
  have hn (n : ℕ) (hl : 0<n) (hu : n≤p) : (n:K) ≠ 0 := cast_ne_zero_of_budget ho hl hu
  have ker (i : Fin m) : (∑ j : Fin m, w j / ((i.val+j.val+3:ℕ):K))=0 := by
    have hx : ((i.val+1:ℕ):K) ≠ 0 := hn _ (by omega) (by omega)
    apply mul_left_cancel₀ hx
    rw [mul_zero]
    rw [Finset.mul_sum]
    have term (j : Fin m) :
        ((i.val+1:ℕ):K) * (w j / ((i.val+j.val+3:ℕ):K)) =
        a j.succ / ((j.val+2:ℕ):K) - a j.succ / ((i.val+j.val+3:ℕ):K) := by
      have h₁ := hn (j.val+2) (by omega) (by omega)
      have h₂ := hn (i.val+j.val+3) (by omega) (by omega)
      dsimp [w]; field_simp; push_cast; ring
    rw [Finset.sum_congr rfl (fun j _ => term j), Finset.sum_sub_distrib]
    have h₀ := mom (0:Fin (m+1))
    have h₁ := mom i.succ
    have h₁' : (∑ j : Fin m, a j.succ / ((i.val+j.val+3:ℕ):K))=B := by
      convert h₁ using 2 with j
      congr 2
      simp only [Fin.val_succ]
      omega
    simpa using (show (∑ j : Fin m, a j.succ / ((j.val+2:ℕ):K)) -
        (∑ j : Fin m, a j.succ / ((i.val+j.val+3:ℕ):K))=0 by
      rw [h₁', show (∑ j : Fin m, a j.succ / ((j.val+2:ℕ):K)) = B by simpa using h₀, sub_self])
  have hz := moments_detect ho (d:=3) (by decide) (by omega) (fun i j => by omega) w ker
  have mm := mom (0:Fin (m+1))
  change (∑ j : Fin m, a j.succ / ((0+j.val+2:ℕ):K)) = B at mm
  simp only [zero_add] at mm
  change (∑ j : Fin m, w j) = B at mm
  simpa [hz] using mm.symm

/-- Under the boundary conditions, a single terminal stage vector cannot be
in a polynomial-plus-defect space. The two endpoints and every moment are
used, without assuming the weights are positive. -/
theorem terminal_not_decomposable {s : ℕ} {A : Fin (s+1) → Fin (s+1) → K}
    {b : Vec K (s+1)} (ho : HasTreeOrderAtLeast A b p) (hp : 2*m+1≤p)
    (h0 : ∀ j, A 0 j=0) (i : Fin (s+1)) (hi : nodes A i=1) (hbi : b i≠0)
    (a : Fin (m+1) → K) (f : Vec K (s+1)) (hf : f ∈ zeroSpace A m) :
    Pi.single i (1:K) ≠ polyEval A m a + f := by
  intro h
  have hc0 : nodes A 0=0 := by simp [nodes, h0]
  have hne : (0:Fin (s+1)) ≠ i := by intro hh; rw [← hh,hc0] at hi; exact zero_ne_one hi
  have hnorm (t : Tree) : normTree A t 0 = if t = .leaf then 1 else 0 := by
    cases t with
    | leaf => simp [normTree_leaf]
    | attach t u => simp [normTree, stageWeight, h0]
  have hfirst : zeroSpace A m ≤ LinearMap.ker (LinearMap.proj 0) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,u,hh,_,rfl⟩
    change normTree A t 0 - normTree A u 0 = 0
    rw [hnorm, hnorm, sub_eq_zero]
    have leaf (v : Tree) : v=.leaf ↔ v.order=1 := by
      cases v with
      | leaf => simp [Tree.order]
      | attach t u =>
        have := t.order_pos; have := u.order_pos
        simp only [reduceCtorEq,Tree.order,false_iff]; omega
    simp only [leaf, hh]
  have hf0 : f 0=0 := hfirst hf
  have hp0 : polyEval A m a 0 = a 0 := by
    rw [polyEval_apply, Fin.sum_univ_succ]
    simp [Finset.sum_apply, normTree_bush, hc0]
  have ha : a 0=0 := by
    have hp' := congrFun h 0
    simpa only [Pi.add_apply, Pi.single_eq_of_ne hne, hp0, hf0, add_zero] using hp'.symm
  apply hbi
  apply constant_moments_origin_zero ho hp a ha (b i)
  intro k
  have hm := congrArg (probe A b k.val) h
  rw [map_add, show probe A b k.val f=0 from probe_zeroSpace ho (by omega) hf,add_zero] at hm
  rw [←hm]
  simp [probe, Pi.single_apply, hi]

end RKCert.Paired

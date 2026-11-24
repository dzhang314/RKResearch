import RKCert.ReviewedNative.Explicit

#print axioms RKResearch.Certified.phi_tallTree_eq_zero
#print axioms RKResearch.Certified.explicit_order_le_stages

-- The native theorem still applies to an arbitrary nontrivial semiring and zero stages.
example {R : Type*} [CommSemiring R] [Nontrivial R]
    {A : Matrix (Fin 0) (Fin 0) R} {b : Fin 0 → R} {p : ℕ}
    (h : RKResearch.HasOrder A b p) : p = 0 := by
  have hp := RKResearch.Certified.explicit_order_le_stages
    (fun i _ _ => Fin.elim0 i) h
  omega

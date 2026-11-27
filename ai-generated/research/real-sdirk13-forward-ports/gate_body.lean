
private theorem det3_zero_of_kernel (a b c d e f g h i v u : K)
    (h1 : u*b+v*a+c=0) (h2 : u*e+v*d+f=0) (h3 : u*h+v*g+i=0) :
    det3 a b c d e f g h i = 0 := by
  rw [eq_neg_of_add_eq_zero_right h1, eq_neg_of_add_eq_zero_right h2,
    eq_neg_of_add_eq_zero_right h3]
  unfold det3
  ring

/-- The moment of the five manufactured reflected ladder pins, with
all integral degrees interpreted algebraically in characteristic zero. -/
def raw (g : K) (j : ℕ) : K :=
  1 / (((j+5)+1 : ℕ) : K)
  - (25*g)*(1/(((j+4)+1 : ℕ) : K))
  + (230*g^2)*(1/(((j+3)+1 : ℕ) : K))
  - (950*g^3)*(1/(((j+2)+1 : ℕ) : K))
  + (1689*g^4)*(1/(((j+1)+1 : ℕ) : K))
  - (945*g^5)*(1/(((j+0)+1 : ℕ) : K))

private theorem normalize_raw (g : K) :
    27720*raw g 0 = M0 g ∧ 27720*raw g 1 = M1 g ∧ 27720*raw g 2 = M2 g ∧
    27720*raw g 3 = M3 g ∧ 27720*raw g 4 = M4 g ∧ 27720*raw g 5 = M5 g := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> norm_num [raw,M0,M1,M2,M3,M4,M5] <;> ring

/-- A monic quadratic cannot cancel the ladder hull's first four exact
moments. In particular the required first six moments cannot vanish. -/
theorem no_paid_quadratic (g u v : K)
    (h : ∀ j : ℕ, j ≤ 3 → u*raw g (j+1)+v*raw g j+raw g (j+2)=0) : False := by
  obtain ⟨e0,e1,e2,e3,e4,e5⟩ := normalize_raw g
  have hom (j : ℕ) (hj : j≤3) :
      u*(27720*raw g (j+1))+v*(27720*raw g j)+27720*raw g (j+2)=0 := by
    calc
      _ = 27720*(u*raw g (j+1)+v*raw g j+raw g (j+2)) := by ring
      _ = 0 := by rw [h j hj, mul_zero]
  have z0 := hom 0 (by decide)
  have z1 := hom 1 (by decide)
  have z2 := hom 2 (by decide)
  have z3 := hom 3 (by decide)
  simp only [Nat.reduceAdd,e0,e1,e2,e3,e4,e5] at z0 z1 z2 z3
  exact no_common_zero g (det3_zero_of_kernel _ _ _ _ _ _ _ _ _ v u z0 z1 z2)
    (det3_zero_of_kernel _ _ _ _ _ _ _ _ _ v u z0 z1 z3)

def hull (g z : K) : K := (z-g)*(z-3*g)*(z-5*g)*(z-7*g)*(z-9*g)
def nodes (g a b : K) : Fin 7 → K := ![g,3*g,5*g,7*g,9*g,a,b]

private theorem weightedHull (g a b : K) (w : Fin 7 → K)
    (h : ∀ j : ℕ, j≤12 → (∑ i, w i * (nodes g a b i)^j) = 1/(((j+1 : ℕ)):K))
    (j : ℕ) (hj : j≤5) :
    (∑ i, w i * ((nodes g a b i)^j * hull g (nodes g a b i))) = raw g j := by
  calc
    _ = (∑ i, w i * (nodes g a b i)^(j+5))
        - (25*g)*(∑ i, w i * (nodes g a b i)^(j+4))
        + (230*g^2)*(∑ i, w i * (nodes g a b i)^(j+3))
        - (950*g^3)*(∑ i, w i * (nodes g a b i)^(j+2))
        + (1689*g^4)*(∑ i, w i * (nodes g a b i)^(j+1))
        - (945*g^5)*(∑ i, w i * (nodes g a b i)^(j+0)) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hull,pow_add]
      ring
    _ = _ := by
      unfold raw
      rw [h (j+5) (by omega), h (j+4) (by omega), h (j+3) (by omega),
        h (j+2) (by omega), h (j+1) (by omega), h (j+0) (by omega)]

/-- No seven-occurrence degree-twelve quadrature can place its first five
reflected physical nodes at the odd multiples of a common diagonal.
Weights need not be positive; the theorem does not require any distinctness. -/
theorem no_seven_site_ladder (g a b : K) (w : Fin 7 → K)
    (h : ∀ j : ℕ, j ≤ 12 → (∑ i, w i * (nodes g a b i)^j) = 1/(((j+1 : ℕ)):K)) :
    False := by
  apply no_paid_quadratic g (-(a+b)) (a*b)
  intro j hj
  rw [← weightedHull g a b w h (j+1) (by omega),
    ← weightedHull g a b w h j (by omega),
    ← weightedHull g a b w h (j+2) (by omega)]
  calc
    _ = ∑ i, w i * (nodes g a b i)^j * hull g (nodes g a b i) *
      (nodes g a b i-a) * (nodes g a b i-b) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [pow_add]
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      fin_cases i <;> simp [nodes,hull]

#print axioms no_seven_site_ladder
end RKResearch.Certified.FiveLadderThirteen

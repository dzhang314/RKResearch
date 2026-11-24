module
public import RKCert.ReviewedNative.SDIRKSixFront
public import RKCert.ReviewedNative.SDIRKSixWords
@[expose] public section
namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix
variable {K : Type*} [Field K] {s : ℕ}

/-- Rescale the native tableau so its common diagonal becomes one. -/
def scaleTable (z : K) (A : Matrix (Fin s) (Fin s) K) : Matrix (Fin s) (Fin s) K :=
  fun i j => z*A i j

theorem mat_scaleTable (z : K) (A : Matrix (Fin s) (Fin s) K) (x : Fin s → K) :
    mat (scaleTable z A) x=z • mat A x :=
  Matrix.smul_mulVec z A x

theorem nodes_scaleTable (z : K) (A : Matrix (Fin s) (Fin s) K) :
    nodes (scaleTable z A)=z • nodes A :=
  mat_scaleTable z A 1

theorem diag_scale (z:K) (x v:(Fin s → K)) : diag (z•x) v=z•diag x v := by
  ext i;simp only [diag_apply,Pi.smul_apply,smul_eq_mul];ring
theorem seed_scaleTable (z : K) (A : Matrix (Fin s) (Fin s) K) :
    seed (scaleTable z A)=z^2 • seed A := by
  simp only [seed,nodes_scaleTable,mat_scaleTable,diag_scale,map_smul,smul_smul]
  ext i;simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul];ring
theorem volterra_scaleTable (z : K) (A : Matrix (Fin s) (Fin s) K) (x : (Fin s → K)) :
    volterra (scaleTable z A) x=z^2 • volterra A x := by
  change diag (nodes _) (mat _ x)-mat _ (diag (nodes _) x)-mat _ (mat _ x)=
    z^2 • (diag (nodes A) (mat A x)-mat A (diag (nodes A) x)-mat A (mat A x))
  simp only [nodes_scaleTable,mat_scaleTable,diag_scale,map_smul,smul_smul]
  ext i;simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul];ring
theorem tap_scaleTable (z γ : K) (A : Matrix (Fin s) (Fin s) K) (h : z*γ=1) (x : (Fin s → K)) :
    tapMap (scaleTable z A) 1 x=z • tapMap A γ x := by
  change mat (scaleTable z A) x-(1:K) • x=z • (mat A x-γ • x)
  rw [mat_scaleTable,smul_sub,smul_smul,h]

def kap (u : K) := 1+2*u-u^2
def leg (z x : K) := 20*x^3-30*z*x^2+12*z^2*x-z^3
theorem leg_scale (A : Matrix (Fin s) (Fin s) K) (z:K) (i : Fin s) :
    leg z (nodes (scaleTable z A) i) = z^3*leg3c A i := by
  rw [leg3c_at,nodes_scaleTable];change leg z (z*nodes A i)=_;unfold leg;ring

structure Front (B : Matrix (Fin 6) (Fin 6) K) (z : K) : Prop where
  tri : B.IsLowerTriangular
  single : ∀ i, B i i=1
  tap_ne : B 1 0≠0
  comm : mat B (volterra B 1)=volterra B (mat B 1)
  clock : ∀ i, (nodes B i-1)*seed B i = kap (B 1 0)*tapMap B 1 (seed B) i
  profile : ∀ i, B 1 0*leg z (nodes B i) =
    B 1 0*leg z 1*seed B i +
      (leg z (1+B 1 0)-kap (B 1 0)*leg z 1)*tapMap B 1 (seed B) i

theorem normal_front [CharZero K] {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) : Front (scaleTable γ⁻¹ A) γ⁻¹ := by
  let z := γ⁻¹
  let B := scaleTable z A
  change Front B z
  have hz : z*γ=1 := inv_mul_cancel₀ hγ
  have hl : B.IsLowerTriangular := by intro i j hij;change z*A i j=0;rw [@ha i j hij,mul_zero]
  have hd (i) : B i i=1 := by change z*A i i=1;rw [he,hz]
  have ht := first_tap_nonzero ho ha he hγ
  have h₀ : nodes B 0=1 := by rw [node_mat_one,at0 hl hd];simp
  have h₁ : nodes B 1=1+B 1 0 := by rw [node_mat_one,at1 hl hd];simp [add_comm]
  have hs : kap (B 1 0)=z^2*seed A 1 := by
    rw [seed1 ha he];change 1+2*(γ⁻¹*A 1 0)-(γ⁻¹*A 1 0)^2=_
    dsimp [z];field_simp
  have hq (i) : tapMap B 1 (seed B) i=z^3*tapMap A γ (seed A) i := by
    simp only [B,seed_scaleTable,map_smul,tap_scaleTable z γ A hz,Pi.smul_apply,smul_eq_mul];ring
  refine ⟨hl,hd,mul_ne_zero (inv_ne_zero hγ) ht,?_,?_,?_⟩
  · simp only [B,volterra_scaleTable,mat_scaleTable,map_smul,front_commutator ho ha he hγ,smul_smul]
    rw [mul_comm z (z^2)]
  · intro i
    have h := congrFun (front_clock_seed ho ha he hγ) i
    change γ^2*(nodes A i*seed A i-γ*seed A i)=seed A 1*tapMap A γ (seed A) i at h
    rw [hs,hq]
    simp only [B,nodes_scaleTable,seed_scaleTable,Pi.smul_apply,smul_eq_mul]
    dsimp [z];field_simp;linear_combination h
  · intro i
    have h := congrFun (cubic_reconstruction ho ha he hγ (leg3c A) (leg3c_silent ho)) i
    change leg3c A i=(leg3c A 0/γ^2)*seed A i+
      ((leg3c A 1-(leg3c A 0/γ^2)*seed A 1)/(A 1 0*γ^2))*tapMap A γ (seed A) i at h
    rw [hs,hq,← h₁,← h₀]
    simp only [B,leg_scale,seed_scaleTable,scaleTable,Pi.smul_apply,smul_eq_mul]
    dsimp [z];field_simp at h ⊢;linear_combination h

theorem Φ_scale (z:K) (A : Matrix (Fin s) (Fin s) K) (t : FiniteRootedTree) :
    Φ t (scaleTable z A)=z^((t.order:ℕ)-1) • Φ t A := by
  induction t with
  | leaf => ext i;simp [order]
  | butcherProduct r t hr ht =>
    ext i
    change Φ r (scaleTable z A) i * mat (scaleTable z A) (Φ t (scaleTable z A)) i =
      z^(((r.order:ℕ)+(t.order:ℕ))-1) * (Φ r A i * mat A (Φ t A) i)
    have he : (r.order:ℕ)+(t.order:ℕ)-1=1+((r.order:ℕ)-1)+((t.order:ℕ)-1) := by
      have := t.order.pos; have := r.order.pos; omega
    rw [ht,hr,mat_scaleTable,map_smul,he,pow_add,pow_add,pow_one]
    simp only [Pi.smul_apply,smul_eq_mul];ring

theorem scale_treeSpace (z:K) (hz:z≠0) (A : Matrix (Fin s) (Fin s) K) (j:ℕ) :
    treeSpace (scaleTable z A) j=treeSpace A j := by
  apply le_antisymm
  · apply Submodule.span_le.mpr;rintro _ ⟨t,ht,rfl⟩
    rw [Φ_scale];exact (treeSpace A j).smul_mem _ (Φ_mem_treeSpace A _ ht)
  · apply Submodule.span_le.mpr;rintro _ ⟨t,ht,rfl⟩
    change Φ t A ∈ treeSpace (scaleTable z A) j
    have h := Φ_mem_treeSpace (scaleTable z A) t ht
    rw [Φ_scale] at h
    simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hz),one_smul] using
      (treeSpace (scaleTable z A) j).smul_mem ((z^((t.order:ℕ)-1))⁻¹) h

theorem at2 {A : Matrix (Fin 6) (Fin 6) K} {γ : K} (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : (Fin 6 → K)) :
    mat A x 2 = A 2 0*x 0+A 2 1*x 1+γ*x 2 := by
  have h3:=@ha (2:Fin 6) 3 (by decide);have h4:=@ha (2:Fin 6) 4 (by decide);have h5:=@ha (2:Fin 6) 5 (by decide)
  change (∑ j : Fin 6, A 2 j * x j) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change _+(A 2 1*x 1+(A 2 2*x 2+(A 2 3*x 3+(A 2 4*x 4+(A 2 5*x 5+0)))))=_
  rw [he,h3,h4,h5];simp;ring

theorem nodes_detect {A : Matrix (Fin s) (Fin s) K} {a : ℕ} (ht : treeSpace A a=⊤)
    {i j : Fin s} (h : ∀ t:FiniteRootedTree,Φ t A i=Φ t A j) : i=j := by
  by_contra hn
  let dd := (LinearMap.proj i : (Fin s → K)→ₗ[K] K)-LinearMap.proj j
  have hl : treeSpace A a≤LinearMap.ker dd := by
    apply Submodule.span_le.mpr;rintro _ ⟨t,_,rfl⟩
    exact sub_eq_zero.mpr (h t)
  rw [ht] at hl
  have hx : (Pi.single i 1 : (Fin s → K))∈LinearMap.ker dd := hl trivial
  change ((Pi.single i 1 : (Fin s → K)) i)-((Pi.single i 1 : (Fin s → K)) j)=0 at hx
  simp [Ne.symm hn] at hx

def w3 (B : Matrix (Fin 6) (Fin 6) K) : K := B 2 0+B 2 1

theorem zero_tap_distinct {B : Matrix (Fin 6) (Fin 6) K} {z : K} (hf : Front B z)
    (ht : treeSpace B 4=⊤) (hr : B 2 1=0) : w3 B≠0 ∧ w3 B≠B 1 0 := by
  have ha:=hf.tri;have he:=hf.single
  have hrow (x : (Fin 6 → K)) : mat B x 2=w3 B*x 0+x 2 := by rw [at2 ha he];unfold w3;rw [hr];ring
  constructor
  · intro hw
    have h (t:FiniteRootedTree) : Φ t B 2=Φ t B 0 := by
      induction t with
      | leaf => rfl
      | butcherProduct r t hr ht =>
        change Φ r B 2*mat B (Φ t B) 2=Φ r B 0*mat B (Φ t B) 0
        rw [hrow,hw,at0 ha he,zero_mul,zero_add,one_mul,ht,hr]
    exact (by decide : (2:Fin 6)≠0) (nodes_detect ht h)
  · intro hw
    have h (t:FiniteRootedTree) : Φ t B 2=Φ t B 1 := by
      induction t with
      | leaf => rfl
      | butcherProduct r t hr ht =>
        change Φ r B 2*mat B (Φ t B) 2=Φ r B 1*mat B (Φ t B) 1
        rw [hrow,hw,at1 ha he,one_mul,ht,hr]
    exact (by decide : (2:Fin 6)≠1) (nodes_detect ht h)

structure Third (z u w r:K) : Prop where
  comm : r*u*(2*u-w)=0
  clock : w*(kap w+2*r*u)=kap u*(w+r*(kap u-1))
  leg3 : u*leg z (1+w)=u*leg z 1*(kap w+2*r*u)+
    (leg z (1+u)-kap u*leg z 1)*(w+r*(kap u-1))

theorem third_data {B : Matrix (Fin 6) (Fin 6) K} {z : K} (hf : Front B z) :
    Third z (B 1 0) (w3 B) (B 2 1) := by
  have ha:=hf.tri;have hd:=hf.single
  have n0 : nodes B 0=1 := by rw [node_mat_one,at0 ha hd];simp
  have n1 : nodes B 1=1+B 1 0 := by rw [node_mat_one,at1 ha hd];simp [add_comm]
  have n2 : nodes B 2=1+w3 B := by rw [node_mat_one,at2 ha hd];simp [w3];ring
  have g0 : seed B 0=1 := by rw [seed0 ha hd];simp
  have g1 : seed B 1=kap (B 1 0) := by rw [seed1 ha hd];unfold kap;ring
  have g2 : seed B 2=kap (w3 B)+2*B 2 1*B 1 0 := by
    change 2*mat B (nodes B) 2-nodes B 2*nodes B 2=_
    rw [at2 ha hd,n0,n1,n2];unfold w3 kap;ring
  have q2 : tapMap B 1 (seed B) 2=w3 B+B 2 1*(kap (B 1 0)-1) := by
    change mat B (seed B) 2-1*seed B 2=_
    rw [at2 ha hd,g0,g1];unfold w3;ring
  refine ⟨?_,?_,?_⟩
  · have h:=congrFun hf.comm 2
    change mat B (volterra B 1) 2 =
      nodes B 2 * mat B (mat B 1) 2 - mat B (diag (nodes B) (mat B 1)) 2 -
        mat B (mat B (mat B 1)) 2 at h
    rw [comm_one,map_neg] at h
    simp only [Pi.neg_apply,at2 ha hd,at1 ha hd,at0 ha hd,Pi.one_apply,diag_apply,n0,n1,n2,g0,g1,g2] at h
    unfold w3 kap at *
    linear_combination h
  · have h:=hf.clock 2;rw [n2,g2,q2] at h;linear_combination h
  · simpa only [n2,g2,q2] using hf.profile 2

end RKResearch.Certified.Graded.SDIRKSix



module
public import RKCert.SDIRK6Normal
@[expose] public section
namespace RKCert.Paired.SDIRK.P6
open RKCert.Paired RKCert.Paired.SDIRK
variable {K : Type*} [Field K] {s : ℕ}

/-- A stage vector physically vanishes on the first k coordinates. -/
def clears (k:ℕ) (x : Vec K s) : Prop := ∀ i:Fin s,i.val<k→x i=0

theorem tap_advances {B : Fin s→Fin s→K} (hb:lower B) (hd:∀i,B i i=1)
    {k:ℕ} {x:Vec K s} (hx:clears k x) : clears (k+1) (tapMap B 1 x) := by
  intro i hi
  have hm : mat B x i=B i i*x i := by
    change (∑ j : Fin s,B i j*x j)=_
    apply Finset.sum_eq_single i
    · intro j _ hji
      by_cases hj : j.val < i.val
      · rw [hx j (by omega),mul_zero]
      · have hij : i.val<j.val := by
          have hne : j.val≠i.val := fun h=>hji (Fin.ext h)
          omega
        rw [hb i j hij,zero_mul]
    · simp
  change mat B x i-1*x i=0
  rw [hm,hd,sub_self]

theorem clear_all {x : Vec K s} (hx:clears s x) : x=0 := by
  ext i;exact hx i i.isLt

theorem eval_N (A : Fin s→Fin s→K) (z:K) (x:Vec K s) :
    Op.eval A (Op.N z) x=tapMap (scaleTable z A) 1 x := by
  change z • mat A x-x=mat (scaleTable z A) x-(1:K) • x
  rw [mat_scaleTable,one_smul]

theorem eval_X_at (A : Fin s→Fin s→K) (z:K) (x:Vec K s) (i:Fin s) :
    Op.eval A (Op.X z) x i=nodes (scaleTable z A) i*x i := by
  rw [nodes_scaleTable];change z*(nodes A i*x i)=(z*nodes A i)*x i;ring

theorem eval_Q_at (A : Fin s→Fin s→K) (z u:K) (i:Fin s) :
    Op.eval A (Op.Q z u) 1 i=(nodes (scaleTable z A) i-1)*(nodes (scaleTable z A) i-1-u) := by
  change Op.eval A (Op.X z) (Op.eval A (Op.X z) 1-(1+u) • (1:Vec K s)) i-
    (Op.eval A (Op.X z) 1-(1+u) • (1:Vec K s)) i=_
  simp only [eval_X_at,Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul];ring

theorem eval_reflect_at (A : Fin s→Fin s→K) (z v:K) (x:Vec K s) (i:Fin s) :
    Op.eval A (.mul (.sub (Op.Y z) .ident) (.sub (Op.Y z) (.scale (1+v) .ident))) x i=
    (z-nodes (scaleTable z A) i-1)*(z-nodes (scaleTable z A) i-1-v)*x i := by
  rw [nodes_scaleTable]
  change z*((z*x i-z*(nodes A i*x i))-(1+v)*x i)-
    z*(nodes A i*((z*x i-z*(nodes A i*x i))-(1+v)*x i))-
    ((z*x i-z*(nodes A i*x i))-(1+v)*x i)=_
  change _=(z-z*nodes A i-1)*(z-z*nodes A i-1-v)*x i
  ring

theorem first_clear {A : Fin 6→Fin 6→K} {z:K} (hf:Front (scaleTable z A) z)
    (h:Op K) (hx:clears 3 (Op.eval A h 1)) :
    Op.eval A (Op.first z h) 1=0 := by
  change Op.eval A (Op.N z) (Op.eval A (Op.N z) (Op.eval A (Op.N z) (Op.eval A h 1)))=0
  simp only [eval_N]
  exact clear_all (tap_advances hf.tri hf.single (tap_advances hf.tri hf.single
    (tap_advances hf.tri hf.single hx)))

theorem second_clear {A : Fin 6→Fin 6→K} {z v:K} (hf:Front (scaleTable z A) z)
    (h4:nodes (scaleTable z A) 4=z-1-v) (h5:nodes (scaleTable z A) 5=z-1)
    (h:Op K) (hx:clears 3 (Op.eval A h 1)) :
    Op.eval A (Op.second z v h) 1=0 := by
  let y:=Op.eval A (Op.N z) (Op.eval A h 1)
  have hy : clears 4 y := by dsimp [y];rw [eval_N];exact tap_advances hf.tri hf.single hx
  have hj : Op.eval A (Op.J2 z) y=0 := first_clear hf h hx
  change Op.eval A (.mul (.sub (Op.Y z) .ident) (.sub (Op.Y z) (.scale (1+v) .ident))) y-
    (2:K) • Op.eval A (Op.J2 z) y=0
  rw [hj,smul_zero,sub_zero]
  ext i
  rw [eval_reflect_at]
  by_cases hi : i.val<4
  · rw [hy i hi,mul_zero];rfl
  · have hi' : i=4 ∨ i=5 := by
      have hi' := i.isLt
      omega
    rcases hi' with e|e <;> subst i
    · rw [h4];change _=0;ring
    · rw [h5];change _=0;ring

theorem eval_J2_head {A : Fin 6→Fin 6→K} {z:K} (hf:Front (scaleTable z A) z) :
    Op.eval A (Op.J2 z) 1 0=0 ∧ Op.eval A (Op.J2 z) 1 1=0 ∧
    Op.eval A (Op.J2 z) 1 2=scaleTable z A 2 1*scaleTable z A 1 0 := by
  let B:=scaleTable z A
  have hn0 : nodes B 0=1 := by rw [node_mat_one,at0 hf.tri hf.single];simp
  have hn1 : nodes B 1=1+B 1 0 := by rw [node_mat_one,at1 hf.tri hf.single];simp [B,add_comm]
  have e: Op.eval A (Op.J2 z) 1=tapMap B 1 (nodes B-1) := by
    change Op.eval A (Op.N z) (Op.eval A (Op.N z) 1)=_
    simp only [eval_N];congr 1;change mat B 1-(1:K)•(1:Vec K 6)=nodes B-1
    rw [one_smul,node_mat_one]
  rw [e]
  refine ⟨tap0 hf.tri hf.single _,?_,?_⟩
  · rw [tap1 hf.tri hf.single];simp [hn0]
  · change mat B (nodes B-1) 2-1*(nodes B-1) 2=B 2 1*B 1 0
    rw [at2 hf.tri hf.single]
    simp only [Pi.sub_apply,Pi.one_apply,hn0,hn1];ring

theorem head3 {x:Vec K 6} (h0:x 0=0) (h1:x 1=0) (h2:x 2=0) : clears 3 x := by
  intro i hi
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hc with e|e|e <;> subst i <;> assumption

theorem J2_clear {A : Fin 6→Fin 6→K} {z:K} (hf:Front (scaleTable z A) z)
    (hr:scaleTable z A 2 1=0) : clears 3 (Op.eval A (Op.J2 z) 1) := by
  obtain ⟨h0,h1,h2⟩:=eval_J2_head hf
  exact head3 h0 h1 (by rw [h2,hr,zero_mul])

theorem H_clear {A : Fin 6→Fin 6→K} {z:K} (hf:Front (scaleTable z A) z)
    (hw:w3 (scaleTable z A)=2*scaleTable z A 1 0)
    (hd:Op.D (scaleTable z A 1 0)*scaleTable z A 2 1=
      2*scaleTable z A 1 0*(3*scaleTable z A 1 0-2)) :
    clears 3 (Op.eval A (Op.H z (scaleTable z A 1 0)) 1) := by
  let B:=scaleTable z A
  let u:=B 1 0
  have hn0 : nodes B 0=1 := by rw [node_mat_one,at0 hf.tri hf.single];simp
  have hn1 : nodes B 1=1+u := by rw [node_mat_one,at1 hf.tri hf.single];simp [u,B,add_comm]
  have hn2 : nodes B 2=1+2*u := by
    rw [node_mat_one,at2 hf.tri hf.single]
    change B 2 0*1+B 2 1*1+1*1=1+2*(B 1 0)
    change w3 B=2*(B 1 0) at hw
    rw [← hw];unfold w3;ring
  have e (i:Fin 6) : Op.eval A (Op.H z u) 1 i=
      Op.D u*Op.eval A (Op.J2 z) 1 i-(3*u-2)*((nodes B i-1)*(nodes B i-1-u)) := by
    change Op.D u*Op.eval A (Op.J2 z) 1 i-(3*u-2)*Op.eval A (Op.Q z u) 1 i=_
    rw [eval_Q_at]
  obtain ⟨h0,h1,h2⟩:=eval_J2_head hf
  apply head3
  · rw [e,h0,hn0];ring
  · rw [e,h1,hn1];ring
  · rw [e,h2,hn2];change Op.D u*(B 2 1*u)-_ = 0
    change Op.D u*B 2 1=2*u*(3*u-2) at hd
    linear_combination u*hd

end RKCert.Paired.SDIRK.P6

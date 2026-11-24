module

public import RKCert.SDIRK6Elimination
public import RKCert.SDIRK6Flags

@[expose] public section
namespace RKCert.Paired.SDIRK.P6
open RKCert.Paired RKCert.Paired.SDIRK
/-! An operator expression is merely a convenient certificate format for finitely many
ordinary tree moments. Its interpretation is always the actual tableau and literal clock. -/
inductive Op (K : Type*) where
  | ident | prim | clock
  | sub (a b : Op K)
  | mul (a b : Op K)
  | scale (k : K) (a : Op K)

namespace Op
variable {K : Type*} [Field K] {s : ℕ}
def eval (A : Fin s→Fin s→K) : Op K → Vec K s →ₗ[K] Vec K s
  | .ident => LinearMap.id
  | .prim => mat A
  | .clock => diag (nodes A)
  | .sub a b => eval A a - eval A b
  | .mul a b => (eval A a).comp (eval A b)
  | .scale k a => k • eval A a

def foldTree : Op K → (Tree→K) → Tree→K
  | .ident, f => f
  | .prim, f => fun t => f (t.attach .leaf)
  | .clock, f => fun t => f (.attach .leaf t)
  | .sub a b, f => fun t=>foldTree a f t - foldTree b f t
  | .mul a b, f => foldTree b (foldTree a f)
  | .scale k a, f => fun t=> k * foldTree a f t

theorem foldTree_eq (A : Fin s→Fin s→K) (g : Op K)
    (l : Vec K s→ₗ[K] K) (t : Tree) :
    l (eval A g (stageWeight A t)) = foldTree g (fun t=>l (stageWeight A t)) t := by
  induction g generalizing l t with
  | ident => rfl
  | prim =>
    congr 1;ext i;simp [eval,stageWeight]
  | clock =>
    congr 1;ext i;simp [eval,stageWeight,nodes]
  | sub a b ha hb =>
    change l (eval A a _-eval A b _) = _
    rw [map_sub,ha,hb];rfl
  | scale k a h =>
    change l (k • eval A a _) = _
    rw [map_smul,h];rfl
  | mul a b ha hb =>
    change (l.comp (eval A a)) (eval A b (stageWeight A t))=_
    rw [hb]
    have h : (fun t => (l.comp (eval A a)) (stageWeight A t))=foldTree a (fun t=>l (stageWeight A t)) :=
      funext (ha l)
    rw [h];rfl

def height : Op K→ℕ
  | .ident=>0 | .prim=>1 | .clock=>1
  | .sub a b=>max (height a) (height b)
  | .mul a b=>height a+height b
  | .scale _ a=>height a

theorem foldTree_congr (g : Op K) (t : Tree) (f f' : Tree→K)
    (h : ∀ u, u.order≤t.order+height g → f u=f' u) :
    foldTree g f t=foldTree g f' t := by
  induction g generalizing t f f' with
  | ident => exact h t (by simp [height])
  | prim => exact h _ (by simp [height,Tree.order])
  | clock => exact h _ (by simp [height,Tree.order,Nat.add_comm])
  | sub a b ha hb =>
    change foldTree a f t-foldTree b f t=_
    rw [ha t f f' (fun u hu=>h u (by dsimp [height];omega)),
      hb t f f' (fun u hu=>h u (by dsimp [height];omega))];rfl
  | scale k a ha =>
    change k*foldTree a f t=_;rw [ha t f f' h];rfl
  | mul a b ha hb =>
    apply hb
    intro u hu
    apply ha
    intro v hv
    exact h _ (by dsimp [height];omega)

def expectation (g : Op K) : K := foldTree g (fun t => ((t.density:K))⁻¹) .leaf

theorem expectation_eq [CharZero K] {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (g : Op K) (hg : height g+1≤p) :
    row b (eval A g 1) = expectation g := by
  change row b (eval A g (stageWeight A .leaf))=_
  rw [foldTree_eq]
  apply foldTree_congr
  intro t ht
  exact (hasTreeOrderAtLeast_iff_inverse A b p).mp ho t (by change t.order≤1+height g at ht;omega)

def N (z:K) : Op K := .sub (.scale z .prim) .ident
def X (z:K) : Op K := .scale z .clock
def Q (z u:K) : Op K := .mul (.sub (X z) .ident) (.sub (X z) (.scale (1+u) .ident))
def J2 (z:K) : Op K := .mul (N z) (N z)
def Y (z:K) : Op K := .sub (.scale z .ident) (X z)
def D (u:K) : K := -2+u+4*u^2-u^3
def H (z u:K) : Op K := .sub (.scale (D u) (J2 z)) (.scale (3*u-2) (Q z u))
def first (z:K) (h:Op K) : Op K := .mul (J2 z) (.mul (N z) h)
def second (z v:K) (h:Op K) : Op K :=
  .mul (.sub (.mul (.sub (Y z) .ident) (.sub (Y z) (.scale (1+v) .ident))) (.scale 2 (J2 z)))
    (.mul (N z) h)

set_option maxHeartbeats 8000000 in
theorem zero_word [CharZero K] {A : Fin s→Fin s→K} {b : Vec K s} (ho : HasTreeOrderAtLeast A b 6)
    (z u v : K) : 720 * row b (eval A (first z (J2 z)) 1) = -zeroLaguerre z u v := by
  rw [expectation_eq ho _ (by simp [height,first,J2,N])]
  norm_num [expectation,foldTree,first,J2,N,zeroLaguerre,Tree.density,Tree.order,Tree.childDensityProduct]
  ring

set_option maxHeartbeats 8000000 in
theorem first_word [CharZero K] {A : Fin s→Fin s→K} {b : Vec K s} (ho : HasTreeOrderAtLeast A b 6)
    (z u v : K) : 720 * row b (eval A (first z (H z u)) 1) = bridge1 z u v := by
  rw [expectation_eq ho _ (by simp [height,first,J2,N,H,Q,X])]
  norm_num [expectation,foldTree,first,J2,N,H,Q,X,D,bridge1,Tree.density,Tree.order,Tree.childDensityProduct]
  ring

set_option maxHeartbeats 8000000 in
theorem second_word [CharZero K] {A : Fin s→Fin s→K} {b : Vec K s} (ho : HasTreeOrderAtLeast A b 6)
    (z u v : K) : 120 * row b (eval A (second z v (H z u)) 1) = bridge2 z u v := by
  rw [expectation_eq ho _ (by simp [height,second,J2,N,H,Q,X,Y])]
  norm_num [expectation,foldTree,second,J2,N,H,Q,X,Y,D,bridge2,Tree.density,Tree.order,Tree.childDensityProduct]
  ring

end Op
end RKCert.Paired.SDIRK.P6


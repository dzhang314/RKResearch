module
public import RKCert.CompanionBandMoments

@[expose] public section

/-! # Candidate reusable sparse stencil for repeated residue samples

This alternative checker is intentionally separate from the sealed replay.
Coordinate-only companion minor tags can be checked once instead of regenerated
when checking every residue value. No new arithmetic polynomial is assumed. -/
namespace RKCert.Compound
variable {R : Type*} [CommRing R]

abbrev LaplaceTerm (n : ℕ) := ℕ × Fin (n+1) × Bool × Option (ℕ×ℤ)

inductive ReplayStencil (n : ℕ) where
  | mono (tag : Option (ℕ×ℤ))
  | column (terms : List (LaplaceTerm n))
  deriving DecidableEq

def exactStencil {n k h : ℕ} (E : OrderedAxes n (k+1) h) (i t : Fin h) :
    ReplayStencil n :=
  if (E.axis t (Fin.last k)).val+1<n then .mono (bandTag (fullBandPairs E i t))
  else .column (List.ofFn fun s : Fin (k+1) =>
    (s.val+k, (E.axis i s).castSucc, decide (E.axis i s=E.axis t (Fin.last k)),
      bandTag (reducedBandPairs E i t s)))

def evalReplayStencil {n : ℕ} (b : Fin (n+1)→R) (W : ℕ→R) :
    ReplayStencil n → R
  | .mono none => 0
  | .mono (some (d,e)) => (e:R)*W d
  | .column ts => (ts.map fun t =>
      match t.2.2.2 with
      | none => 0
      | some (d,e) => (-1:R)^t.1*((e:R)*(b t.2.1*W d+
           (if t.2.2.1 then b (Fin.last n) else 0)*W (d+1)))).sum

theorem eval_exactStencil {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (M j w : ℕ) (u : R) (b : Fin (n+1)→R) (i t : Fin h) :
    evalReplayStencil b (monomialMomentWeight M j w u) (exactStencil E i t)=
      sparseMomentEntry E M j w u b i t := by
  by_cases l : (E.axis t (Fin.last k)).val+1<n
  · simp only [exactStencil,sparseMomentEntry,l,ite_true]
    cases bandTag (fullBandPairs E i t) with
    | none => rfl
    | some d => rcases d with ⟨d,e⟩; rfl
  · simp only [exactStencil,sparseMomentEntry,l,ite_false,evalReplayStencil,List.map_ofFn]
    rw [List.sum_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro s _
    cases tag : bandTag (reducedBandPairs E i t s) with
    | none => simp [tagLinearMoment,tag]
    | some d =>
      rcases d with ⟨d,e⟩
      by_cases he : E.axis i s=E.axis t (Fin.last k)
        <;> simp [tagLinearMoment,tag,he]

def decodeBandTag (a : ℕ) : Option (ℕ×ℤ) :=
  if a=0 then none else some ((a-1)/2, if (a-1)%2=0 then 1 else -1)

def decodeStencil (n k q : ℕ) : ReplayStencil n :=
  if q<16 then .mono (decodeBandTag q)
  else .column (List.ofFn fun s : Fin k =>
    let a := ((q-16)/2048^s.val)%2048
    (a/256, ⟨(a/16%8)%(n+1),Nat.mod_lt _ (Nat.succ_pos _)⟩,
      a/128%2==1, decodeBandTag (a%16)))

/-- Every matrix row is a single natural. Keeping the literal code small
is important for repeated kernel reduction of array access. -/
def stencilAt {n h : ℕ} (k : ℕ) (D : Array ℕ) (i t : Fin h) : ReplayStencil n :=
  decodeStencil n k ((D[i.val]?.getD 0 / (2^56)^t.val) % (2^56))

theorem stencilTable_sound {n k h : ℕ} {E : OrderedAxes n (k+1) h} {D : Array ℕ}
    (checked : (List.finRange h).all (fun i =>
      (List.finRange h).all (fun t => decide (stencilAt (k+1) D i t=exactStencil E i t)))=true) :
    ∀ i t, stencilAt (k+1) D i t=exactStencil E i t := by
  intro i t
  have row := List.all_eq_true.mp checked i (by simp)
  exact of_decide_eq_true (List.all_eq_true.mp row t (by simp))

/-- Store the useful finite weight prefix and preserve the exact standard
fallback outside it, avoiding any additional bounded-degree premise. -/
def cachedWeight (M j w : ℕ) (u : R) (D : Array ℕ) (d : ℕ) : R :=
  if h : d<D.size then (D[d]:R) else monomialMomentWeight M j w u d

theorem cachedWeight_sound {M j w : ℕ} {u : R} {D : Array ℕ}
    (h : ∀ i : Fin D.size, (D[i]:R)=monomialMomentWeight M j w u i.val) :
    cachedWeight M j w u D=monomialMomentWeight M j w u := by
  funext d
  by_cases hd : d<D.size
  · exact (dite_eq_left hd).trans (h ⟨d,hd⟩)
  · exact dite_eq_right hd

end RKCert.Compound

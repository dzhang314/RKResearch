/-! Finite integer obstruction for the symmetric ERK10 radius equation. -/
namespace RKResearch.ERK10SymmetricRadiusModEight

def numerator (a b c d : Int) : Int :=
  7*(a*a)*(c*c) - 2*(a*a)*(d*d) - 2*(b*b)*(c*c) + (b*b)*(d*d)

private def R (x y : Int) : Prop := x % 8 = y % 8

private theorem radd {a b c d : Int} (h : R a c) (k : R b d) : R (a+b) (c+d) := by
  unfold R at *
  rw [Int.add_emod a b, Int.add_emod c d, h, k]

private theorem rsub {a b c d : Int} (h : R a c) (k : R b d) : R (a-b) (c-d) := by
  unfold R at *
  rw [Int.sub_emod a b, Int.sub_emod c d, h, k]

private theorem rmul {a b c d : Int} (h : R a c) (k : R b d) : R (a*b) (c*d) := by
  unfold R at *
  rw [Int.mul_emod a b, Int.mul_emod c d, h, k]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem residues :
    ∀ a b c d : Fin 8,
      ((a.val:Int)%2 ≠ 0 ∨ (b.val:Int)%2 ≠ 0) →
      ((c.val:Int)%2 ≠ 0 ∨ (d.val:Int)%2 ≠ 0) →
      numerator a.val b.val c.val d.val % 8 ≠ 0 := by
  decide +kernel

theorem noIntegralRadii (a b c d : Int) (h₁ : a%2≠0 ∨ b%2≠0)
    (h₂ : c%2≠0 ∨ d%2≠0) :
    numerator a b c d ≠ 0 := by
  let ra : Fin 8 := ⟨(a % 8).toNat, by omega⟩
  let rb : Fin 8 := ⟨(b % 8).toNat, by omega⟩
  let rc : Fin 8 := ⟨(c % 8).toNat, by omega⟩
  let rd : Fin 8 := ⟨(d % 8).toNat, by omega⟩
  have ha : (ra.val : Int) = a % 8 := by dsimp [ra]; omega
  have hb : (rb.val : Int) = b % 8 := by dsimp [rb]; omega
  have hc : (rc.val : Int) = c % 8 := by dsimp [rc]; omega
  have hd : (rd.val : Int) = d % 8 := by dsimp [rd]; omega
  have h := residues ra rb rc rd
  rw [ha,hb,hc,hd] at h
  have h₁' : (a%8)%2≠0 ∨ (b%8)%2≠0 := by omega
  have h₂' : (c%8)%2≠0 ∨ (d%8)%2≠0 := by omega
  have ra' : R a (a % 8) := (Int.emod_emod a 8).symm
  have rb' : R b (b % 8) := (Int.emod_emod b 8).symm
  have rc' : R c (c % 8) := (Int.emod_emod c 8).symm
  have rd' : R d (d % 8) := (Int.emod_emod d 8).symm
  have hp : R (numerator a b c d) (numerator (a%8) (b%8) (c%8) (d%8)) := by
    unfold numerator
    have h7 : R 7 7 := rfl
    have h2 : R 2 2 := rfl
    exact radd
      (rsub (rsub (rmul (rmul h7 (rmul ra' ra')) (rmul rc' rc'))
                  (rmul (rmul h2 (rmul ra' ra')) (rmul rd' rd')))
            (rmul (rmul h2 (rmul rb' rb')) (rmul rc' rc')))
      (rmul (rmul rb' rb') (rmul rd' rd'))
  intro hzero
  unfold R at hp
  rw [hzero] at hp
  exact (h h₁' h₂') hp.symm

end RKResearch.ERK10SymmetricRadiusModEight
#print axioms RKResearch.ERK10SymmetricRadiusModEight.noIntegralRadii

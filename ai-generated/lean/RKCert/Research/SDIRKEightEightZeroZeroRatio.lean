import Mathlib.Tactic.Ring.Basic

/-! Division-free scalar receipts for the duplicate-terminal reverse gates. -/

namespace RKResearch.Certified.SDIRKEightEightZeroZeroRatio

variable {R : Type*} [CommRing R]

/-- Compare three literal aggregate affine errors after killing the
terminal input, without dividing by three possible ordinary weights. -/
theorem fourth_affine_clear
    {r t f α β Bt Br Bf Jt Jr Ff v p : R}
    (ht : -(Bt*Jt)=α+β*t) (hr : -(Br*Jr)=α+β*r)
    (hf : Bf*Ff=α+β*f) (hp : v*Jr=p*Jt) :
    v*(r-t)*Bf*Ff+
      Jt*(v*(r-t)*Bt+(f-t)*(p*Br-v*Bt))=0 := by
  calc
    _ = v*(r-t)*(Bf*Ff)+v*(r-t)*Bt*Jt+
          (f-t)*(Br*(p*Jt)-Bt*(v*Jt)) := by ring1
    _ = v*(r-t)*(Bf*Ff)+v*(r-t)*Bt*Jt+
          (f-t)*(Br*(v*Jr)-Bt*(v*Jt)) := by rw [hp]
    _ = v*((r-t)*((Bf*Ff)-(-(Bt*Jt)))-
          (f-t)*((-(Br*Jr))-(-(Bt*Jt)))) := by ring1
    _ = _ := by rw [hf,ht,hr]; ring1

/-- At the extra nodal root y the ordinary cleared cardinal numerator
is actually constant in y. -/
theorem extra_cardinal_square {s m₀ m₁ k : R} (hk : k=s*m₀-m₁) :
    k*(m₁-s*m₀)= -k^2 := by rw [hk]; ring1

end RKResearch.Certified.SDIRKEightEightZeroZeroRatio

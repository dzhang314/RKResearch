module
public import RKCert.DirkSevenLK89800
public import RKCert.DirkSevenLK89801
public import RKCert.DirkSevenLK89802
public import RKCert.DirkSevenLK89803
public import RKCert.DirkSevenLK89810
public import RKCert.DirkSevenLK89811
public import RKCert.DirkSevenLK89812
public import RKCert.DirkSevenLK89813
@[expose] public section
namespace RKCert.SevenPort.Branch898
open Polynomial RKCert.SevenPort RKCert.FixedFactor
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem fchecks:∀i:Fin 31,d5 (898:E) ((i.val:E)+2) 0=horner f ((i.val:E)+2):=by
  intro i;fin_cases i
  · exact fsample0
  · exact fsample1
  · exact fsample2
  · exact fsample3
  · exact fsample4
  · exact fsample5
  · exact fsample6
  · exact fsample7
  · exact fsample8
  · exact fsample9
  · exact fsample10
  · exact fsample11
  · exact fsample12
  · exact fsample13
  · exact fsample14
  · exact fsample15
  · exact fsample16
  · exact fsample17
  · exact fsample18
  · exact fsample19
  · exact fsample20
  · exact fsample21
  · exact fsample22
  · exact fsample23
  · exact fsample24
  · exact fsample25
  · exact fsample26
  · exact fsample27
  · exact fsample28
  · exact fsample29
  · exact fsample30
theorem feq:minPoly (898:E) 0=mp f:=fits_offset _ _ _ (by decide) fchecks
theorem fdeg:(mp f).natDegree=30:=by
  apply le_antisymm (natDegree_map_le.trans (degree_horner_le f _ (by decide)))
  apply le_natDegree_of_ne_zero
  rw [coeff_map,coeff_horner];decide +kernel
private theorem gchecks:∀i:Fin 31,d5 (898:E) ((i.val:E)+2) 1=horner g ((i.val:E)+2):=by
  intro i;fin_cases i
  · exact gsample0
  · exact gsample1
  · exact gsample2
  · exact gsample3
  · exact gsample4
  · exact gsample5
  · exact gsample6
  · exact gsample7
  · exact gsample8
  · exact gsample9
  · exact gsample10
  · exact gsample11
  · exact gsample12
  · exact gsample13
  · exact gsample14
  · exact gsample15
  · exact gsample16
  · exact gsample17
  · exact gsample18
  · exact gsample19
  · exact gsample20
  · exact gsample21
  · exact gsample22
  · exact gsample23
  · exact gsample24
  · exact gsample25
  · exact gsample26
  · exact gsample27
  · exact gsample28
  · exact gsample29
  · exact gsample30
theorem geq:minPoly (898:E) 1=mp g:=fits_offset _ _ _ (by decide) gchecks
theorem gdeg:(mp g).natDegree=30:=by
  apply le_antisymm (natDegree_map_le.trans (degree_horner_le g _ (by decide)))
  apply le_natDegree_of_ne_zero
  rw [coeff_map,coeff_horner];decide +kernel
private theorem bezout:∀i:Fin 61,horner a (i.val:E)*horner f (i.val:E)+horner b (i.val:E)*horner g (i.val:E)=1:=by decide +kernel
theorem good:res (898:E)≠0:=by
  rw [res,feq,geq]
  simpa only [fdeg,gdeg] using resultant_ne_zero _ _ (coprime_from_samples f g a b (by decide) (by decide) (by decide) (by decide) bezout)
end RKCert.SevenPort.Branch898

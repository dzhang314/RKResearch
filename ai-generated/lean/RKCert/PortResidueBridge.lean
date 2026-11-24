module
public import RKCert.PortGridSetup
@[expose] public section
namespace RKCert.PortRank
open Polynomial RKCert.FixedFactor
universe u
theorem port_det_residue_of_checked (checked : portChecked allKnots=true) {E : Type u} [Field E] [CharP E 1361] (P:E[X]) (w:E)
    (pm:P.Monic) (pd:P∣F.map (Int.castRingHom E)) (deg:P.natDegree≤5)
    (hw:(H.map (Int.castRingHom E)).eval w=0) (pw:P.eval w=0) : portDet P w≠0 := by
  let φ:=ZMod.castHom (dvd_refl 1361) E
  have fh : φ.comp (Int.castRingHom (ZMod 1361))=Int.castRingHom E:=Subsingleton.elim ..
  have ef : F.map (Int.castRingHom E)=linearProduct φ allKnots := by
    rw [←fh,←map_map,F_split,map_product]; rfl
  have eh : H.map (Int.castRingHom E)=linearProduct φ nonzeroKnots := by
    rw [←fh,←map_map,H_split,map_product]; rfl
  obtain ⟨B,fac⟩:=pd
  obtain ⟨t,sub,pt⟩:=select_monic_factor (fun z=>φ z) allKnots P B pm (fac.symm.trans ef)
  obtain ⟨a,ha,e⟩:=endpoint_of_product φ t w (pt ▸ pw)
  obtain ⟨v,vt,ev⟩:=endpoint_of_product φ nonzeroKnots w (eh ▸ hw)
  have av:a=v:=φ.injective (e.symm.trans ev)
  have an:a≠0:=by intro az; have vz:v=0:=av.symm.trans az; exact (by decide : (0:ZMod 1361)∉nonzeroKnots) (vz ▸ vt)
  have dt:t.length≤5:=by rwa [pt,degree_product] at deg
  have nz:=portCheckSound checked sub dt ha an
  have mp:P=(linearProduct id t).map φ:=pt.trans (map_product φ id t).symm
  rw [mp,e,←map_portDet]
  exact fun z=>nz (φ.injective (z.trans φ.map_zero.symm))

theorem port_det_integral_of_checked (checked : portChecked allKnots=true) {K : Type u} [Field K] [CharZero K] (P:K[X]) (w:K)
    (pm:P.Monic) (pd:P∣F.map (Int.castRingHom K)) (deg:P.natDegree≤5)
    (hw:(H.map (Int.castRingHom K)).eval w=0) (pw:P.eval w=0) : portDet P w≠0 :=
  good_prime_marked_factor 1361 F H monic_F monic_H 5 (@portDet) (@map_portDet)
    (port_det_residue_of_checked checked) P w pm pd deg hw pw


end RKCert.PortRank

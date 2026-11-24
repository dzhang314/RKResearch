module
public import RKCert.Dirk17Minimal
public import RKCert.Dirk17QuarticBudget
@[expose] public section
namespace RKCert.Paired.Seventeen
open Polynomial Module Terminal RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
/-- In the minimal anchored p17 chart even the unrestricted cubic original
forward probes are jointly invisible. The four plus three observations come
from two distinct marked physical pivots, before any quartic ratio arises. -/
theorem minimal_cubic_joint (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Minimal A b):
    zeroSpace A 3≤jointWithOrigin A b 0:=by
  intro v hv
  obtain ⟨Q,dq,fit,off,θ,tr,ac⟩:=h.D.port_contrast ha ho (by decide) (by decide) hv (h.zero _ (zeroSpace_mono A (by decide) hv))
  have van:Q=0:=by
    by_contra nz
    obtain ⟨i,l,_,_,_,_,un,vn,vu,first,second⟩:=h.D.two_paid_ports ha ho (by decide) (by decide) tr nz ac
    apply nz
    exact quintic_four_three Q (by omega) un vn vu
      (fun k=>first k.val (by have:=k.isLt;omega)) (fun k=>second k.val (by have:=k.isLt;omega))
  have hit(i:Fin 23) (ti:tau A b i≠0):v i=0:=by simpa [van] using fit i ti
  apply jointWithOrigin_iff.mpr
  refine ⟨⟨?_,?_⟩,fun _=>zeroSpace_first_of_row h.origin 3 hv⟩ <;> ext i
  · by_cases t:tau A b i=0
    · exact off i t
    · simp [hit i t]
  · by_cases t:tau A b i=0
    · simp [t]
    · simp [hit i t]

/-- An original-width count, not a fixed Radau ansatz: at most seven
distinct clean active clocks remain, including the true terminal clock zero. -/
theorem minimal_seven_sites (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Minimal A b)
    (anc:q₂ (mat A) (nodes A) 1=0): (cleanSites A b).card≤7 ∧ 0∈cleanSites A b:=by
  classical
  have dirty:=signed_cubic_sharp_physical ha ho h.D (j:=7) (by decide) (by decide)
  change 15≤(Finset.univ.filter (fun i=>tau A b i≠0)).card at dirty
  have top:=clean_active_plus_joint (A:=A) (b:=b) 0
  have low:= (ranks ha ho).three
  have e:excess A=0:=by simp [excess,anc]
  rw [e] at low
  have sub:=Submodule.finrank_mono (minimal_cubic_joint ha ho h)
  have small:(cleanSites A b).card≤(cleanActive A b).card:=Finset.card_image_le
  have f3:finrank K (zeroSpace A 3)=1:=by simpa using low
  have joint:1≤finrank K (jointWithOrigin A b 0):=f3.ge.trans sub
  refine ⟨by omega,?_⟩
  have t0:tau A b (Fin.last 22)=0:=by
    have td:tau A b∈dirkBack A b 1:=by rw [h.D.one];exact Submodule.subset_span (Set.mem_singleton _)
    have marked0:tau A b∈ReverseHermite.zeroMarked A 17 (Fin.last 22) 3:=by
      rw [h.D.cover 3 (by decide) (by decide)];exact td
    exact marked0.2
  simpa only [terminal_mirror_zero h.T] using mem_cleanSites (Fin.last 22) h.T.weight_ne t0
end
end RKCert.Paired.Seventeen

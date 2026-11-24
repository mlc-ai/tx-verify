-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Representative
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Fits

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Flow.Arith32 SmWarp
variable {p : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event} {ns nv : Nat}

theorem fits_next (hc : ctaR p L g = Epilogue.ctaW L g) (rep : Represents p L g d d' e)
    (hF : SFits p L g d.scheduler ns nv) (hE : SExpect p L g d.scheduler ns e) :
    SFits p L g d'.scheduler (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨a, ev, hev, _, hs, hsite, hv, _, _, hm⟩ := rep
  have h : SFits p L g a (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
    rcases hm with rfl | ⟨site, _, hsh, hvote⟩
    · exact sfits_next hc hF hE hev hs
    · have e' : SExpect p L g d.scheduler ns ev := by
        obtain ⟨s,v,k,acc⟩ := d
        change payloadSite s at site
        rcases site with ⟨i,j,rfl⟩ | ⟨b,c,rfl⟩ <;>
          exact fun h => by cases h
      have hsh' : Epilogue.sh ev = Epilogue.sh e := by unfold Epilogue.sh; rw [hsh]
      have hv' : Epilogue.vt ev = Epilogue.vt e := by unfold Epilogue.vt; rw [hvote]
      rw [← hsh', ← hv']
      exact sfits_next hc hF e' hev hs
  cases d' with
  | mk s v k acc =>
    cases hsite
    cases hv
    exact h

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Prologue.Input

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control

private theorem ld_site (s : Site) :
    s.pc = 34 ∨ s.pc = 37 ∨ s.pc = 41 → s = .ld 0 ∨ s = .ld 1 ∨ s = .ld 2 := by
  cases s <;> decide +revert

/-- A request-word load reads input bytes. -/
public theorem request_address {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩) (site : pc = 34 ∨ pc = 37 ∨ pc = 41) :
    Iface.InputAcc Q a := by
  have hg := he.lt hX
  obtain ⟨w,d,t,ins,u,ht,_,pce,hc,fire,_⟩ := prologue_occ hp hX hf he (by simp)
    (by change 27 < pc; omega) (by change pc < 574; omega)
  have pc : pc = d.site.pc := pce
  subst pc
  rcases ld_site d.site site with hs | hs | hs <;>
    exact request_input hp hg _ hs ht hc fire

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

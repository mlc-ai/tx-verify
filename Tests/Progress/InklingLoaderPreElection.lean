-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

import Kernels.InklingRelDecode.Proof.Loader.Export.NoElection
import Kernels.InklingRelDecode.Proof.Loader.Machine
import Kernels.InklingRelDecode.Proof.Dispatch.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Tests
open PTX PTX.Proof

/-- Split zero has one MMA block and no recurrent Loader block. -/
private theorem all_preloaded {Q : Params} {L : Launch} {c r : Nat}
    (split : (L.ctaidOf c).get .x = 0) (req : (L.ctaidOf c).get .z = r)
    (two : Q.splits = 2) (seq : Q.seqK r = 129) (len : Q.qLen r = 1) :
    Q.numIters r 0 = 1 ∧ Iface.preloadCount Q L c = 1 := by
  simp [Iface.preloadCount,Params.numIters,Params.blocks,Params.past,split,req,two,seq,len]

/-- The actual control successors skip the issue loop, return to dispatch, and
take the exit branch when the exit role byte is broadcast. -/
example (L : Launch) (g : Nat) (e : Event) (hw : g%L.block/32=6) :
    let d : Loader.D := {site := .beginBar,counter := b32 1,limit := b32 1}
    Loader.next L g d e = some (some {d with site := .endBar}) ∧
    Loader.next L g {d with site := .endBar} e = some (some {d with site := .inc}) ∧
    Loader.next L g {d with site := .inc} e = some (some {d with site := .dispatch}) ∧
    Dispatch.target 3 = .exitSync ∧
    Dispatch.next L g ⟨.exitSync,1⟩ e = some (some ⟨.ret,1⟩) ∧
    Dispatch.next L g ⟨.ret,1⟩ ⟨2855,.exit⟩ = none := by
  have late : ¬ g%L.block<32 := by omega
  exact ⟨rfl,rfl,rfl,rfl,by simp [Dispatch.next,late],rfl⟩

/-- In an exited CTA for this split, every lane of warp 6 has no election and
its first lane has exited. The no-election/no-exit implication cannot hold
uniformly for completed work. -/
theorem preloaded_exit {Q L m X c r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hc : c<L.grid) (ex : CtaExited L X c)
    (split : (L.ctaidOf c).get .x = 0) (req : (L.ctaidOf c).get .z = r)
    (two : Q.splits = 2) (seq : Q.seqK r = 129) (len : Q.qLen r = 1) :
    (∀ g, g/L.block=c → g%L.block/32=6 → ∀ k pc mask inst lane,
      X.get (g,k) ≠ some ⟨pc,.elect mask inst lane⟩) ∧
    ∃ pc, (X.tr (c*L.block+192)).getLast? = some ⟨pc,.exit⟩ := by
  obtain ⟨one,full⟩ := all_preloaded split req two seq len
  constructor
  · intro g cta warp
    apply Loader.Export.no_election_of_preloaded hp hX hf warp
    rw [cta,req,split,one,full]
  · apply ex
    · simp only [Launch.threads,hp.block]
      omega
    · rw [hp.block]
      omega

end PTX.Kernels.InklingRelDecode.Proof.Tests

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyCheckpoint
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasBoxes
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

private theorem warmBiasExpectationOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {t : Nat} {s : TState} (hs : At s 1153 [(2041,b32 32768),(1140,b32 (l.sharedBase+320))]) :
    out kernel Assumptions.all l t s = .ev (.arrive (biasReadyObject l (t/l.block) 0)
      32768 (next (mbarStateDest s (some 7698))) 1 true .cta) := by
  rw [loaderOutCore (by rw [hs.1]; decide) (by rw [hs.1]; decide)]
  rw [out_event hs.2.2.2.1 (by rw [hs.1]; exact Flow.code_1153) rfl rfl]
  have hBase : l.sharedBase+320 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+320)%8 = 0 := by have := hp.shared.1; omega
  have hEff : effAddr l t s .shared 1140 0 = .ok (biasReadyObject l (t/l.block) 0) := by
    simpa [biasReadyObject] using effAddr_b32_off (off := 0) hs.2.2.2.2.2.1 hBase
  have hLoc : mbarLoc l t s 1140 0 = .ok (biasReadyObject l (t/l.block) 0) := by
    simp [mbarLoc,hEff,biasReadyObject,hAlign,bind,Except.bind,pure,Except.pure]
  have hOne : readBits l t s 32 (.imm 1) = .ok 1#64 := rfl
  simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hs.2.2.2.2.1 (by decide),
    hOne,bind,Except.bind,pure,Except.pure,ofExec]

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

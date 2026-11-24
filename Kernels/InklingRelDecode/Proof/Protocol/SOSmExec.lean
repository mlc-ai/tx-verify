-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSmRun
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaExec

@[expose] public section

/-!
# The default partition's handshake events on an execution

The default partition's thread is **not yet a composed `Flow.Machine`** (the prologue, the softmax
region, the bridge and the epilogue are separate code machines). What the protocol needs from the
composed thread is one named structure, `SmRunAt`: the events of thread `g` from event `k₀` on are
a run of the softmax region's machine from the state `d₀`, and the events from `k₀` up to `k`
reach the state `d`. With it:

* `sm_swait_exec`: a successful poll of `s_ready b` at event `k` is at the `waitS` site of an
  iteration `i` with `i = blockB b n`, `n` the thread's earlier successful polls of that barrier,
  and its parity is `fullParity i`, which is `n % 2`: the parity field of the barrier's thread-layer
  facts, for each of the 128 softmax threads.
* `sm_parrive_exec`: an arrival on `p_ready b` at event `k` is at the `arrive` site of iteration
  `i`, of thread 0 of the block, and `i = blockB b n`, `n` the thread's earlier arrivals on that
  barrier: the thread's `n`-th arrival on `p_ready b` is for block `2 n + b`.
* `sm_no_parrive`: a thread other than thread 0 has no arrival on `p_ready b` in the run.
* `sm_owait_exec`: a successful poll of `o_done` at event `k` is at the `waitO` site of iteration
  `i`, with parity `oDoneParity i` (from `WaitOShape`).

The premises `smPolled d₀ = 0` and no earlier poll (arrival) before `k₀` say that the run starts at
the beginning of the region (`Sm.Inv.start`): the role is entered once. The default partition's
earlier code (the prologue) polls no handshake barrier; that is `hfresh`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW countP_take_split)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d0 : Sm.D}

/-- **What the composed default-partition thread has to provide.** The events of thread `g` from
event `k₀` are a run of the softmax region's machine from `d₀`, and the events from `k₀` up to `k`
reach `d`. -/
structure SmRunAt (L : Launch) (X : Execution) (g k0 k : Nat) (d0 d : Sm.D) : Prop where
  trace : (Sm.code Sm.asms L g d0).toMachine.Trace (some d0) ((X.tr g).drop k0)
  reach : (Sm.code Sm.asms L g d0).toMachine.after (some d0)
    (((X.tr g).drop k0).take (k - k0)) = some (some d)

/-! ### On a run -/

/-! ### On an execution -/

end
end PTX.Kernels.InklingRelDecode.Proof.SO

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Select
public import Kernels.InklingRelDecode.Proof.Interface.Reach
public import Kernels.InklingRelDecode.Proof.Interface.Writes
public import Kernels.InklingRelDecode.Proof.Interface.Output
public import Kernels.InklingRelDecode.Proof.Interface.OutputFrame
public import Kernels.InklingRelDecode.Proof.Interface.Bridge
public import Kernels.InklingRelDecode.Proof.Interface.Premises
public import Kernels.InklingRelDecode.Proof.Interface.Facts
public import Kernels.InklingRelDecode.Proof.Interface.Reads
public import Kernels.InklingRelDecode.Proof.Interface.Inject
public import Kernels.InklingRelDecode.Proof.Interface.LseValue
public import Kernels.InklingRelDecode.Proof.Interface.MmaFacts
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Interface.SyncSites
public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts

/-!
# The interface between the thread layer and the layers above: umbrella

The layers above the thread layer follow every thread by one machine, `threadCode L g Q`
(`Select`): its abstract states are `TSt.d s` (a default-partition thread, `DComp.code`) or
`TSt.w s` (a worker thread, `WComp.code`), chosen by `g % L.block < 128`. Everything here speaks of
`Frame.stateAt (code L Q) X g k`, the state before event `k` of thread `g`, and of the machines'
sites; no program counter or register number occurs outside `Site.pc`/`evPc`.

## What is proved

* `Select`: `threadCode`, `sound` (every launched thread's machine is sound under `Pre` and the
  softmax region's obligations `SmOb`).
* `Reach`: `TReach` and `treach_stateAt`: the prologue's numbers and the epilogue's registers carry
  the launch's meaning at every state of a run (`Epi.Means` at the epilogue).
* `Premises`: `Premises` (`WPremises`, `DPremises`, `tmplOk`), `tracked_of_premises`, `ub_stop`,
  `no_ub`.
* `Facts`: `ThreadFacts` (`sound`, `tracked`, `tracked_select`, `ub_stop`, `reach`, `global_wr`,
  `write_in_arrays`), `threadFacts` and `ThreadFacts.post_frame` (`Post`'s last conjunct).
  `Bridge`: `tracked_select` turns `tracked` into the bound layer's `htr`
  (`Bound.threadCode L Q` unfolds to `selectCode L Q`).
* `Writes`, `Output`, `OutputFrame`: every global write is an epilogue store of `OPart` or
  `LsePart`, with the word and footprint `Spec` gives; no atomic, copy, tensor store or
  cancellation writes global memory.
* `Reads`: `reads_mem0`, `read_launch_byte`: a read of a `Params.reads` byte returns the launch
  byte. `Inject`: two overlapping global writes are stores of the same output element.
  `LseValue`: the `-inf` bytes of an empty row.
* `MmaFacts`, `CopyFacts`, `SyncSites`, `SyncFacts`, `ExitFacts`: MMAs and commits, tensor copies,
  mbarrier initializations, arrivals and polls, and exits fire from the sites of the roles that own
  them, with those sites' event shapes; in a complete execution every thread exits.
  Use them as `mma_event_state hpre hX hf.sound hf.tracked ...` for `hf : ThreadFacts ..`.

## What is not (rows of "thread-layer gaps" in the development notes, "interface layer")

* The two machines' premises are one generic field each (`follows`), not yet per-site semantic
  conditions; `tmplOk` is a premise.
* The softmax region's score stage is `DComp.SmObligations` (`SmOb`); the values `l`, `mx`, `lse`,
  `eq0` of the epilogue's registers are not tied to `Spec.rowSum`.
* No event shape for the worker's role-byte read, so there is no classification of all global
  reads; the Spec-level addresses of the prologue's block-table and query loads are not stated.
* From an output element back to its thread, that a store site runs once per thread, and that a
  valid row's thread issues all its stores (`issued`) are not proved.
-/

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsScanFirst
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsScanLoop
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsScanLoop2
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsScanSecond
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsSelect
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsTiles
import Kernels.TmlFa4Fwd.Proof.Epilogue.StepsWrite
import Kernels.TmlFa4Fwd.Gen.StepEpilogue

@[expose] public section

/-! # The output warp's obligations

Every state of the output warp's machine satisfies its step obligation (`stepAt`): the site
files prove them by `site_cases`, one theorem per kind of site, checked in parallel. With the
startup facts at `setmaxnreg` (the prologue's hand-off) this is the machine's soundness. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt (hp : Pre p L m) (hg : g < L.threads) (d : D) : (code p L g ent).StepAt d := by
  cases hs : d.site with
  | start => exact stepAt_start hp hg d hs
  | word k =>
    cases k with
    | first => exact stepAt_word_first hp hg d hs
    | loop => exact stepAt_word_loop hp hg d hs
    | second => exact stepAt_word_second hp hg d hs
    | loop2 => exact stepAt_word_loop2 hp hg d hs
  | down k =>
    cases k with
    | first => exact stepAt_down_first hp hg d hs
    | loop => exact stepAt_down_loop hp hg d hs
    | second => exact stepAt_down_second hp hg d hs
    | loop2 => exact stepAt_down_loop2 hp hg d hs
  | up k j =>
    cases k with
    | first => exact stepAt_up_first hp hg d ⟨j, hs⟩
    | loop => exact stepAt_up_loop hp hg d ⟨j, hs⟩
    | second => exact stepAt_up_second hp hg d ⟨j, hs⟩
    | loop2 => exact stepAt_up_loop2 hp hg d ⟨j, hs⟩
  | total k =>
    cases k with
    | first => exact stepAt_total_first hp hg d hs
    | loop => exact stepAt_total_loop hp hg d hs
    | second => exact stepAt_total_second hp hg d hs
    | loop2 => exact stepAt_total_loop2 hp hg d hs
  | vote l => exact stepAt_vote hp hg d ⟨l, hs⟩
  | pre l => exact stepAt_pre hp hg d ⟨l, hs⟩
  | tiles l =>
    cases l with
    | false => exact stepAt_tiles_first hp hg d hs
    | true => exact stepAt_tiles_late hp hg d hs
  | q0 => exact stepAt_read hp hg d (.inl hs)
  | q1 => exact stepAt_read hp hg d (.inr hs)
  | ready st => exact stepAt_ready hp hg d ⟨st, hs⟩
  | store st b => exact stepAt_store hp hg d ⟨st, b, hs⟩
  | commit st => exact stepAt_commit hp hg d (.inl ⟨st, hs⟩)
  | drain st => exact stepAt_commit hp hg d (.inr ⟨st, hs⟩)
  | free st => exact stepAt_free hp hg d ⟨st, hs⟩
  | exit l => exact stepAt_exit hp hg d ⟨l, hs⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue

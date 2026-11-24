-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Mma.StepsCommit
import Kernels.TmlFa4Fwd.Proof.Mma.StepsEnd
import Kernels.TmlFa4Fwd.Proof.Mma.StepsPv01
import Kernels.TmlFa4Fwd.Proof.Mma.StepsPv23
import Kernels.TmlFa4Fwd.Proof.Mma.StepsQk01
import Kernels.TmlFa4Fwd.Proof.Mma.StepsQk23
import Kernels.TmlFa4Fwd.Proof.Mma.StepsReq
import Kernels.TmlFa4Fwd.Proof.Mma.StepsScanFirst
import Kernels.TmlFa4Fwd.Proof.Mma.StepsScanLoop
import Kernels.TmlFa4Fwd.Proof.Mma.StepsScanLoop2
import Kernels.TmlFa4Fwd.Proof.Mma.StepsScanSecond
import Kernels.TmlFa4Fwd.Proof.Mma.StepsSelect
import Kernels.TmlFa4Fwd.Proof.Mma.StepsSetup
import Kernels.TmlFa4Fwd.Proof.Mma.StepsShfl
import Kernels.TmlFa4Fwd.Proof.Mma.StepsTiles
import Kernels.TmlFa4Fwd.Proof.Mma.StepsWait
import Kernels.TmlFa4Fwd.Gen.StepMma

@[expose] public section

/-! # The MMA warp's obligations

Every state of the MMA warp's machine satisfies its step obligation (`stepAt`): the site files
prove them by `site_cases`, one theorem per family of sites, checked in parallel. Five sites are
overrides: the two named barriers, the permit relinquishment and the deallocation, whose
continuation `advances` did not know when they were written, and the poll of PV block 0 on a
lane that issues no MMA, whose segment `seg_sym` cannot walk in one piece (`stepOk_mw0`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt (hp : Pre p L m) (hg : g < L.threads) (d : D) : (code p L g ent).StepAt d := by
  cases hs : d.site with
  | bar1 => exact stepAt_bar1 hp hg d hs
  | ldAlloc => exact stepAt_setup hp hg d (.inl hs)
  | bcast => exact stepAt_setup hp hg d (.inr hs)
  | word k =>
    cases k with
    | first => exact stepAt_scan_first hp hg d (.inl hs)
    | loop => exact stepAt_scan_loop hp hg d (.inl hs)
    | second => exact stepAt_scan_second hp hg d (.inl hs)
    | loop2 => exact stepAt_scan_loop2 hp hg d (.inl hs)
  | down k =>
    cases k with
    | first => exact stepAt_scan_first hp hg d (.inr (.inl hs))
    | loop => exact stepAt_scan_loop hp hg d (.inr (.inl hs))
    | second => exact stepAt_scan_second hp hg d (.inr (.inl hs))
    | loop2 => exact stepAt_scan_loop2 hp hg d (.inr (.inl hs))
  | up k j =>
    cases k with
    | first => exact stepAt_scan_first hp hg d (.inr (.inr (.inl ⟨j, hs⟩)))
    | loop => exact stepAt_scan_loop hp hg d (.inr (.inr (.inl ⟨j, hs⟩)))
    | second => exact stepAt_scan_second hp hg d (.inr (.inr (.inl ⟨j, hs⟩)))
    | loop2 => exact stepAt_scan_loop2 hp hg d (.inr (.inr (.inl ⟨j, hs⟩)))
  | total k =>
    cases k with
    | first => exact stepAt_scan_first hp hg d (.inr (.inr (.inr hs)))
    | loop => exact stepAt_scan_loop hp hg d (.inr (.inr (.inr hs)))
    | second => exact stepAt_scan_second hp hg d (.inr (.inr (.inr hs)))
    | loop2 => exact stepAt_scan_loop2 hp hg d (.inr (.inr (.inr hs)))
  | vote l => exact stepAt_select hp hg d (.inl ⟨l, hs⟩)
  | pre l => exact stepAt_select hp hg d (.inr (.inl ⟨l, hs⟩))
  | tiles l =>
    cases l with
    | false => exact stepAt_tiles hp hg d hs
    | true => exact stepAt_select hp hg d (.inr (.inr hs))
  | q0 => exact stepAt_req hp hg d (.inl hs)
  | q1 => exact stepAt_req hp hg d (.inr (.inl hs))
  | uk => exact stepAt_req hp hg d (.inr (.inr hs))
  | wt k => exact stepAt_wait hp hg d (.inl ⟨k, hs⟩)
  | mw b l => exact stepAt_wait hp hg d (.inr ⟨b, l, hs⟩)
  | sh k => exact stepAt_shfl hp hg d ⟨k, hs⟩
  | eq b =>
    if hb : b.val < 2 then exact stepAt_qk01 hp hg d (.inl ⟨b, hb, hs⟩)
    else exact stepAt_qk23 hp hg d (.inl ⟨b, by omega, hs⟩)
  | qk b j =>
    if hb : b.val < 2 then exact stepAt_qk01 hp hg d (.inr ⟨b, j, hb, hs⟩)
    else exact stepAt_qk23 hp hg d (.inr ⟨b, j, by omega, hs⟩)
  | ep b =>
    if hb : b.val < 2 then exact stepAt_pv01 hp hg d (.inl ⟨b, hb, hs⟩)
    else exact stepAt_pv23 hp hg d (.inl ⟨b, by omega, hs⟩)
  | pv b j =>
    if hb : b.val < 2 then exact stepAt_pv01 hp hg d (.inr ⟨b, j, hb, hs⟩)
    else exact stepAt_pv23 hp hg d (.inr ⟨b, j, by omega, hs⟩)
  | ce c => exact stepAt_commit hp hg d (.inl ⟨c, hs⟩)
  | cm c => exact stepAt_commit hp hg d (.inr ⟨c, hs⟩)
  | relinq l => exact stepAt_end hp hg d (.inl ⟨l, hs⟩)
  | bar2 l => exact stepAt_end hp hg d (.inr (.inl ⟨l, hs⟩))
  | dealloc l => exact stepAt_end hp hg d (.inr (.inr (.inl ⟨l, hs⟩)))
  | exit l => exact stepAt_end hp hg d (.inr (.inr (.inr ⟨l, hs⟩)))

end PTX.Kernels.TmlFa4Fwd.Proof.Mma

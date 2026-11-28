-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Lemmas.Flow.SegChain
import Kernels.InklingRelDecode.Proof.Lib.MmaBits
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.Footprint

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

abbrev liveFacts (L : Launch) (regs : Nat → Value) (w : Value) (d : D) (pc : Nat) :=
  factsFrom (Flow.live pc) (valueOf L regs w d)

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w d

local macro "cross_arith" : tactic => `(tactic| (
  intro t ht
  seg_fp ht using
    try simp only [valueOf, values, lookupLit, Option.getD_some, Option.getD_none]
    all_goals seg_close [D.limit, Lib.mulhi3, Nat.and_one_is_mod, Lib.bfe_u32, Lib.lor_field, qLo,
      kLo, vLo, descHi, desc, vdesc]))

theorem setup_descriptors (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i = 0) :
    Seg kernel Assumptions.all L g 14 2428 (F 2428) 2442 (F 2442) := by cross_arith

theorem seed_cursors (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i = 0) :
    Seg kernel Assumptions.all L g 4 2443 (F 2443) 2455 (F 2455) := by cross_arith

theorem ready_head (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i < 2 ^ 31) :
    Seg kernel Assumptions.all L g 4 2457 (F 2457) 2461 (F 2461) := by cross_arith

theorem first_iter (hi : d.i < 2 ^ 31) :
    Seg kernel Assumptions.all L g 1 2500 (F 2500) 2501 (F 2501) := by cross_arith

theorem p_head (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i < 2 ^ 31) (hp : 1 ≤ d.i) :
    Seg kernel Assumptions.all L g 7 2502 (F 2502) 2509 (F 2509) := by cross_arith

theorem bump_cursors (hi : d.i ≤ d.limit)
    (hn : d.limit ≤ 2147483646) :
    Seg kernel Assumptions.all L g 7 2447 (F 2447) 2454
      (liveFacts L regs w {d with i := d.i + 1} 2454) := by
  cases d
  simp only [D.limit] at hn hi
  cross_arith

end
end PTX.Kernels.InklingRelDecode.Proof.Mma

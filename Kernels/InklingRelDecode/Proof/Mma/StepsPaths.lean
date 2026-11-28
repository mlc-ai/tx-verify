-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Loop
import Kernels.InklingRelDecode.Proof.Mma.Offsets
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Kernels.InklingRelDecode.Proof.Lib.MmaBits
import Lemmas.Flow.LandsU
import Lemmas.Flow.Step.AdvancesTc
import Lemmas.Flow.Footprint

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof
variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value}
local notation "MC" => (code L g regs w)
local notation "F" => liveFacts L regs w
local notation "S" => SegU kernel Assumptions.all L g

theorem crossing {d dst : D} {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins) (hl : ins.op.isLocal = false)
    (hguard : Code.GuardTrue ((MC).facts d) ins.guard)
    (adv : ∀ {t e u}, Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e (some u) →
      u = PTX.next t)
    (hn : ∀ e, next L g d e = some (some dst))
    (span : Inv d → S (d.site.pc + 1) ((MC).facts d) dst.site.pc ((MC).facts dst))
    (inv : Inv d → Inv dst) : (MC).StepAtU d := by
  refine ⟨fun _ => ⟨ins,hc,hl,hguard⟩, ?_⟩
  intro t e u ins' ht hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := adv hf
  obtain ⟨s,hτ,hgood⟩ := Code.landsU (C := MC) (d := dst)
    (At.next (Code.at_of_atD ht rfl rfl)) (span hi) (inv hi) rfl rfl
  exact .inl (.inr ⟨dst,s,hn e,hτ,hgood⟩)

theorem inv_iter {d : D} (hi : d.i ≤ d.limit) (hn : d.limit ≤ 2147483646) : Inv (iterNext d) := by
  unfold iterNext
  split_ifs <;> simp only [Inv, D.limit] at * <;> omega

theorem inv_after {d : D} (hi : d.i < d.limit) (hn : d.limit ≤ 2147483646) : Inv (afterQk d) := by
  unfold afterQk
  split
  · exact inv_iter hi.le hn
  · change 0 < d.i ∧ d.i ≤ d.limit ∧ d.limit ≤ _
    omega

macro "mma_arithmetic_span" : tactic => `(tactic| (
  intro t ht
  seg_fp ht using
    try simp only [valueOf, values, lookupLit, Option.getD_some, Option.getD_none]
    all_goals seg_close [D.limit, Lib.mulhi3, Nat.and_one_is_mod, Lib.bfe_u32, Lib.lor_field,
      qLo, kLo, vLo, descHi, desc, vdesc]))

variable {Q : Params} {m : Mem0} (hp : Pre Q L m) (i : Nat) (v : Value)
include hp

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem qk_notify_step : (MC).StepAtU ⟨.qkCommit,i,v⟩ := by
  let d : D := ⟨.qkCommit,i,v⟩
  refine crossing (d := d) (dst := afterQk d) Flow.code_2499 rfl
    (Code.guardTrue_factsFrom (show 10 ∈ Flow.live 2499 by decide) rfl)
    fires_tcCommit (fun _ => rfl) ?_ (fun hi => inv_after hi.left hi.right)
  intro hi
  apply SegU.comp (b := 2500) (G := F d 2500)
  · exact SegU.of_seg (n := 0) (fun t ht => by dsimp only [d,code] at ht ⊢; seg_fp ht using rfl)
  · exact after_qk hp.sharedRange hi.left hi.right

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem qk_skip_step : (MC).StepAtU ⟨.qkSkip,i,v⟩ := by
  let d : D := ⟨.qkSkip,i,v⟩
  refine crossing (d := d) (dst := afterQk d) Flow.code_2466 rfl trivial
    (by advances) (fun _ => rfl) ?_ (fun hi => inv_after hi.left hi.right)
  intro hi
  apply SegU.comp (b := 2500) (G := F d 2500)
  · exact SegU.of_seg (n := 1) (fun t ht => by dsimp only [d,code] at ht ⊢; seg_fp ht using rfl)
  · exact after_qk hp.sharedRange hi.left hi.right

set_option hygiene false in
local macro "pv_back" : tactic => `(tactic| (
  intro hi
  apply SegU.comp (b := 2447) (G := F d 2447)
  · apply SegU.of_seg (n := 1)
    intro t ht
    dsimp only [code] at ht ⊢
    seg_fp ht using rfl
  · exact loop_back hp.sharedRange hi.right.left hi.right.right))

theorem pv_skip_step : (MC).StepAtU ⟨.pvSkip,i,v⟩ := by
  let d : D := ⟨.pvSkip,i,v⟩
  refine crossing (d := d) (dst := iterNext d) Flow.code_2514 rfl trivial
    (by advances) (fun _ => rfl) ?_ (fun hi => inv_iter hi.right.left hi.right.right)
  pv_back

theorem pv_done_step : (MC).StepAtU ⟨.pvCommit2,i,v⟩ := by
  let d : D := ⟨.pvCommit2,i,v⟩
  refine crossing (d := d) (dst := iterNext d) Flow.code_2548 rfl
    (Code.guardTrue_factsFrom (show 15 ∈ Flow.live 2548 by decide) rfl)
    fires_tcCommit (fun _ => rfl) ?_ (fun hi => inv_iter hi.right.left hi.right.right)
  pv_back

end PTX.Kernels.InklingRelDecode.Proof.Mma

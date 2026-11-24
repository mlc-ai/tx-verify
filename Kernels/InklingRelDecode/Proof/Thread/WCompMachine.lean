-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompSound

@[expose] public section

/-!
# The worker thread as one site machine

The MMA warp's and the exit's obligations complete `stepAt` for every state of `code L g Q`
(`WCompBase.lean`); `sound` is the machine's `Code.Sound` and `machine` its `Machine.Sound`.

* The MMA warp's steps are `Mma.step`; its last event (`setmaxnreg.inc`) is `mma_return`, which
  needs the Tensor Memory base the warp carries to be the word of the registers it inherited
  (`Pro.val L g P 464 = b32 tm`, in the state's invariant) and the shared base to be a 32-bit
  number (`Pre.sharedRange`).
* The exit's `bar.sync 0` is `exit_bar_step`. The `ret` is the thread's last instruction: its
  event is the only one that fires without a continuation, so it has no step to prove.

## What the protocol layer owes

The machine does not follow the code at the places `next` returns `some none`; for each, the
layers above prove the fact that excludes it:

* the shuffle of `Worker.Site.shfl` returns the warp index;
* the Tensor Memory base word (`%r2`) read by the first load is a 32-bit word `tm` with
  `tm + 512 ≤ 2 ^ 16` where the role byte sends the thread to the MMA role (`roleStart`).

The dispatch follows every role byte on every warp; that the role is the warp's (the loader's (0)
for warp 6, the MMA role's (1) for warp 7, the idle role's (2) for warps 4 and 5, the exit (3) in
a later round) is the role table's value (`Interface.RoleReads`).

## Hypotheses of `sound`

`Pre Q L mem0` (the CTA's shape, the parameters the first instructions read, the shared base's
range) and `4 ≤ warpOf L g`, that is, the thread is of warp 4, 5, 6 or 7 of its CTA (the CTA
has 256 threads, `Pre.ntid`); `g` need not be a thread of the launch beyond that, since the
machine is about thread `g` of the launch `L`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro Pro.val Pro.table)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0} {e : Event} {t u : TState}
  {ins : Instr}

/-- An MMA state. -/
theorem stepAt_mma (hpre : Pre Q L mem0) (hsb : L.sharedBase < 2 ^ 32) (d : Mma.D) (P : Pro) :
    (code L g Q).StepAt (.mma d P) where
  site hi := Mma.site_ok hpre hi.1
  step := by
    intro t e u ins h hi hc hf
    obtain ⟨hm, hpro, hR, h463, h7, hw, ht⟩ := hi
    have h' : At t d.site.pc (Mma.facts L d) := h
    have hc' : kernel.code[d.site.pc]? = some ins := hc
    have hf' : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      obtain ⟨t', hr, ht', hi'⟩ := mma_return hR hpro ((hpro 463 (by decide)).trans h463)
        (baseW_eq hsb)
        ⟨hm, hpro, hR, h463, h7, hw, ht⟩ h' hc' hf'
      have hn : (code L g Q).next (.mma ⟨.setMaxRegInc, i, n, tm, pro⟩ P) e =
          some (some (.worker ⟨.loop, Worker.bumpPro P⟩)) := rfl
      exact .inl (.inr ⟨.worker ⟨.loop, Worker.bumpPro P⟩, t', hn, hr, good_worker ht' hi'⟩)
    · rcases Mma.step hpre d hm h' hc' hf' with
        (hn | ⟨d', t', hn, hr, ht', hi'⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by rw [next_mma_ne P hs, hn]; rfl))
      · obtain ⟨hp, htm⟩ := mma_next_pro hn
        exact .inl (.inr ⟨.mma d' P, t', by rw [next_mma_ne P hs, hn]; rfl, hr, ht',
          hi', fun r hr => (hp r hr).trans (hpro r hr), hR, by rw [htm]; exact h463,
          (hp 464 (by decide)).trans h7, hw, ht⟩)
      · exact .inr ⟨by rw [next_mma_ne P hs, hn]; rfl, hd⟩

/-- An exit state. -/
theorem stepAt_exit (x : ExitD) : (code L g Q).StepAt (.exit x) where
  site _ := by
    obtain ⟨s, P⟩ := x
    cases s
    · exact ⟨_, Flow.code_bar_37, rfl, trivial⟩
    · exact ⟨_, Flow.code_exit_0, rfl, trivial⟩
  step := by
    intro t e u ins h hi hc hf
    obtain ⟨s, P⟩ := x
    cases s
    · have h' : At t ExitSite.bar.pc (exitFacts L g ⟨.bar, P⟩) := h
      have hc' : kernel.code[ExitSite.bar.pc]? = some ins := hc
      have hf' : Fires ExitSite.bar.pc (eventTmpl asms L g t ins.op) e (some u) := hf
      obtain ⟨t', hr, ht', hi'⟩ := exit_bar_step hi h' hc' hf'
      exact .inl (.inr ⟨.exit ⟨.ret, P⟩, t', rfl, hr, good_exit ht' hi'⟩)
    · have hc' : kernel.code[ExitSite.ret.pc]? = some ins := hc
      have hf' : Fires ExitSite.ret.pc (eventTmpl asms L g t ins.op) e (some u) := hf
      obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_exit_0)
      simp [eventTmpl, Fires] at hf'

/-- **Every state of the worker thread's machine meets its obligation.** -/
theorem stepAt (hpre : Pre Q L mem0) (d : WSt) : (code L g Q).StepAt d := by
  have hsb : L.sharedBase < 2 ^ 32 := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    omega
  cases d with
  | worker w => exact stepAt_worker hsb w
  | idle d => exact stepAt_idle d
  | loader d P => exact stepAt_loader d P
  | mma d P => exact stepAt_mma hpre hsb d P
  | exit x => exact stepAt_exit x

/-- **The worker thread's machine is sound.** A thread of warp 4 or above of a launch that
satisfies `Pre` starts in the machine's first state (`Worker.start`), and every state meets its
obligation (`stepAt`). -/
theorem sound (hpre : Pre Q L mem0) (hw : 4 ≤ warpOf L g) : (code L g Q).Sound where
  start := by
    obtain ⟨t, hr, ht, hi⟩ := Worker.start (g := g) hpre hw
    exact ⟨t, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi⟩
  steps := stepAt hpre

/-- **The worker thread as one `Flow.Machine` with `Machine.Sound`**: the abstract states are
`WSt` (`.worker`, `.idle`, `.loader`, `.mma`, `.exit`) with the extra state `none`, which stands
for any state that performs an event (the machine uses it after an event whose continuation it
does not follow). -/
theorem machine_sound (hpre : Pre Q L mem0) (hw : 4 ≤ warpOf L g) :
    (code L g Q).toMachine.Sound :=
  (sound hpre hw).machine

end
end PTX.Kernels.InklingRelDecode.Proof.WComp

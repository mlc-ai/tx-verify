-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmEntryBase

@[expose] public section

/-! # The entry link from the prologue to the softmax region

The default-partition thread's last prologue event is the `barrier.sync 1` at pc 573; its hand-off
(`ProA.handoff`) puts the thread at pc 574 with the facts `ProA.exitFacts`. This file proves that
this thread is then in the softmax region's first state: the facts at pc 574 are
`Sm.factsAt L g 574 d₀` for the state `d₀ = d0 (entOf P L g dt)` (site `setMaxReg`, loop counter 0,
the running maximum `-inf` and sum 0), `Sm.Inv` holds there, and so the region's code machine
`Sm.code` starts at `d₀`.

* `entry`: the exit facts of the prologue are the first state's facts, and its invariant holds.
* `start`: a thread that reaches the prologue's exit facts satisfies `Code.Sound.start` of
  `Sm.code … d₀`.
* `ProA_to_Sm`: the same from the prologue's last event, composing `ProA.handoff`.

## Hypotheses (exactly)

* `hpre : Pre P L mem0`, `hg : g < L.threads`: the launch and a thread of it.
* `ha : ProA.ArgsOk L g dt.pro`: the thread is in the default partition and its inherited
  registers hold the launch's parameters (`ProA.argsOk_of_pre` derives it).
* `hs : dt.pro.w71 = P.splits`: the inherited `num_splits` register (`%r71`, from the common code).
* `hm : ProA.WordsMatch P (ProA.cta L g .z) dt`: the three words the prologue loaded are the
  request's `cu_seqlens_q[r]`, `cu_seqlens_q[r + 1]`, `seq_lens[r]`.
* `hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32))`: `%p3`, a register of the common code,
  that the prologue carries unchanged; the same fact as `Worker.Inv.p3`.
* `htm : dt.pro.tm < 2 ^ 32`: the Tensor Memory base the common code loaded is a 32-bit word
  (`Ent.Ok.tm`).
* `hn : 0 < P.nTok`: the launch has a query token; `Ent.Ok.blk` (every loop block number is below
  `2 ^ 31`) follows from `Pre.outRange` only with it (see `entOk`).

The first state's `Sm.D` holds no information the prologue does not pin down: of its table, the 29
registers live at pc 574 are in the prologue's table; the rest (`%rd193 …`, the position pairs,
the preloaded words, `m`, `l`) are defined by the region's own setup from them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.SmEntry
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {dt : ProA.Dat} {t u : TState}

/-- **The entry link.** A thread at pc 574 with the prologue's exit facts is at the softmax
region's first state `d0 (entOf P L g dt)` of its code machine, and the state satisfies the
region's invariant. -/
theorem entry (hpre : Pre P L mem0) (hg : g < L.threads) (ha : ProA.ArgsOk L g dt.pro)
    (hs : dt.pro.w71 = P.splits) (hm : ProA.WordsMatch P (ProA.cta L g .z) dt)
    (hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32))) (htm : dt.pro.tm + 512 ≤ 2 ^ 16)
    (hw : dt.w = b32 dt.pro.tm) (hn : 0 < P.nTok)
    (h : At t Flow.setMaxReg_1 (ProA.exitFacts L g dt)) :
    (Sm.code Sm.asms L g (d0 (entOf P L g dt))).AtD (d0 (entOf P L g dt)) t ∧
      Sm.Inv L g (d0 (entOf P L g dt)) := by
  refine ⟨?_, inv_d0 hpre hg ha hm htm hn⟩
  rw [← factsAt_eq hpre hg ha hs hm hp3 hw] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **`Code.Sound.start` of the softmax region**, from a thread that reaches the prologue's exit
facts. -/
theorem start (hpre : Pre P L mem0) (hg : g < L.threads) (ha : ProA.ArgsOk L g dt.pro)
    (hs : dt.pro.w71 = P.splits) (hm : ProA.WordsMatch P (ProA.cta L g .z) dt)
    (hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32))) (htm : dt.pro.tm + 512 ≤ 2 ^ 16)
    (hw : dt.w = b32 dt.pro.tm) (hn : 0 < P.nTok)
    (hreach : ∃ t, Relation.ReflTransGen (Tau kernel Sm.asms L g) {} t ∧
      At t Flow.setMaxReg_1 (ProA.exitFacts L g dt)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Sm.asms L g) {} t ∧
      (Sm.code Sm.asms L g (d0 (entOf P L g dt))).AtD (d0 (entOf P L g dt)) t ∧
      (Sm.code Sm.asms L g (d0 (entOf P L g dt))).inv (d0 (entOf P L g dt)) := by
  obtain ⟨t, hr, ht⟩ := hreach
  obtain ⟨h1, h2⟩ := entry hpre hg ha hs hm hp3 htm hw hn ht
  exact ⟨t, hr, h1, h2⟩

/-- **The prologue to the softmax region.** The thread was at the prologue's last site (`bar18`,
the `barrier.sync 1` at pc 573) with its data `dt` and the event fired: it is now at the softmax
region's first state. -/
theorem ProA_to_Sm {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (ha : ProA.ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : ProA.WordsMatch P (ProA.cta L g .z) dt)
    (hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32))) (htm : dt.pro.tm + 512 ≤ 2 ^ 16)
    (hw : dt.w = b32 dt.pro.tm) (hn : 0 < P.nTok) (h : ProA.AtS L g ⟨.bar18, dt⟩ t)
    (hc : kernel.code[Flow.bar_18]? = some ins)
    (hf : Fires Flow.bar_18 (eventTmpl ProA.asms L g t ins.op) e (some u)) :
    (Sm.code Sm.asms L g (d0 (entOf P L g dt))).AtD (d0 (entOf P L g dt)) u ∧
      Sm.Inv L g (d0 (entOf P L g dt)) :=
  entry hpre hg ha hs hm hp3 htm hw hn (ProA.handoff h hc hf)

end
end PTX.Kernels.InklingRelDecode.Proof.SmEntry

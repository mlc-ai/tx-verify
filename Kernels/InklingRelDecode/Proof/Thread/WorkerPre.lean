-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompAll
public import Kernels.InklingRelDecode.Proof.Thread.EvWTc
public import Lemmas.Flow.NotShfl
public import Lemmas.Flow.NotClc

@[expose] public section

/-!
# The worker's first four events

A worker thread (warps 4 to 7) starts with four events before its machine can stop following
it: `bar.sync 0`, the load of the Tensor Memory base word, `bar.sync 0` and the broadcast of the
warp index (`shfl.sync.idx` of `%r3` from lane 0). These are the sites of rank 0 to 3
(`Worker.preRank`). The facts here are what the layers above need to show, for any worker thread
and without knowing anything about its loaded values, that its first shuffle is its fourth event
and has its warp index as operand:

* `WComp.pre_next`: from a site of rank `r < 3` the successor is the site of rank `r + 1`, or
  `none` (the load of the base word faults);
* `WComp.pre_tgt`: a successor at a site of rank `r + 1` comes from the site of rank `r`, and no
  successor is at the site of rank 0;
* `WComp.pre_fires`: the events of the sites of rank below 3 are neither shuffles nor exits;
* `WComp.shfl_fires`: the event of the broadcast is a full-warp `shfl.sync.idx` whose operand is
  the thread's warp index.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow

/-- The rank of the worker's first four sites. -/
def preRank : Site → Option Nat
  | .bar0 => some 0
  | .ld0 => some 1
  | .bar1 => some 2
  | .shfl => some 3
  | _ => none

end PTX.Kernels.InklingRelDecode.Proof.Worker

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Worker (preRank)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {L : Launch} {g : Nat} {Q : Params}

/-- **The successor of a site of rank `r < 3`** is the site of rank `r + 1`, or `none`. -/
theorem pre_next {w : Worker.D} {r : Nat} {e : Event} (hr : preRank w.site = some r)
    (h3 : r < 3) : next L g (.worker w) e = none ∨
      ∃ w', next L g (.worker w) e = some (some (.worker w')) ∧
        preRank w'.site = some (r + 1) := by
  obtain ⟨s, P⟩ := w
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [preRank, Option.some.injEq, reduceCtorEq] at hr <;> subst hr <;>
    simp only [next, Worker.next] at *
  · exact Or.inr ⟨_, rfl, rfl⟩
  · cases k <;> simp only [Option.map_none, true_or]
    split <;> simp [preRank]
  · exact Or.inr ⟨_, rfl, rfl⟩
  · omega

/-- **A successor at a site of rank `r + 1` comes from the site of rank `r`.** -/
theorem pre_tgt {s : WSt} {w' : Worker.D} {r : Nat} {e : Event}
    (h : next L g s e = some (some (.worker w'))) (hr : preRank w'.site = some (r + 1)) :
    ∃ w, s = .worker w ∧ preRank w.site = some r := by
  obtain ⟨pc, k⟩ := e
  cases s with
  | worker w =>
    obtain ⟨s, P⟩ := w
    cases s
    case ldRole =>
      simp only [next] at h
      unfold dispatch at h
      split at h
      · rename_i d' _
        unfold roleStart at h
        split at h <;> (try split at h) <;> (try split at h) <;>
          simp only [Option.some.injEq, reduceCtorEq, WSt.worker.injEq] at h <;>
          (try subst h) <;> simp_all [preRank]
      · cases h
      · cases h
    all_goals
      simp only [next, Worker.next] at h
      (repeat' split at h) <;>
        simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq,
          WSt.worker.injEq] at h <;> (try subst h) <;>
        simp_all [preRank]
  | idle d =>
    simp only [next] at h
    split at h <;>
      (try (simp only [Option.some.injEq, WSt.worker.injEq] at h; subst h)) <;> simp_all [preRank]
  | loader d P =>
    simp only [next] at h
    split at h <;>
      (try (simp only [Option.some.injEq, WSt.worker.injEq] at h; subst h)) <;> simp_all [preRank]
  | mma d P =>
    simp only [next] at h
    split at h <;>
      (try (simp only [Option.some.injEq, WSt.worker.injEq] at h; subst h)) <;> simp_all [preRank]
  | exit x =>
    simp only [next] at h
    split at h <;> simp_all

/-- **No successor is at the site of rank 0.** -/
theorem pre_tgt_zero {s : WSt} {w' : Worker.D} {e : Event}
    (h : next L g s e = some (some (.worker w'))) : preRank w'.site ≠ some 0 := by
  obtain ⟨pc, k⟩ := e
  intro hr
  cases s with
  | worker w =>
    obtain ⟨s, P⟩ := w
    cases s
    case ldRole =>
      simp only [next] at h
      unfold dispatch at h
      split at h
      · unfold roleStart at h
        split at h <;> (try split at h) <;> (try split at h) <;>
          simp only [Option.some.injEq, reduceCtorEq, WSt.worker.injEq] at h <;>
          (try subst h) <;> simp_all [preRank]
      · cases h
      · cases h
    all_goals
      simp only [next, Worker.next] at h
      (repeat' split at h) <;>
        simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq,
          WSt.worker.injEq] at h <;> (try subst h) <;>
        simp_all [preRank]
  | idle d =>
    simp only [next] at h
    split at h <;>
      (try (simp only [Option.some.injEq, WSt.worker.injEq] at h; subst h)) <;> simp_all [preRank]
  | loader d P =>
    simp only [next] at h
    split at h <;>
      (try (simp only [Option.some.injEq, WSt.worker.injEq] at h; subst h)) <;> simp_all [preRank]
  | mma d P =>
    simp only [next] at h
    split at h <;>
      (try (simp only [Option.some.injEq, WSt.worker.injEq] at h; subst h)) <;> simp_all [preRank]
  | exit x =>
    simp only [next] at h
    split at h <;> simp_all

/-- **The events of the sites of rank below 3 are neither shuffles nor exits.** -/
theorem pre_fires {w : Worker.D} {r : Nat} (hr : preRank w.site = some r) (h3 : r < 3)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc (.worker w)]? = some ins)
    (hf : Fires (pc (.worker w)) (eventTmpl asms L g t ins.op) e o) :
    Execution.isShfl e = false ∧ e.kind ≠ .exit := by
  have hop : ins.op.isShfl = false ∧ ins.op ≠ .ret ∧ ins.op ≠ .exit := by
    obtain ⟨s, P⟩ := w
    cases s <;> simp only [preRank, Option.some.injEq, reduceCtorEq] at hr <;> subst hr <;>
      simp only [pc, Worker.Site.pc] at hc
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
      exact ⟨rfl, by simp, by simp⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
      exact ⟨rfl, by simp, by simp⟩
    · omega
  refine ⟨?_, ?_⟩
  · cases hs : Execution.isShfl e
    · rfl
    · have := fires_shfl_op hf hs
      rw [hop.1] at this
      cases this
  · intro hk
    rcases fires_exit_op hf hk with h | h
    · exact hop.2.1 h
    · exact hop.2.2 h

/-- **The broadcast of the warp index**: the event of the worker's `shfl` site is a full-warp
`shfl.sync.idx` from lane 0 whose operand is the thread's warp index. -/
theorem shfl_fires {P : Loader.Pro} {t u : TState} {ins : Instr} {e : Event}
    (ha : (code L g Q).AtD (.worker ⟨.shfl, P⟩) t)
    (hc : kernel.code[pc (.worker ⟨.shfl, P⟩)]? = some ins)
    (hf : Fires (pc (.worker ⟨.shfl, P⟩)) (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ recv ok, e = ⟨pc (.worker ⟨.shfl, P⟩), .shfl .idx (b32 (warpOf L g)) 0 31 recv ok⟩ := by
  have hpc : pc (.worker ⟨.shfl, P⟩) = 17 := rfl
  have hr : t.regs 464 = some (b32 (warpOf L g)) := by
    have hl : (464 : Nat) ∈ Flow.live 17 := by decide +kernel
    have hm := holds_mem ha.2.2.2.2 (Flow.mem_factsFrom hl)
    rw [hm]
    rfl
  rw [hpc] at hc hf ⊢
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  exact fires_shfl_idx (p := none) hr hf hsh

end
end PTX.Kernels.InklingRelDecode.Proof.WComp

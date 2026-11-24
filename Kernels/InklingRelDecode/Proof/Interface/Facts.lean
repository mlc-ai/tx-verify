-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.OutputFrame
public import Kernels.InklingRelDecode.Proof.Interface.Premises
public import Kernels.InklingRelDecode.Proof.Interface.Bridge

@[expose] public section

/-!
# `ThreadFacts`: what the thread layer says about every consistent execution

`ThreadFacts Q L mem0 X` collects, for an execution `X` of the kernel's launch `L` with the
parameters `Q`, what the layers above the thread layer consume. Every statement is about the
abstract states of the thread machines (`Frame.stateAt (code L Q) X g k`, `TSt`), never about
program counters or registers. `threadFacts` proves it from `Pre`, the softmax region's
obligations (`DComp.SmObligations`) and the machines' premises (`Premises`).

* `sound`, `tracked`, `tracked_select`, `ub_stop`: each launched thread's machine is sound and
  follows the thread;
  undefined behaviour comes only after the machine stopped (`Premises.tmplOk`).
* `reach`: the meaning of the abstract state before each event (`TReach`): the prologue's numbers
  and the epilogue's registers are the launch's.
* `global_wr`: every global write is an epilogue store of `OPart` or `LsePart`, of the word and at
  the footprint of `Spec` (`Output.lean`).
* `post_frame`: `Post`'s last conjunct, from every global write being inside an output array
  (`OutputFrame.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The softmax region's obligations of every default-partition thread of the launch. -/
def SmOb (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ g < L.threads, IsDefault L g → DComp.SmObligations Q L mem0 g

/-- **The thread layer's facts about an execution.** -/
structure ThreadFacts (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  /-- Every launched thread's machine is sound. -/
  sound : ∀ g < L.threads, (threadCode L g Q).Sound
  /-- Every launched thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L Q) X
  /-- Every launched thread is followed by the bound layer's machine family
  (`Bound.threadCode L Q`, which unfolds to `selectCode L Q`): this is its `htr`. -/
  tracked_select : Frame.Tracked (selectCode L Q) X
  /-- Undefined behaviour comes after the machine stopped. -/
  ub_stop : ∀ {g k pc : Nat} {f : Fault}, g < L.threads →
    X.get (g, k) = some ⟨pc, .ub f⟩ → St Q L X g k = none ∨ St Q L X g k = some none
  /-- The meaning of the abstract state before each event of a launched thread. -/
  reach : ∀ {g k : Nat} {s : TSt}, g < L.threads → St Q L X g k = some (some s) →
    TReach Q L g s
  /-- Every generic write to global memory is an epilogue store of a valid row, of the word and at
  the footprint `Spec` gives (`oLoc`, `lseLoc`). -/
  global_wr : ∀ {g k pc : Nat} {a : Acc} {bs : List Byte}, g < L.threads →
    X.get (g, k) = some ⟨pc, .wr a bs⟩ → a.loc.space = .global →
    ∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ pc = Epi.evPc d.site ∧
      Epi.Means Q L g d.pr ∧ d.pr.rv = true ∧
      ((∃ j : Fin 64, d.site = .stO j ∧ ∃ v, storeValue 32 (d.word j) = .ok v ∧
          bs = v.toBytes ∧ a = EvD.wordAcc (oLoc Q (Epi.outSplit L g) (Epi.outToken Q L g)
            (Epi.outHead L g) (Epi.outCol0 L g + j.val))) ∨
        (d.site = .stLse ∧ ∃ v, storeValue 32 d.pr.lseWord = .ok v ∧ bs = v.toBytes ∧
          a = EvD.wordAcc (lseLoc Q (Epi.outSplit L g) (Epi.outToken Q L g)
            (Epi.outHead L g))))
  /-- The loader's counter bounds (`Premises.ldRng`). -/
  ldRng : LdRng Q L X
  /-- Every state is in its warp's role (`Premises.roleWarp`). -/
  roleWarp : RoleWarps Q L X
  /-- Every global write covers a byte of `OPart` or `LsePart` only. -/
  write_in_arrays : ∀ {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte},
    X.MemWrites w a bs → a.loc.space = .global → ∀ {l : Loc}, a.Covers l →
      (Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) ∨
        (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q)

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every thread's machine is sound**, from `Pre` and the softmax region's obligations. -/
theorem sound_all (hpre : Pre Q L mem0) (hso : SmOb Q L mem0) :
    ∀ g < L.threads, (threadCode L g Q).Sound :=
  fun g hg => sound hpre hg (hso g hg)

/-- **The thread layer's facts for every consistent execution.** -/
theorem threadFacts (hpre : Pre Q L mem0) (hso : SmOb Q L mem0)
    (hX : Consistent L kernel asms mem0 X) (hP : Premises Q L X) : ThreadFacts Q L mem0 X := by
  have hS := sound_all hpre hso
  have ht := tracked_of_premises hP
  exact
    { sound := hS
      tracked := ht
      tracked_select := tracked_select ht
      ub_stop := fun hg h => ub_stop hS hP hX hg h
      reach := fun hg h => treach_stateAt hpre hg h
      global_wr := fun hg he hsp => global_wr_state hpre hX hS ht hg he hsp
      ldRng := hP.ldRng
      roleWarp := hP.roleWarp
      write_in_arrays := fun hw hsp _ hc => global_write_in_arrays hpre hX hS ht hw hsp hc }

/-- **The frame of `Post`**: a global byte outside both output arrays keeps its launch
content. -/
theorem ThreadFacts.post_frame (hf : ThreadFacts Q L mem0 X) {m : FinalMem}
    (hfin : IsFinal L mem0 X m) :
    ∀ l, l.space = .global → ¬ (Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) →
      ¬ (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q) → m l = mem0 l := by
  intro l hl ho hs
  apply hfin.unwritten
  intro w a bs hw hc
  have hsp : a.loc.space = .global := hc.1.symm.trans hl
  rcases hf.write_in_arrays hw hsp hc with h | h
  · exact ho h
  · exact hs h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

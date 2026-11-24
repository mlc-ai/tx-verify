-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Reach
public import Lemmas.Flow.UbStop
public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure

@[expose] public section

/-!
# The premises of the thread machines

A thread machine follows its thread only where the event is one it can continue from. The
machines' `next` returns `some none` ("not followed") at the places listed below, and `none` ("the
thread is dead") where the code faults. The thread layer does not prove that these do not happen:
they are facts about what the memory returns and what the other threads wrote, which the protocol
layer proves. Each machine has one `Premises` structure; its one field is what `Frame.tracked_of`
needs, stated at the abstract states of an execution (`Frame.stateAt`).

**Worker machine** (`WComp.next`; the development notes, "S5 premises of the worker thread
composition"):

* the shuffle of `Worker.Site.shfl` returns the warp index;
* the role byte read at `Worker.Site.ldRole` is below 4, and is the loader's (0) for warp 6, the
  MMA warp's (1) for warp 7, the idle role's (2) for warps 4 and 5 (any warp may read 3: exit);
* the Tensor Memory base word read at `Worker.Site.ld0` is a 32-bit word `tm`, with
  `tm + 512 < 2 ^ 32` for warp 7;
* the MMA warp's read of `num_iters` is a word of the shape `Mma.next` names; the MMA warp's
  shuffles return 7. The loader follows every loaded word (`Loader.next`); the counter bounds of its
  states (`Loader.Rng`) are the field `ldRng`, a consequence of the loaded words being the
  launch's.

**Default-partition machine** (`DComp.next`):

* the common start's Tensor Memory word is a 32-bit word below `2 ^ 32` and its shuffle returns the
  warp index (`DStart.next`);
* the prologue's reads of `cu_seqlens_q`, `seq_lens` and the block table are 32-bit words, the
  three words satisfy `ProA.WordsOk` and `ProA.WordsMatch` (the request's own), the query loads are
  16-bit values, and its shuffles return the warp index (`ProA.next`, `DComp.proNext`;
  the development notes, "thread-layer gaps": `ProA` loaded words);
* the softmax region's bias loads are `bf16` numbers, its shuffle at `shfl4` returns the warp
  index, the S-tile load returns 64 four-byte words (`Sm.next`);
* the epilogue's shuffle returns the warp index and its Tensor Memory load returns 64 words
  (`Epi.next`);
* the softmax region's open obligations (`DComp.SmObligations`) are separate.

**Undefined behaviour** (`TmplOk`): no state fires an event template that is undefined behaviour.
The machines prove the continuing events of every state (`StepAt.step`) but not that the template
is never `.ub` (the row of "thread-layer gaps" for `Code.TmplOk`); until they do it is a premise,
and
`ub_stop` is the consequence the layers above use.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The premises of the worker machine** along an execution: it follows every event of a
worker thread (the cases listed in the header). -/
structure WPremises (Q : Params) (L : Launch) (X : Execution) : Prop where
  follows : ∀ {g k : Nat} {s : WComp.WSt} {e : Event}, g < L.threads →
    (X.tr g)[k]? = some e → Frame.stateAt (code L Q) X g k = some (some (.w s)) →
      WComp.next L g s e ≠ some none

/-- **The premises of the default-partition machine** along an execution. -/
structure DPremises (Q : Params) (L : Launch) (X : Execution) : Prop where
  follows : ∀ {g k : Nat} {s : DComp.St} {e : Event}, g < L.threads →
    (X.tr g)[k]? = some e → Frame.stateAt (code L Q) X g k = some (some (.d s)) →
      DComp.next L g Q s e ≠ some none

/-- **The loader's counter bounds along an execution**: every loader state of a launched thread
has the counters below `2 ^ 31` and, in the loop, the counter below `num_iters` (`Loader.Rng`).
The machine follows every loaded word; the bounds hold because the words it loads are the
launch's (`Interface.ldRng_of_reads`). -/
def LdRng (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Loader.D} {P : Loader.Pro}, g < L.threads →
    Frame.stateAt (code L Q) X g k = some (some (.w (.loader d P))) → Loader.Rng d

/-- The warp of a thread, and the role the warp has: no role state is at a thread of another
warp. -/
def RoleWarp (L : Launch) (g : Nat) : TSt → Prop
  | .d _ => True
  | .w s => Ledger.roleWarp (g % L.block / 32) s

/-- **The roles by warp along an execution**: every state of a thread's machine before one of its
events (or at its end) is in its warp's role: the idle role in warps 4 and 5, the loader in warp
6, the MMA role in warp 7. The dispatch follows every role byte on every warp; this holds because
the bytes the workers read are the role table's (`Interface.roleWarp_of_reads`). -/
def RoleWarps (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {s : TSt}, k ≤ (X.tr g).length →
    Frame.stateAt (code L Q) X g k = some (some s) → RoleWarp L g s

/-- **The premises of the thread layer**: the two machines' premises, that no state's template is
undefined behaviour, the loader's counter bounds and the roles by warp. -/
structure Premises (Q : Params) (L : Launch) (X : Execution) : Prop where
  worker : WPremises Q L X
  default : DPremises Q L X
  tmplOk : ∀ g < L.threads, (threadCode L g Q).TmplOk
  ldRng : LdRng Q L X
  roleWarp : RoleWarps Q L X

theorem next_d_ne {s : DComp.St} {e : Event} (h : DComp.next L g Q s e ≠ some none) :
    (threadCode L g Q).next (.d s) e ≠ some none := by
  intro hh
  apply h
  cases h1 : DComp.next L g Q s e with
  | none => simp [threadCode, TSt.next, h1] at hh
  | some o =>
    cases o with
    | none => rfl
    | some a => simp [threadCode, TSt.next, h1] at hh

theorem next_w_ne {s : WComp.WSt} {e : Event} (h : WComp.next L g s e ≠ some none) :
    (threadCode L g Q).next (.w s) e ≠ some none := by
  intro hh
  apply h
  cases h1 : WComp.next L g s e with
  | none => simp [threadCode, TSt.next, h1] at hh
  | some o =>
    cases o with
    | none => rfl
    | some a => simp [threadCode, TSt.next, h1] at hh

/-- **Every thread is followed by its machine**, from the premises. -/
theorem tracked_of_premises (hP : Premises Q L X) : Frame.Tracked (code L Q) X := by
  refine Frame.tracked_of ?_
  intro g k d e hg he hσ
  cases d with
  | d s => exact next_d_ne (hP.default.follows hg he hσ)
  | w s => exact next_w_ne (hP.worker.follows hg he hσ)

/-- **Undefined behaviour comes after the machine stopped**: an undefined-behaviour event of a
thread of an execution comes after an event its machine does not follow or cannot continue
from. -/
theorem ub_stop (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hP : Premises Q L X)
    (hX : Consistent L kernel asms mem0 X) {g k pc : Nat} {f : Fault} (hg : g < L.threads)
    (h : X.get (g, k) = some ⟨pc, .ub f⟩) :
    Frame.stateAt (code L Q) X g k = none ∨ Frame.stateAt (code L Q) X g k = some none :=
  Code.ub_stopped (hS g hg) (hP.tmplOk g hg) (hX.thr g hg) h

/-- **No undefined behaviour while every event is followed**: if every thread's machine continues
from every state at every event (no `none` successor), no thread has an undefined-behaviour
event. -/
theorem no_ub (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hP : Premises Q L X)
    (hX : Consistent L kernel asms mem0 X)
    (hfault : ∀ {g k : Nat} {s : TSt} {e : Event}, g < L.threads → (X.tr g)[k]? = some e →
      (X.tr g)[k + 1]? ≠ none →
      Frame.stateAt (code L Q) X g k = some (some s) → (threadCode L g Q).next s e ≠ none) :
    ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, h⟩
  have hg := Frame.lt_of_get hX h
  have ht := tracked_of_premises hP
  rcases ub_stop hS hP hX hg h with hn | hn
  · obtain ⟨i, d, hi, h1, h2⟩ := Frame.first_stop ht hg hn
    have hev : ∃ e, (X.tr g)[i]? = some e := by
      by_contra hne
      push Not at hne
      have : (X.tr g).length ≤ i := by
        by_contra hl
        exact hne _ (List.getElem?_eq_getElem (by omega))
      have h3 := Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) this
      have h4 := Frame.stateAt_of_le (C := code L Q) (X := X) (g := g)
        (show (X.tr g).length ≤ i + 1 by omega)
      rw [h4] at h2
      rw [h3] at h1
      rw [h1] at h2
      cases h2
    obtain ⟨e, he⟩ := hev
    have := Frame.stateAt_succ (C := code L Q) (X := X) (g := g) he
    rw [h2, h1] at this
    simp only [Option.bind_some] at this
    have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp h).1
    have hfol : (X.tr g)[i + 1]? ≠ none := by
      rw [List.getElem?_eq_getElem (by omega)]
      simp
    exact hfault hg he hfol h1 this.symm
  · exact ht g k hg hn

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

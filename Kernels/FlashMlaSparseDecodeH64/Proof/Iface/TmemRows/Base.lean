-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # The Tensor Memory rows: vocabulary

The words the rows of `Iface/TmemRows/<Role>.lean` are written in; lanes and pc regions are the
mbarrier rows' (`MbarRow.warp`, `MbarRow.<Role>At`).

* **The row.** `TcRow L X At Ok`: a `tcgen05` event (`.tc c`) of a launched lane `g` at a pc of
  its role (`At g pc`) has the role's form `Ok g e`. Only three roles have `tcgen05` sites: the
  startup (the allocation, pc 91, and the relinquishment, pc 96), warpgroup 0 (loads, stores,
  their waits, fences, the deallocation at pc 1840) and the MMA warp (fences, copies, MMAs,
  commits); the others' rows say `False`.
* **The recorded form.** A row states the event Core RECORDS, read off Core's step templates
  (`Lemmas/Flow/Resource.lean`, `Lemmas/Flow/TmemOperands.lean`, `Lemmas/Flow/TcAddr.lean`)
  through the roles' shape tables, not the operand text: the allocation records
  `.resource .one (some dst) (.alloc 512)`, the relinquishment `.resource .one none .relinquish`
  (`fires_tcRelinquish_some`), the deallocation `.resource .one none (.dealloc a n)` with `a`, `n`
  the values its registers read (`fires_tcDealloc_at`; here the moved constants 0 and 512,
  `dealloc_operands`), a `32x32b` load or store `.ld a vals .s32x32b` / `.st a vals .s32x32b` with
  `a` the column its address register holds.
* **The static check.** `regionOk code lo hi sites` decides that the `tcgen05` instructions of
  `[lo, hi)` (`tcOp`) are exactly at the pcs of `sites`, each of its tag's instruction form
  (`Tag.ok`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace TmemRow

/-- Whether an operation is a `tcgen05` instruction. -/
def tcOp : Op → Bool
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcMma .. | .tcCommit .. | .tcFenceBefore
  | .tcFenceAfter | .tcLd .. | .tcWaitLd | .tcSt .. | .tcWaitSt | .tcCp .. | .tcShift .. => true
  | _ => false

/-- The instruction form of a `tcgen05` site. -/
inductive Tag where
  | alloc | relinq | dealloc | ld | waitLd | st | waitSt | fenceB | fenceA | cp | mma | commit
  deriving DecidableEq, Repr

/-- Whether operation `op` has the form of tag `t` (group one; loads and stores `32x32b`). -/
def Tag.ok : Tag → Op → Bool
  | .alloc, .tcAlloc .one .. => true
  | .relinq, .tcRelinquish .one => true
  | .dealloc, .tcDealloc .one .. => true
  | .ld, .tcLd _ _ .s32x32b none => true
  | .waitLd, .tcWaitLd => true
  | .st, .tcSt _ _ .s32x32b => true
  | .waitSt, .tcWaitSt => true
  | .fenceB, .tcFenceBefore => true
  | .fenceA, .tcFenceAfter => true
  | .cp, .tcCp .one .s128x256b _ _ none => true
  | .mma, .tcMma _ => true
  | .commit, .tcCommit .one .. => true
  | _, _ => false

/-- **The `tcgen05` sites of `[lo, hi)` are exactly `sites`**, each of its tag's form. -/
def regionOk (code : List Instr) (lo hi : Nat) (sites : List (Nat × Tag)) : Bool :=
  code.zipIdx.all (fun x => !(lo ≤ x.2 && x.2 < hi && tcOp x.1.op) ||
      (sites.lookup x.2).any (fun t => t.ok x.1.op)) &&
    sites.all (fun s => lo ≤ s.1 && s.1 < hi && (code[s.1]?).any (fun i => s.2.ok i.op))

/-- **The row of a role**: a `tcgen05` event of a launched lane `g` at a pc of the role
(`At g pc`) has the role's form `Ok g e`. -/
def TcRow (L : Launch) (X : Execution) (At : Nat → Nat → Prop) (Ok : Nat → Event → Prop) :
    Prop :=
  ∀ {g k : Nat} {e : Event} {c : TcKind}, g < L.threads → X.get (g, k) = some e → At g e.pc →
    e.kind = .tc c → Ok g e

/-- A paired Tensor Memory operation (allocation, relinquishment, deallocation) of group `grp`. -/
def Res (e : Event) (grp : CtaGroup) (act : Tmem.Request) : Prop :=
  ∃ dst, e.kind = .tc (.resource grp dst act)

end TmemRow

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

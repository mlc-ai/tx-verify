-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # The named-barrier classification rows: vocabulary

The words the rows of `Iface/BarRows/<Role>.lean` are written in; lanes and pc regions are the
mbarrier rows' (`MbarRow.warp`, `MbarRow.<Role>At`).

* **Uses.** `Cta e`: the startup's `bar.sync 0` (no thread count); `Sync e id n`: a `bar.sync` or
  `barrier.sync` of barrier `id` with `n` threads; `Everyone e pc`: `everyone_sync` (barrier 12,
  all 384 threads of the CTA, recorded without a count) at `pc`. The ids and counts of every site
  but pc 97 are registers: the row states their values, and its producer proves them (the moves
  are in `Data/Barriers.lean`).
* **The recorded count.** A row states the count the EVENT carries, not the code's operand:
  Core's `barTmpl` records an operand count `n` as `recCnt L.block n`, i.e. `none` when `n = 0`
  or `n = L.block` (384 here) and `some n` otherwise (`barTmpl_cnt`). So `everyone_sync`'s 384 is
  `none`, `wg0_sync`'s 128 is `some 128`, the warp-pair barriers' 64 are `some 64`
  (`recCnt_everyone`, `recCnt_nine`, `recCnt_pair`).
* **The static check.** `regionOk code lo hi sites` decides that the instructions of `[lo, hi)`
  that `barOp` selects (`bar.sync`, `barrier.sync`, `bar.arrive`) are exactly the unguarded
  `sites`, each of its shape (`Shape.ok`: the immediate `bar.sync 0`, or a register id and count
  with the site's aligned flag). It is `MbarRow.regionOk` with `barOp` for `mbarOp`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace BarRow

/-- The startup's `bar.sync 0` of the whole CTA, without a thread count. -/
def Cta (e : Event) : Prop := e.kind = .bar 0 none .sync

/-- A `bar.sync` or `barrier.sync` of barrier `id` with `n` threads. -/
def Sync (e : Event) (id n : Nat) : Prop := e.kind = .bar id (some n) .sync

/-- `everyone_sync` (barrier 12, all 384 threads of the CTA: recorded without a count,
`recCnt_everyone`) at `pc`. -/
def Everyone (e : Event) (pc : Nat) : Prop := e.pc = pc ∧ e.kind = .bar 12 none .sync

/-- The count a barrier event records for the operand count `n` in a CTA of `block` threads. -/
def recCnt (block n : Nat) : Option Nat := if n = 0 ∨ n = block then none else some n

/-- **The template records `recCnt`**: a valid `bar.sync` with a count operand reading `n`. -/
theorem barTmpl_cnt {L : Launch} {g : Nat} {t : TState} {a b : Opnd} {id n : BitVec 64}
    (ha : readBits L g t 32 a = .ok id) (hb : readBits L g t 32 b = .ok n)
    (hid : id.toNat < 16) (hn : n.toNat % 32 = 0) :
    barTmpl L g t a (some b) .sync = .bar id.toNat (next t) (recCnt L.block n.toNat) .sync := by
  simp only [barTmpl, ha, hb, recCnt, show ¬ 16 ≤ id.toNat by omega, ↓reduceIte, hn,
    reduceCtorEq, false_imp_iff, and_self]

/-- The shape of a barrier site's operation. -/
inductive Shape where
  /-- `bar.sync 0`, aligned, without a count. -/
  | cta
  /-- `bar.sync` (`aligned`) or `barrier.sync` (not `aligned`) with a register id and count. -/
  | sync (aligned : Bool)
  deriving DecidableEq, Repr

/-- Whether operation `op` has shape `s`. -/
def Shape.ok : Shape → Op → Bool
  | .cta, .barSync (.imm 0) a => a
  | .sync a, .barSyncN (.reg _) (.reg _) a' => a == a'
  | _, _ => false

/-- **The barrier sites of `[lo, hi)` are exactly `sites`**, each unguarded and of its shape. -/
def regionOk (code : List Instr) (lo hi : Nat) (sites : List (Nat × Shape)) : Bool :=
  code.zipIdx.all (fun x => !(lo ≤ x.2 && x.2 < hi && barOp x.1.op) ||
      (x.1.guard.isNone && (sites.lookup x.2).any (fun s => s.ok x.1.op))) &&
    sites.all (fun s => lo ≤ s.1 && s.1 < hi &&
      (code[s.1]?).any (fun i => barOp i.op && s.2.ok i.op))

/-- **The row of a role whose one barrier site is `everyone_sync` at `pc`**: a barrier event of a
lane of the role (`At`) is that site's. -/
def EveryoneRow (L : Launch) (X : Execution) (At : Nat → Nat → Prop) (pc : Nat) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → At g e.pc →
    Execution.isBar e = true → Everyone e pc

end BarRow

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

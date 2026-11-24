-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SrOrder

@[expose] public section

/-!
# The coordinates of the Tensor Memory writers and readers of one CTA

The events that write or read the Tensor Memory of the S/P/O handshake, each with its place in
the loop, in the terms of the handshake's own counts (no program counter, no register number):

* `QkAt x i`: an MMA of the lane `cm` that is a QK MMA of block `i` (`EvW.QkIssue`: its columns lie
  in `S (i % 2)`), with at most `i / 2` commits to `s_ready (i % 2)` before it, at least `i / 2`
  successful polls of `p_ready (i % 2)` and at least `i - 1` commits to `o_done` before it;
* `PvAt x m`: an MMA of the lane that is PV MMA `j < 8` of block `m` (`EvW.PvIssue` with the loop
  counter `m + 1`: its results lie in `O`, its A operand in `P (m % 2)`), with at most `m / 2 + 1`
  commits to `s_ready (m % 2)` before it, `below2 b (m + 1)` successful polls of `p_ready b` for
  both buffers and at most `m` commits to `o_done`;
* `PSt`, `OSt`: a `tcgen05.st` of a softmax thread, the `P` store of block `i` (32 words,
  half-split 32, at `tm + 128 (i % 2)`) or the rescale store of iteration `i ≥ 1` (64 words,
  half-split 64, at `tm + 256`), with the `StGate` of its iteration.

`Lane` collects them for one CTA: the MMAs and the `tcgen05.st`s of the CTA have such coordinates.
These are statements about the events of the roles' machines (the counts of `SOMmaExec`,
`SOSmExec`, the event shapes of `EvW`/`Sm`), the rows of "thread-layer gaps" for `Sr`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InP InO TmOk below2)

noncomputable section

variable {L : Launch} {X : Execution}

/-- **A QK MMA of block `i`** (see the file header). -/
structure QkAt (L : Launch) (X : Execution) (c cm tm : Nat) (x : EvId) (i : Nat) : Prop where
  thread : x.1 = cm
  issue : ∃ j pc e, X.get x = some e ∧ EvW.QkIssue L c tm i j pc e
  sCommits : ((X.tr cm).take x.2).countP (commitsTo (sReady L c (i % 2))) ≤ i / 2
  pPolls : i / 2 ≤ okPolls (pReady L c (i % 2)) ((X.tr cm).take x.2)
  oCommits : i - 1 ≤ ((X.tr cm).take x.2).countP (commitsTo (oDone L c))

/-- **A PV MMA of block `m`** (the PV half of loop iteration `m + 1`). -/
structure PvAt (L : Launch) (X : Execution) (c cm tm : Nat) (x : EvId) (m : Nat) : Prop where
  thread : x.1 = cm
  issue : ∃ j pc e, j < 8 ∧ X.get x = some e ∧ EvW.PvIssue L c tm (m + 1) j pc e
  sCommits : ((X.tr cm).take x.2).countP (commitsTo (sReady L c (m % 2))) ≤ m / 2 + 1
  pPolls : ∀ b < 2, below2 b (m + 1) ≤ okPolls (pReady L c b) ((X.tr cm).take x.2)
  oCommits : ((X.tr cm).take x.2).countP (commitsTo (oDone L c)) ≤ m

/-- **The `P` store of block `i`** by the softmax thread `t`: 32 words at `tm + 128 (i % 2)` plus
the thread's warp lane field, half-split 32, with the gate of `s_ready (i % 2)` and use `i / 2`.
Before the store the thread has made `below2 b (i + 1)` successful polls of `s_ready b` for both
buffers (the polls of the iterations up to `i`), so the coordinate `i` is the thread's loop
counter at the store (`Kk.pst_iter`). -/
structure PSt (L : Launch) (X : Execution) (c p0 : Nat) (Soft : Nat → Prop) (tm t sk i : Nat)
    (a : Nat) (vals : List Value) (sh : TcShape) : Prop where
  gate : StGate L X c p0 Soft t sk (sReady L c (i % 2)) (i / 2) (i % 2) (i / 2)
  /-- The event at `sk` is the `tcgen05.st` the coordinates describe. -/
  event : X.TSt (t, sk) a vals sh
  polls : ∀ b < 2, okPolls (sReady L c b) ((X.tr t).take sk) = below2 b (i + 1)
  shape : sh = .s16x32bx2 32 ∧ vals.length = 32 ∧ ∃ w, a = tm + 128 * (i % 2) + w * 2 ^ 21

/-- **The rescale store of iteration `i ≥ 1`** by the softmax thread `t`: 64 words at `tm + 256`
plus the thread's warp lane field, half-split 64, with the gate of `o_done` after `i - 1` earlier
polls, before thread 0's arrival on `p_ready (i % 2)` of use `i / 2`. The thread has made exactly
`i` successful polls of `o_done` before the store (the iteration's own poll is the last one), so
the coordinate `i` is the thread's loop counter at the store (`Rr.ostIter_of`). -/
structure OSt (L : Launch) (X : Execution) (c p0 : Nat) (Soft : Nat → Prop) (tm t sk i : Nat)
    (a : Nat) (vals : List Value) (sh : TcShape) : Prop where
  gate : StGate L X c p0 Soft t sk (oDone L c) (i - 1) (i % 2) (i / 2)
  one_le : 1 ≤ i
  /-- The event at `sk` is the `tcgen05.st` the coordinates describe. -/
  event : X.TSt (t, sk) a vals sh
  polls : okPolls (oDone L c) ((X.tr t).take sk) = i
  shape : sh = .s16x32bx2 64 ∧ vals.length = 64 ∧ ∃ w, a = tm + 256 + w * 2 ^ 21

/-- **The Tensor Memory lane of one CTA `c`**: the committing MMA lane `cm`, thread 0 `p0` of the
default partition, the Tensor Memory base `tm` and the softmax threads. -/
structure Lane (L : Launch) (X : Execution) (c cm p0 tm : Nat) (Soft : Nat → Prop) : Prop where
  tmOk : TmOk tm
  cm_ok : cm < L.threads ∧ cm / L.block = c
  /-- The MMA lane's polls of `p_ready` are acquire polls. -/
  pAcq : ∀ {b j pc p : Nat} {acq : Bool} {sc : MbarScope}, b < 2 →
    X.get (cm, j) = some ⟨pc, .wait (pReady L c b) p true acq sc⟩ → acq = true
  /-- Thread 0's polls of `s_ready` are acquire polls. -/
  sAcq : ∀ {b j pc p : Nat} {acq : Bool} {sc : MbarScope}, b < 2 →
    X.get (p0, j) = some ⟨pc, .wait (sReady L c b) p true acq sc⟩ → acq = true
  /-- Every MMA of the CTA is the lane's and a QK or PV MMA of its block. -/
  mma : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c →
    (∃ i, QkAt L X c cm tm x i) ∨ ∃ m, PvAt L X c cm tm x m
  /-- Every `tcgen05.st` of a thread of the CTA is a softmax thread's `P` store or rescale store. -/
  st : ∀ {t sk a : Nat} {vals : List Value} {sh : TcShape}, X.TSt (t, sk) a vals sh →
    t / L.block = c → (∃ i, PSt L X c p0 Soft tm t sk i a vals sh) ∨
      ∃ i, OSt L X c p0 Soft tm t sk i a vals sh

/-- An MMA of the CTA is the lane's. -/
theorem Lane.mma_thread {c cm p0 tm : Nat} {Soft : Nat → Prop} (l : Lane L X c cm p0 tm Soft)
    {x : EvId} (hx : IsMma X x) (hxc : x.1 / L.block = c) : x.1 = cm := by
  rcases l.mma hx hxc with ⟨i, h⟩ | ⟨m, h⟩
  · exact h.thread
  · exact h.thread

/-! ### The cells of the read side -/

/-- **The accumulator-read cells of a QK MMA of block `i`** lie in `S (i % 2)` of the CTA. -/
theorem qk_readCells {cta tm i j pc : Nat} {e : Event} (hT : TmOk tm)
    (hq : EvW.QkIssue L cta tm i j pc e) {x : EvId} (hx : X.get x = some e) {cell : Cell}
    (hc : X.MmaReadCell x cell) : InS tm (i % 2) cell.column ∧ cell.cta = cta := by
  obtain ⟨da, db, dsc, hd, -, -, rfl⟩ := hq
  obtain ⟨d, s, mask, row, col, ⟨pc', hget⟩, hw⟩ := hc
  rw [hx] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hget
  obtain ⟨-, rfl, rfl, -, -⟩ := hget
  obtain ⟨hm, hn, hws, hg⟩ := SO.qk_desc hd
  obtain ⟨hcol, hcl, -, hcta⟩ := SO.resultCell_cols (s := ⟨dsc, da, db, cta, cta, none, {}⟩)
    hm hg hws hn hw
  have hb : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hmod : (tm + 128 * (i % 2)) % 2 ^ 16 = tm + 128 * (i % 2) := by
    apply Nat.mod_eq_of_lt
    unfold TmOk at hT
    omega
  rw [hmod] at hcol
  refine ⟨?_, ?_⟩
  · unfold InS
    omega
  · simpa using hcta

/-- **The accumulator-read cells of a PV MMA** lie in `O` of the CTA. -/
theorem pv_readCells {cta tm i j pc : Nat} {e : Event} (hT : TmOk tm)
    (hq : EvW.PvIssue L cta tm i j pc e) {x : EvId} (hx : X.get x = some e) {cell : Cell}
    (hc : X.MmaReadCell x cell) : InO tm cell.column ∧ cell.cta = cta := by
  obtain ⟨db, dsc, hd, -, rfl⟩ := hq
  obtain ⟨d, s, mask, row, col, ⟨pc', hget⟩, hw⟩ := hc
  rw [hx] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hget
  obtain ⟨-, rfl, rfl, -, -⟩ := hget
  obtain ⟨hm, hn, hws, hg, -⟩ := SO.pv_desc hd
  obtain ⟨hcol, hcl, -, hcta⟩ := SO.resultCell_cols
    (s := ⟨dsc, db, db, cta, cta, some (tm + 128 * ((i - 1) % 2) + 8 * j), {}⟩)
    hm hg hws hn hw
  have hmod : (tm + 256) % 2 ^ 16 = tm + 256 := by
    apply Nat.mod_eq_of_lt
    unfold TmOk at hT
    omega
  rw [hmod] at hcol
  refine ⟨?_, ?_⟩
  · unfold InO
    omega
  · simpa using hcta


/-- **The softmax threads of CTA `c`**: its launched default-partition threads (the warps 0 to 3 of
the CTA's block, `Mbar.Route.soft_thread`). -/
def SoftOf (L : Launch) (c g : Nat) : Prop :=
  g < L.threads ∧ g / L.block = c ∧ g % L.block < 128

/-- **The data of the Tensor Memory handshake of every CTA of the launch**: the committing MMA lane,
thread 0 of the default partition, the Tensor Memory base and the MMA lanes of each CTA with
`Mbar.Ctx` (the reuse paths and record sources; its softmax threads are `SoftOf`) and `Lane` (the
coordinates). -/
structure SrPkg (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) where
  cm : Nat → Nat
  p0 : Nat → Nat
  tm : Nat → Nat
  Mma : Nat → Nat → Prop
  ctx : ∀ c, c < L.grid → Mbar.Ctx L K A mem0 X c (cm c) (p0 c) (SoftOf L c) (Mma c)
  lane : ∀ c, c < L.grid → Lane L X c (cm c) (p0 c) (tm c) (SoftOf L c)

/-- The softmax threads of the package: the default-partition threads of the CTA. -/
abbrev SrPkg.Soft {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (_ : SrPkg L K A mem0 X) : Nat → Nat → Prop :=
  SoftOf L

end
end PTX.Kernels.InklingRelDecode.Proof.Sr

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Exports
public import Kernels.FlashKdaFwd.Proof.Protocol.StoreCover
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue

@[expose] public section

/-! # Epilogue phase: its share of the contracts of the other layers

Each theorem is a field of a contract structure, restricted to the events of a thread in the
epilogue: thread `g` entered the epilogue before its event `k0` (`Entered`, `Exports.lean`) and
the event is at a position `k ≥ k0`. The conclusion is the field's, word for word where it is
about one event. Facts about earlier events of the thread that a field needs (counts that the
epilogue does not change) are hypotheses about the first `k0` events, in the contract's own
vocabulary; the assembly takes them from the exits of the three tile-loop phases.

`Protocol.BarFacts` (`Bars.lean`):
* `bar_shape`, `bar0_pc`, `bar_sched` (hypothesis `hT`: a compute thread has made its six
  `bar.sync 0` and its `T` named barriers before the epilogue), `bar0_le`, `bar0_exit`,
  `bar8_exit` (hypothesis: `T` named barriers before the epilogue).

`Protocol.LifeFacts` (`Life.lean`): `store_wait`; `polls_exit` (the successful polls of any
mbarrier at the exit are those before the epilogue: `state_polled`, `full_polled`).

`Protocol.UnionFacts` (`UnionClass.lean`), with the owner function `finalOwner`:
* `wr_final` (the class `final` of a thread access: a compute thread's write, seven barriers
  before it, of a byte it owns in the union region of its block), `no_read` (the epilogue has
  no read and no atomic event), `ts_final` (the class `final` of a tensor store: the store
  leader's, eight barriers before it, source in the union region), `bar_fence`,
  `store_bar_wait`.

`Protocol.StoreCover` (`StoreCover.lean`): `store_in` is `ts_final`; `final_cover`;
`final_lt` is `Arith.lean: finalOwner_lt`.

`Protocol.StoresIssued` (`ResultGlue.lean`): `ts_state` (`final`), `wr_shared` (`finalAsync`),
`state_issued` (`stateIssued`).

For `Top.DirectFacts`: `ts_bounds` (`storeBounds`), `ts_writes_state` (the write frame: a byte
a final-state store writes is a byte of the final state of the block), and `wr_frame` (a write
event is in the data part of the block's own shared window).

For progress (`Schedule/Contract.lean: RefProgress`): `bars_eq` (the number of `bar.sync 0`
is the number of the nine barrier instructions before the state's instruction), `bar_step` (a
barrier event leads to a later instruction, at sub-step 0), `exit_pc` (an exit is at
instruction 3835). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- A thread with index 160 in its block is the store leader of its block. -/
theorem storeLeader_of (hpre : Pre P L mem0) (ht : tid g = 160) :
    g = storeLeader L (g / L.block) := by
  have h := thr_eq hpre.block g
  rw [block_mod hpre, ht] at h
  exact h.symm

/-- The block of a thread is the block of its sequence and head. -/
theorem blockOf_own (hpre : Pre P L mem0) :
    blockOf P (seqOf P g) (headOf P g) = g / L.block := by
  rw [block_div hpre, cta_eq P g, blockOf]
  ring

theorem bars_eq_st : ∀ j : Fin 128,
    bars (.st j) = (bar0Pcs.filter (· < (Pos.st j).site.pc)).length := by
  decide +kernel

theorem bars_eq_ts : ∀ i : Fin 16,
    bars (.ts i) = (bar0Pcs.filter (· < (Pos.ts i).site.pc)).length := by
  decide +kernel

/-- The number of `bar.sync 0` before a position is the number of the nine barrier
instructions before the position's instruction. -/
theorem bars_eq (pos : Pos) : bars pos = (bar0Pcs.filter (· < pos.site.pc)).length := by
  cases pos with
  | st j => exact bars_eq_st j
  | ts i => exact bars_eq_ts i
  | _ => decide

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {k0 : Nat} (hE : Entered P L X g k0)
include hpre hX hg hE

/-! ### `Protocol.BarFacts` -/

/-- `BarFacts.shape` for a barrier event of the epilogue. -/
theorem bar_shape {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    mode = .sync ∧ ((id = 0 ∧ cnt = none) ∨ (id = 8 ∧ cnt = some 128 ∧ g % L.block < 128)) := by
  obtain ⟨h1, h2, h3, -⟩ := bar_in hpre hX hg hE hk he
  exact ⟨h3, .inl ⟨h1, h2⟩⟩

/-- `BarFacts.bar0_pc` for a barrier event of the epilogue. -/
theorem bar0_pc {k pc : Nat} {cnt : Option Nat} {mode : BarMode} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) :
    bar0Pcs[bar0Before X (g, k)]? = some pc :=
  (bar_in hpre hX hg hE hk he).2.2.2.1

/-- `BarFacts.sched` for a barrier event of the epilogue: `hT` says that a compute thread made
its `T` named barriers (and six `bar.sync 0`) before the epilogue. -/
theorem bar_sched {T k pc id : Nat} {cnt : Option Nat} {mode : BarMode} (hk : k0 ≤ k)
    (hT : g % L.block < 128 → 6 + T ≤ ((X.tr g).take k0).countP Execution.isBar)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    (id, cnt, mode) = barSched (decide (g % L.block < 128)) T
      (((X.tr g).take k).countP Execution.isBar) := by
  obtain ⟨rfl, rfl, rfl, -, h6, -⟩ := bar_in hpre hX hg hE hk he
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hq := count_in hpre hX hg hE hk hlt (quiet_isOtherBar (P := P) (L := L) (g := g))
  have h1 := countP_isBar ((X.tr g).take k)
  have h2 := countP_isBar ((X.tr g).take k0)
  have h6' : 6 ≤ ((X.tr g).take k).countP (Execution.isBarId 0) := h6
  have h0 : ((X.tr g).take k0).countP (Execution.isBarId 0) = 6 := by
    obtain ⟨s0, -, hin⟩ := hE
    exact hin.2
  unfold barSched
  rw [ite_eq_right]
  rintro ⟨hc, -, hlt'⟩
  have := hT (of_decide_eq_true hc)
  omega

/-- `BarFacts.bar0_le` for a thread in the epilogue. -/
theorem bar0_le : (X.tr g).countP (Execution.isBarId 0) ≤ 9 := bars_le hpre hX hg hE

/-- `BarFacts.bar0_exit` for a thread that exits from the epilogue. -/
theorem bar0_exit {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP (Execution.isBarId 0) = 9 := bars_exit hpre hX hg hE hk he

/-- `BarFacts.bar8_exit`: the named barriers of a thread that exits are those it made before
the epilogue. -/
theorem bar8_exit {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP (Execution.isBarId 8) = ((X.tr g).take k0).countP (Execution.isBarId 8) :=
  count_exit hpre hX hg hE hk he (quiet_isBarId (by decide))

/-- `DirectFacts.matrixCount`, the equality: the matrix events of a thread that exits are
those it made before the epilogue. -/
theorem matrix_exit {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP isMatrix = ((X.tr g).take k0).countP isMatrix :=
  count_exit hpre hX hg hE hk he quiet_isMatrix

/-! ### `Protocol.LifeFacts` -/

/-- `LifeFacts.store_wait` for a tensor store of the epilogue. -/
theorem store_wait {k j pc al pcx : Nat} {sp : TensorStore.Spec} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hx : X.get (g, j) = some ⟨pcx, .exit⟩) :
    ∃ w, k < w ∧ w < j ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  have hlast := Execution.exit_last hX hg hx
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : k ≠ j := by
    rintro rfl
    rw [he] at hx
    cases hx
  exact waits_for hpre hX hg hE hk he (by omega) hx (.inr rfl)

/-- `LifeFacts.state_polled`, `full_polled`, `UnionFacts.polled`: the successful polls of an
mbarrier before an event of the epilogue are those before the epilogue. -/
theorem polls_in {k : Nat} (hk : k0 ≤ k) (hlt : k < (X.tr g).length) (m : Loc) :
    okPolls m ((X.tr g).take k) = okPolls m ((X.tr g).take k0) :=
  count_in hpre hX hg hE hk hlt (quiet_okPoll m)

/-- The arrivals on an mbarrier before an event of the epilogue are those before the
epilogue. -/
theorem arrivals_in {k : Nat} (hk : k0 ≤ k) (hlt : k < (X.tr g).length) (m : Loc) :
    arrivals m ((X.tr g).take k) = arrivals m ((X.tr g).take k0) :=
  count_in hpre hX hg hE hk hlt (quiet_arrivesOn m)

/-! ### `Protocol.UnionFacts` and `Protocol.StoreCover` -/

/-- `UnionFacts.thread`, class `final`: a write event of the epilogue is a compute thread's,
with seven `bar.sync 0` before it, and a byte it covers is a byte of the union region of the
thread's block that the thread owns. -/
theorem wr_final {k pc : Nat} {a : Acc} {bs : List Byte} {l : Loc} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hl : a.Covers l) :
    g % L.block < 128 ∧ bar0Before X (g, k) = 7 ∧ InUnion L (g / L.block) l ∧
      finalOwner P l = g % L.block := by
  obtain ⟨s, j, -, -, ht, -, -, rfl, -, hb⟩ := wr_in hpre hX hg hE hk he
  have hbd := stAddr_bounds hpre ht j
  obtain ⟨h1, h2, h3, h4⟩ := hl
  simp only at h1 h2 h3 h4
  rw [block_mod hpre]
  refine ⟨ht, hb, ⟨h1, h2, ?_, ?_⟩, finalOwner_store hpre ht j h3 h4⟩
  · rw [hpre.sharedBase]; omega
  · rw [hpre.sharedBase]; omega

/-- The epilogue has no read event and no atomic event: a thread access there is a write. -/
theorem no_read {k : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some e) :
    (∀ a bs, e.kind ≠ .rd a bs) ∧ ∀ a o n, e.kind ≠ .rmw a o n := by
  rcases kind_in hpre hX hg hE hk he with ⟨f, h⟩ | ⟨a, bs, h⟩ | h | h | ⟨al, sp, h⟩ | h | h | h <;>
    rw [h] <;> exact ⟨fun _ _ h' => (nomatch h'), fun _ _ _ h' => (nomatch h')⟩

/-- `UnionFacts.store`, class `final`, and `StoreCover.store_in`: a tensor store of the
epilogue is the store leader's, with eight `bar.sync 0` before it, and every byte it reads is
in the union region of its block. -/
theorem ts_final {k pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hl : TensorStore.readLoc sp x y z = some l) :
    g = storeLeader L (g / L.block) ∧ bar0Before X (g, k) = 8 ∧ InUnion L (g / L.block) l := by
  obtain ⟨i, ht, -, -, -, rfl, hb⟩ := ts_in hpre hX hg hE hk he
  obtain ⟨h1, h2, h3, h4⟩ := final_read_in i hl
  refine ⟨storeLeader_of hpre ht, hb, h1, h2, ?_, ?_⟩
  · rw [hpre.sharedBase]; exact h3
  · rw [hpre.sharedBase]; exact h4

/-- `UnionFacts.bar_fence` for a barrier event of the epilogue. -/
theorem bar_fence {k pc : Nat} {cnt : Option Nat} {mode : BarMode} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) (hb : bar0Before X (g, k) = 7) :
    0 < k ∧ ∃ pcf, X.get (g, k - 1) =
      some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain ⟨h1, h2⟩ := (bar_in hpre hX hg hE hk he).2.2.2.2.2.2 hb
  exact ⟨h1, _, h2⟩

/-- `UnionFacts.store_bar_wait` for a tensor store and a later barrier of the epilogue. -/
theorem store_bar_wait {k k' pc al pce : Nat} {cnt : Option Nat} {mode : BarMode}
    {sp : TensorStore.Spec} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hkk : k < k') (he' : X.get (g, k') = some ⟨pce, .bar 0 cnt mode⟩) :
    ∃ w, k < w ∧ w < k' ∧ BulkWaitsFor X .read (g, k) (g, w) :=
  waits_for hpre hX hg hE hk he hkk he' (.inl ⟨_, _, _, rfl⟩)

/-- `StoreCover.final_cover`: at its eighth `bar.sync 0` a compute thread has written, with
seven barriers before the write, every byte of the union region of its block that it owns. -/
theorem final_cover_bar {k pc : Nat} {cnt : Option Nat} {mode : BarMode} {l : Loc}
    (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hb : bar0Before X (g, k) = 7) (ht : g % L.block < 128) (hl : InUnion L (g / L.block) l)
    (ho : finalOwner P l = g % L.block) :
    ∃ i pcw aw bs, i < k ∧ X.get (g, i) = some ⟨pcw, .wr aw bs⟩ ∧ aw.Covers l ∧
      bar0Before X (g, i) = 7 := by
  rw [block_mod hpre] at ht ho
  obtain ⟨h1, h2, h3, h4⟩ := hl
  rw [hpre.sharedBase] at h3 h4
  obtain ⟨j, hj1, hj2⟩ := store_of_owner hpre ht h3 h4 ho
  obtain ⟨hlt, hbj, bs, hev⟩ := stores_done hpre hX hg hE hk he hb ht j
  exact ⟨_, _, _, bs, hlt, hev, ⟨h1, h2, hj1, hj2⟩, hbj⟩

/-! ### `Protocol.StoresIssued` and the frames -/

/-- `StoresIssued.final`: a tensor store of the epilogue with a slot that writes a byte of the
final state of `(s, h)` is a store of the store leader of the block of `(s, h)`, with eight
`bar.sync 0` before it; the slot is in range and the byte is the one `final_writeLoc` names. -/
theorem ts_state {k pc al x y z s h b : Nat} {sp : TensorStore.Spec} {v kk : Fin 128}
    (hk : k0 ≤ k) (hh : h < P.heads) (hb : b < 4)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hw : TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v kk).at b)) :
    g = storeLeader L (blockOf P s h) ∧ bar0Before X (g, k) = 8 ∧ s = seqOf P g ∧
      h = headOf P g ∧ ∃ i : Fin 16, sp = finalSpec P L g i.val ∧ x < 8 ∧ v.val = y ∧
        kk.val = 8 * i.val + x ∧ b = z := by
  obtain ⟨i, ht, -, -, -, rfl, hbar⟩ := ts_in hpre hX hg hE hk he
  obtain ⟨hx, hy, hz⟩ := final_write_lt hw
  rw [final_writeLoc hpre hg i hx hy hz] at hw
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
    stateLoc_at_inj (headOf_lt hpre hg) hh hz hb (Option.some.inj hw)
  refine ⟨?_, hbar, rfl, rfl, i, rfl, hx, rfl, rfl, rfl⟩
  rw [blockOf_own hpre]
  exact storeLeader_of hpre ht

/-- `StoresIssued.finalAsync` and the shared frame: a write event of the epilogue is in the
data part of the shared window of the thread's own block, so it covers no global byte. -/
theorem wr_frame {k pc : Nat} {a : Acc} {bs : List Byte} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ P.sharedBase + 32768 ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304 := by
  obtain ⟨s, j, -, -, ht, -, -, rfl, -, -⟩ := wr_in hpre hX hg hE hk he
  have hbd := stAddr_bounds hpre ht j
  exact ⟨rfl, rfl, hbd.2.1, hbd.2.2⟩

/-- `StoresIssued.finalAsync`: no write event of the epilogue covers a byte of the final
state. -/
theorem wr_shared {k pc s h b : Nat} {a : Acc} {bs : List Byte} {v kk : Fin 128} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : ¬ a.Covers ((P.stateLoc s h v kk).at b) := by
  obtain ⟨h1, -⟩ := wr_frame hpre hX hg hE hk he
  rintro ⟨h2, -⟩
  rw [h1] at h2
  cases h2

/-- `StoresIssued.stateIssued`: when the store leader exits from the epilogue, every byte of
the final state of its sequence and head is the write location of a slot of one of its tensor
stores. -/
theorem state_issued {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (ht : tid g = 160) (v kk : Fin 128) {b : Nat} (hb : b < 4) :
    ∃ i pcs al sp x y z, i < k ∧ X.get (g, i) = some ⟨pcs, .tensorStore al sp⟩ ∧
      TensorStore.writeLoc sp x y z = some ((P.stateLoc (seqOf P g) (headOf P g) v kk).at b) := by
  obtain ⟨i, x, hw⟩ := final_cover hpre hg v kk hb
  obtain ⟨hlt, hev⟩ := stores_issued hpre hX hg hE hk he ht i
  exact ⟨_, _, _, _, x, v.val, b, hlt, hev, hw⟩

/-- `DirectFacts.storeBounds` for a tensor store of the epilogue. -/
theorem ts_bounds {k pc al : Nat} {sp : TensorStore.Spec} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) :
    ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  obtain ⟨i, -, -, -, -, rfl, -⟩ := ts_in hpre hX hg hE hk he
  exact final_noOob hpre hg i

/-- `DirectFacts.writeFrame` for a tensor store of the epilogue: a byte it writes is a byte of
the final state of the block's sequence and head. -/
theorem ts_writes_state {k pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hw : TensorStore.writeLoc sp x y z = some l) : P.StateByte l := by
  obtain ⟨i, -, -, -, -, rfl, -⟩ := ts_in hpre hX hg hE hk he
  obtain ⟨hx, hy, hz⟩ := final_write_lt hw
  rw [final_writeLoc hpre hg i hx hy hz] at hw
  exact ⟨_, seqOf_lt hpre g, _, headOf_lt hpre hg, _, _, z, hz, (Option.some.inj hw).symm⟩

/-! ### Progress -/

/-- `RefProgress.exitAt`: an exit of the epilogue is at instruction 3835. -/
theorem exit_pc {k pc : Nat} (hk : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    pc = 3835 := by
  obtain ⟨s, -, -, -, rfl, -⟩ := exit_in hpre hX hg hE hk he
  rfl

/-- `RefProgress.bar0`: at every followed state of the epilogue, also the one after the
thread's last event, the number of `bar.sync 0` the thread has made is the number of the nine
barrier instructions before the state's instruction; and the state is at an instruction of the
epilogue, at sub-step 0. -/
theorem bars_at {k : Nat} {s : D} (hk : k0 ≤ k) (hle : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = (bar0Pcs.filter (· < s.site.pc)).length ∧
      3113 ≤ s.site.pc ∧ s.site.sub = 0 := by
  obtain ⟨s0, h0, hin⟩ := hE
  obtain ⟨pos, hr, -, -, hb⟩ := epilogue_weak hpre hX hg h0 hin hk hle hσ
  rw [hb, bars_eq pos, hr.site]
  refine ⟨rfl, ?_, ?_⟩
  · cases pos with
    | st j => rw [st_pc j]; omega
    | ts i => rw [ts_pc i]; omega
    | _ => decide
  · cases pos <;> rfl

/-- `RefProgress.barStep`: a barrier event of the epilogue is made at sub-step 0 and leads to
a later instruction of the epilogue. -/
theorem bar_step {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {d d' : D} (hk : k0 ≤ k)
    (hσ : Frame.stateAt (code L) X g k = some (some d))
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ' : Frame.stateAt (code L) X g (k + 1) = some (some d')) :
    d.site.sub = 0 ∧ d.site.pc < d'.site.pc := by
  have hE' := hE
  obtain ⟨s0, h0, hin⟩ := hE'
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨pos, hr, hon, hkp, hb⟩ := epilogue_weak hpre hX hg h0 hin hk (by omega) hσ
  obtain ⟨pos', hr', hon', hkp', hb'⟩ :=
    epilogue_weak hpre hX hg h0 hin (k := k + 1) (by omega) (by omega) hσ'
  have hne : pos ≠ .exit := by
    rintro rfl
    obtain ⟨-, -, -, -, -, h8, -⟩ := bar_in hpre hX hg hE hk he
    have : bar0Before X (g, k) = 9 := hb
    omega
  have hp' : pos' = nxt g pos := ord_inj hon' (onPath_nxt hon) (by rw [ord_nxt hon hne]; omega)
  rw [hr.site, hr'.site, hp']
  refine ⟨by cases pos <;> rfl, ?_⟩
  cases pos with
  | exit => exact absurd rfl hne
  | st j =>
    have hj := j.isLt
    by_cases h1 : j.val + 1 < 128
    · rw [nxt, dite_eq_left h1, st_pc, st_pc]
      simp only
      omega
    · rw [nxt, dite_eq_right h1, st_pc]
      show _ < 3774
      omega
  | ts i =>
    have hi := i.isLt
    by_cases h1 : i.val + 1 < 16
    · rw [nxt, dite_eq_left h1, ts_pc, ts_pc]
      simp only
      omega
    · rw [nxt, dite_eq_right h1, ts_pc]
      show _ < 3832
      omega
  | bar7 => simp only [nxt]; split <;> decide
  | bar8 => simp only [nxt]; split <;> decide
  | _ => simp only [nxt]; decide

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue

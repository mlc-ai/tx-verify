-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Exports
public import Kernels.FlashKdaFwd.Proof.Top.Wire

@[expose] public section

/-! # The Store share of the direct safety facts

`Proof/Top/Wire.lean: DirectFacts` lists the fields of the safety facts that the protocol
contract does not give: footprints of memory accesses, operands of tensor copies, absence of
undefined-behaviour events. This file proves the share of the Store phase. Every theorem is
about an operation whose issuing event is fired at a followed state that satisfies the phase
invariant (`hσ : Frame.stateAt (code L) X g k = some (some s)`, `hI : Inv P X g k s`).

What the phase touches (`Touch`, `touch_store`, `memTouches_store`): the four 4-byte element
reads of a chunk of a partial tile (`rdAcc`: shared memory of the thread's own block), the
2-byte global stores of a chunk (`wrAcc`: output bytes), and the bytes of a tensor store of a
full tile (`tileSpec`: a shared source byte, a global destination byte).

* `memSpaces_store`: field `memSpaces`.
* `sharedFrame_store`: field `sharedFrame` (the bytes are in an output buffer: offsets 86912
  to 95104 of the window; `shared_touch`).
* `global_touch`, `writeFrame_store`: field `writeFrame`: a global byte the phase touches is an
  output byte of a token of the thread's own sequence and head.
* `global_write`: for the field `globalReadFrame`: an operation of the phase that touches a
  global byte is a write intent (the phase reads no global memory).
* `write_intent`, `globalWriteOnce_store`: field `globalWriteOnce` inside one thread: two write
  intents issued in the phase that cover one global byte are one.
* `storeBounds_store`: field `storeBounds`.
* `noUb_store`: field `storeNoUb`, control half: an undefined-behaviour event is at a global
  store whose source register does not convert to 16 bits.

**`globalWriteOnce` across threads** (for the assembly): by `global_touch` a global byte that
a thread `g` touches in this phase is `(P.outLoc (seqOf P g) (headOf P g) tok v).at z` with
`tok < P.length (seqOf P g)`; `Protocol.outLoc_at_inj` turns an equality of two such bytes
into equal sequences and heads, hence equal blocks (`blockOf_cta`), and the store leader of a
block is one thread (`leader_at`). Against the final-state stores of the epilogue: those write
`P.StateByte`s, which are apart from the output bytes by `Pre.outputApartFinal`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Frame PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar storeLeader bar0Before covers_one)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **What an operation of the phase touches**: four bytes of an element of a chunk of the
output stage, the two bytes of an output feature of a token of the sequence, or one byte that a
tensor store of a full tile reads or writes. -/
def Touch (P : Params) (g : Nat) (a : Acc) : Prop :=
  (∃ t row c m, m < 4 ∧ row < 16 ∧ c < 16 ∧ a = rdAcc P g t row c m) ∨
  (∃ t row c j, P.length (seqOf P g) < 16 * t + 16 ∧ 16 * t + row < P.length (seqOf P g) ∧
    c < 16 ∧ j < 8 ∧ a = wrAcc P g t row c j) ∨
  ∃ t i, i < 16 ∧ 16 * t + 16 ≤ P.length (seqOf P g) ∧ a.size = 1 ∧ ∃ x y z,
    TensorStore.readLoc (tileSpec P g t i) x y z = some a.loc ∨
      TensorStore.writeLoc (tileSpec P g t i) x y z = some a.loc

/-- **A global byte that the phase touches is an output byte of the thread's own sequence and
head**: byte `z` of feature `v` of a token `tok` of the sequence. -/
theorem global_touch (hpre : Pre P L mem0) (hg : g < L.threads) {a : Acc} {l : Loc}
    (ht : Touch P g a) (hc : a.Covers l) (hgl : l.space = .global) :
    ∃ tok < P.length (seqOf P g), ∃ v : Fin 128, ∃ z < 2,
      l = (P.outLoc (seqOf P g) (headOf P g) tok v).at z := by
  rcases ht with ⟨t, row, c, m, -, -, -, rfl⟩ | ⟨t, row, c, j, -, hrow, hc', hj, rfl⟩ |
    ⟨t, i, hi, hfull, hs, x, y, z, h | h⟩
  · have h1 : l.space = .shared := hc.1
    rw [hgl] at h1
    cases h1
  · obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨sp, ct, ad⟩ := l
    simp only [wrAcc] at h1 h2 h3 h4
    subst h1 h2
    refine ⟨16 * t + row, hrow, ⟨8 * c + j, by omega⟩, ad - (P.outputBase + 256 *
      ((firstToken P.length (seqOf P g) + (16 * t + row)) * P.heads + headOf P g) +
      2 * (8 * c + j)), by omega, ?_⟩
    simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  · have h1 := (readLoc_range h).1
    rw [covers_one hs hc, hgl] at h1
    cases h1
  · obtain ⟨hx, hy, hz⟩ := tileSpec_lt (.inl h)
    rw [(tileSpec_slot hpre hg hi hfull hx hy hz).1] at h
    rw [← covers_one hs hc, ← Option.some.inj h]
    exact ⟨16 * t + y, by omega, ⟨8 * i + x, by omega⟩, z, hz, rfl⟩

/-- **A shared byte that the phase touches is a byte of an output buffer** of the thread's own
block: inside the data part of the window. -/
theorem shared_touch (hpre : Pre P L mem0) {a : Acc} (ht : Touch P g a)
    (hsh : a.loc.space = .shared) :
    a.loc.cta = g / L.block ∧ P.sharedBase + 86912 ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 95104 := by
  rcases ht with ⟨t, row, c, m, hm, hrow, hc, rfl⟩ | ⟨t, row, c, j, -, -, -, -, rfl⟩ |
    ⟨t, i, hi, hfull, hs, x, y, z, h | h⟩
  · have h2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
    refine ⟨(block_div hpre).symm, ?_, ?_⟩ <;> (simp only [rdAcc]; omega)
  · cases hsh
  · obtain ⟨-, h2, h3, h4⟩ := readLoc_range h
    have h256 : mapBytes 10 = 256 := rfl
    have h2' : t % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [h256] at h4
    rw [block_div hpre]
    exact ⟨h2, by omega, by omega⟩
  · rw [Execution.store_writeLoc_global h] at hsh
    cases hsh

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **What an event of the phase accesses or issues an access of.** -/
theorem touch_store {k : Nat} {e : Event} {a : Acc} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (ha : AccessOf e a ∨ AsyncOf e a) : Touch P g a := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  cases pos with
  | entry => cases hev; rcases ha with ha | ha <;> exact ha.elim
  | wait t => obtain ⟨ok, rfl⟩ := hev; rcases ha with ha | ha <;> exact ha.elim
  | ts t i =>
    cases hev
    rcases ha with ha | ha
    · exact ha.elim
    · exact .inr (.inr ⟨t, i.val, i.isLt, hr.pos.2.1, ha.1, ha.2⟩)
  | commit t => cases hev; rcases ha with ha | ha <;> exact ha.elim
  | ld0 t row c =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    rcases ha with ha | ha
    · exact .inl ⟨t, row, c, 0, by decide, by omega, hc, ha⟩
    · exact ha.elim
  | ld1 t row c v0 =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    rcases ha with ha | ha
    · exact .inl ⟨t, row, c, 1, by decide, by omega, hc, ha⟩
    · exact ha.elim
  | ld2 t row c v0 v1 =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    rcases ha with ha | ha
    · exact .inl ⟨t, row, c, 2, by decide, by omega, hc, ha⟩
    · exact ha.elim
  | ld3 t row c v0 v1 v2 =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    rcases ha with ha | ha
    · exact .inl ⟨t, row, c, 3, by decide, by omega, hc, ha⟩
    · exact ha.elim
  | gst t row c j =>
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    rcases hev with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
    · rcases ha with ha | ha
      · exact .inr (.inl ⟨t, row, c, j.val, hpart, by omega, hc, j.isLt, ha⟩)
      · exact ha.elim
    · rcases ha with ha | ha <;> exact ha.elim
  | bwait t => cases hev; rcases ha with ha | ha <;> exact ha.elim
  | arrive t => cases hev; rcases ha with ha | ha <;> exact ha.elim

/-- **What a memory operation issued in the phase touches** (`Execution.MemTouches`: thread
accesses, `nc` reads and the stages of asynchronous operations, pending or performed). -/
theorem memTouches_store {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    Touch P g a := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    exact touch_store hpre hX hg he hσ hI ha
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact touch_store hpre hX hg hnc hσ hI (.inl rfl)

/-- **`DirectFacts.memSpaces` for the store phase.** -/
theorem memSpaces_store {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    a.loc.space = .shared ∨ a.loc.space = .global := by
  rcases memTouches_store hpre hX hg hr ht hσ hI with ⟨t, row, c, m, -, -, -, rfl⟩ |
    ⟨t, row, c, j, -, -, -, -, rfl⟩ | ⟨t, i, -, -, -, x, y, z, h | h⟩
  · exact .inl rfl
  · exact .inr rfl
  · exact .inl (readLoc_range h).1
  · exact .inr (Execution.store_writeLoc_global h)

/-- **`DirectFacts.sharedFrame` for the store phase**: a shared byte the phase touches is in
the data part of the window of the issuer's own block (in an output buffer: offsets 86912 to
95104). -/
theorem sharedFrame_store {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a) (hsh : a.loc.space = .shared)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    a.loc.cta = g / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304 := by
  obtain ⟨h1, h2, h3⟩ := shared_touch hpre (L := L) (memTouches_store hpre hX hg hr ht hσ hI) hsh
  exact ⟨h1, by omega, by omega⟩

/-- **`DirectFacts.writeFrame` for the store phase**: a global byte that an operation of the
phase touches is an output byte of a token of the batch. -/
theorem writeFrame_store {r : AsyncCopy.Ref} {a : Acc} {l : Loc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a) (hc : a.Covers l)
    (hgl : l.space = .global) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s) : P.OutputByte l := by
  obtain ⟨tok, htok, v, z, hz, rfl⟩ :=
    global_touch hpre hg (memTouches_store hpre hX hg hr ht hσ hI) hc hgl
  exact ⟨seqOf P g, seqOf_lt hpre g, headOf P g, headOf_lt hpre hg, tok, htok, v, z, hz, rfl⟩

/-- **`DirectFacts.storeBounds` for the store phase**: a tensor store at a state of the phase
selects no out-of-bounds element (8 features from `8 i`, the 16 tokens of a full tile, the
thread's head). -/
theorem storeBounds_store {k pc al : Nat} {sp : TensorStore.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
  have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
  have h1 := tok_le hpre g
  have hi := i.isLt
  exact storeOut_noOob (by omega) (by omega) (headOf_lt hpre hg)

/-- **`DirectFacts.storeNoUb`, control half**: an undefined-behaviour event at a state of the
phase is at one of the eight global stores of a chunk, and its fault is that of converting the
store's 16-bit source register to 16 bits. The value layer shows that the register holds a
16-bit payload (`Values/Ends`: with `storeCtl_elem` the event is then a write). -/
theorem noUb_store {k pc : Nat} {f : Fault} {s : D} (he : X.get (g, k) = some ⟨pc, .ub f⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ∃ t row c, ∃ j : Fin 8, RefAt P g (.gst t row c j) s ∧ pc = 3025 + j.val ∧
      storeValue 16 (s.x (gstSrc j.val)) = .error f := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, row, c, j, rfl, h1, h2⟩ := ev_ub_inv hev
  exact ⟨t, row, c, j, hr, h1, h2⟩

/-- **The write intents issued in the phase**: a thread write at a global store of a chunk, or
the write stage of slot `(x, y, z)` of a tensor store of a full tile. -/
theorem write_intent {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D} (hr : r.issuer = (g, k))
    (hi : X.Intent r a true) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s) :
    (∃ t row c, ∃ j : Fin 8, r = .thread (g, k) ∧ RefAt P g (.gst t row c j) s ∧
      ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) (.gst t row c j) ∧
      a = wrAcc P g t row c j.val ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩) ∨
    (∃ t, ∃ i : Fin 16, ∃ x y z, r = .async (g, k) (.write (.store x y z)) ∧
      RefAt P g (.ts t i) s ∧
      ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) (.ts t i) ∧ a.size = 1 ∧
      TensorStore.writeLoc (tileSpec P g t i.val) x y z = some a.loc ∧
      ∃ pc al sp, X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) := by
  have key : ∀ {e : Event}, X.get (g, k) = some e → ¬ phaseKind e.kind → False := by
    intro e he hk
    obtain ⟨pos, -, -, hev, -⟩ := store_good hpre hX hg he hσ hI
    exact hk (ev_kind hev)
  rcases r with ⟨g', k'⟩ | ⟨⟨g', k'⟩, p⟩
  · obtain ⟨rfl, rfl⟩ : g' = g ∧ k' = k := Prod.mk.inj hr
    rcases hi with ⟨bs, -, hw⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
    · cases hw
    · obtain ⟨pos, hr', hl, hev, -⟩ := store_good hpre hX hg he hσ hI
      obtain ⟨t, row, c, j, rfl, -, rfl, -⟩ := ev_wr_inv hev
      exact .inl ⟨t, row, c, j, rfl, hr', hl, rfl, pc, bs, he⟩
    · exact (key he (fun h => h)).elim
  · obtain ⟨rfl, rfl⟩ : g' = g ∧ k' = k := Prod.mk.inj hr
    obtain ⟨hw, hfp⟩ := hi
    cases p with
    | writeCopy =>
      obtain ⟨sp, ⟨pc, he⟩, -⟩ := hfp
      exact (key he (fun h => h)).elim
    | writeLoad x y z =>
      obtain ⟨sp, addr, ⟨pc, he⟩, -⟩ := hfp
      exact (key he (fun h => h)).elim
    | writeStore x y z =>
      obtain ⟨sp, addr, ⟨pc, he⟩, hwl, hs⟩ := hfp
      obtain ⟨pos, hr', hl, hev, -⟩ := store_good hpre hX hg he hσ hI
      obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
      exact .inr ⟨t, i, x, y, z, rfl, hr', hl, hs, hwl, pc, _, _, he⟩
    | writeCta c =>
      obtain ⟨sp, targets, ⟨pc, he⟩, -⟩ := hfp
      exact (key he (fun h => h)).elim
    | writeElem j =>
      obtain ⟨sp, ⟨pc, he⟩, -⟩ := hfp
      exact (key he (fun h => h)).elim
    | _ => first | (cases hw; done) | exact hfp.elim

/-- **`DirectFacts.globalWriteOnce` inside one thread**: two write intents issued at states of
the phase by one thread that cover one global byte are one operation. (Different tiles write
different tokens, the sixteen tensor stores of a tile and the sixteen chunks of a row different
features, the slots of a store and the eight stores of a chunk different bytes; a full tile is
written by tensor stores only and a partial tile by element stores only.) -/
theorem globalWriteOnce_store {r r' : AsyncCopy.Ref} {a a' : Acc} {l : Loc} {k k' : Nat}
    {s s' : D} (hr : r.issuer = (g, k)) (hr' : r'.issuer = (g, k')) (hi : X.Intent r a true)
    (hi' : X.Intent r' a' true) (hc : a.Covers l) (hc' : a'.Covers l)
    (hgl : l.space = .global) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s) (hσ' : Frame.stateAt (code L) X g k' = some (some s'))
    (hI' : Inv P X g k' s') : r = r' := by
  have hh := headOf_lt hpre hg
  -- the byte of a write of a chunk
  have gstByte : ∀ {t row c : Nat} {j : Fin 8} {d : D} {b : Acc},
      RefAt P g (.gst t row c j) d → b = wrAcc P g t row c j.val → b.Covers l →
      ∃ z < 2, l = (P.outLoc (seqOf P g) (headOf P g) (16 * t + row)
        ⟨(8 * c + j.val) % 128, Nat.mod_lt _ (by decide)⟩).at z ∧ row < 16 ∧ c < 16 ∧
        P.length (seqOf P g) < 16 * t + 16 ∧ 16 * t + row < P.length (seqOf P g) := by
    intro t row c j d b hrd hb hcov
    subst hb
    obtain ⟨hpart, hrow, hcc, -⟩ := hrd.pos.2
    obtain ⟨h1, h2, h3, h4⟩ := hcov
    obtain ⟨sp, ct, ad⟩ := l
    simp only [wrAcc] at h1 h2 h3 h4
    subst h1 h2
    have hj := j.isLt
    refine ⟨ad - (P.outputBase + 256 * ((firstToken P.length (seqOf P g) + (16 * t + row)) *
      P.heads + headOf P g) + 2 * (8 * c + j.val)), by omega, ?_, by omega, hcc, hpart,
      by omega⟩
    simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  -- the byte of a slot of a tensor store
  have tsByte : ∀ {t : Nat} {i : Fin 16} {x y z : Nat} {d : D} {b : Acc},
      RefAt P g (.ts t i) d → b.size = 1 →
      TensorStore.writeLoc (tileSpec P g t i.val) x y z = some b.loc → b.Covers l →
      x < 8 ∧ y < 16 ∧ z < 2 ∧ 16 * t + 16 ≤ P.length (seqOf P g) ∧
        l = (P.outLoc (seqOf P g) (headOf P g) (16 * t + y)
          ⟨(8 * i.val + x) % 128, Nat.mod_lt _ (by decide)⟩).at z := by
    intro t i x y z d b hrd hs hwl hcov
    have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hrd.pos.2.1
    obtain ⟨hx, hy, hz⟩ := tileSpec_lt (.inl hwl)
    rw [(tileSpec_slot hpre hg i.isLt hfull hx hy hz).1] at hwl
    refine ⟨hx, hy, hz, hfull, ?_⟩
    rw [← covers_one hs hcov, ← Option.some.inj hwl]
    have hi := i.isLt
    simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  rcases write_intent hpre hX hg hr hi hσ hI with
      ⟨t, row, c, j, rfl, hr1, hl1, ha1, pc1, bs1, he1⟩ |
      ⟨t, i, x, y, z, rfl, hr1, hl1, hs1, hw1, pc1, al1, sp1, he1⟩ <;>
    rcases write_intent hpre hX hg hr' hi' hσ' hI' with
      ⟨t', row', c', j', rfl, hr2, hl2, ha2, pc2, bs2, he2⟩ |
      ⟨t', i', x', y', z', rfl, hr2, hl2, hs2, hw2, pc2, al2, sp2, he2⟩
  · -- two element stores
    obtain ⟨z1, hz1, e1, hrow1, hc1, hp1, ht1⟩ := gstByte hr1 ha1 hc
    obtain ⟨z2, hz2, e2, hrow2, hc2, hp2, ht2⟩ := gstByte hr2 ha2 hc'
    obtain ⟨-, -, h3, h4, -⟩ := Protocol.outLoc_at_inj hh hh ht1 ht2 hz1 hz2 (e1.symm.trans e2)
    have h4' := congrArg Fin.val h4
    simp only at h4'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨rfl, rfl, rfl, hjj⟩ : t = t' ∧ row = row' ∧ c = c' ∧ j.val = j'.val := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    obtain rfl : j = j' := Fin.ext hjj
    have hk : k = k' := nthEv_unique (X := X) (p := isGWrite) he1 (by subst ha1; rfl) he2
      (by subst ha2; rfl) ((congrArg Led.gstores hl1).trans (congrArg Led.gstores hl2).symm)
    rw [hk]
  · -- an element store and a tensor store: one tile is partial, the other full
    exfalso
    obtain ⟨z1, hz1, e1, hrow1, hc1, hp1, ht1⟩ := gstByte hr1 ha1 hc
    obtain ⟨hx, hy, hz, hfull, e2⟩ := tsByte hr2 hs2 hw2 hc'
    obtain ⟨-, -, h3, -⟩ := Protocol.outLoc_at_inj hh hh ht1
      (show 16 * t' + y' < P.length (seqOf P g) by omega) hz1 hz (e1.symm.trans e2)
    omega
  · exfalso
    obtain ⟨hx, hy, hz, hfull, e1⟩ := tsByte hr1 hs1 hw1 hc
    obtain ⟨z2, hz2, e2, hrow2, hc2, hp2, ht2⟩ := gstByte hr2 ha2 hc'
    obtain ⟨-, -, h3, -⟩ := Protocol.outLoc_at_inj hh hh
      (show 16 * t + y < P.length (seqOf P g) by omega) ht2 hz hz2 (e1.symm.trans e2)
    omega
  · -- two tensor stores
    obtain ⟨hx, hy, hz, hfull, e1⟩ := tsByte hr1 hs1 hw1 hc
    obtain ⟨hx', hy', hz', hfull', e2⟩ := tsByte hr2 hs2 hw2 hc'
    obtain ⟨-, -, h3, h4, h5⟩ := Protocol.outLoc_at_inj hh hh
      (show 16 * t + y < P.length (seqOf P g) by omega)
      (show 16 * t' + y' < P.length (seqOf P g) by omega) hz hz' (e1.symm.trans e2)
    have h4' := congrArg Fin.val h4
    simp only at h4'
    have hi1 := i.isLt
    have hi2 := i'.isLt
    obtain ⟨rfl, rfl, hii, rfl⟩ : t = t' ∧ y = y' ∧ i.val = i'.val ∧ x = x' := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    obtain rfl : i = i' := Fin.ext hii
    subst h5
    have hk : k = k' := nthEv_unique (X := X) (p := isTStore) he1 rfl he2 rfl
      ((congrArg Led.tstores hl1).trans (congrArg Led.tstores hl2).symm)
    rw [hk]

/-- **`DirectFacts.globalReadFrame` for the store phase**: the phase reads no global memory, so
an operation of the phase that touches a global byte is a write intent. -/
theorem global_write {r : AsyncCopy.Ref} {a : Acc} {l : Loc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a) (hc : a.Covers l)
    (hgl : l.space = .global) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s) : X.Intent r a true := by
  have key : ∀ {e : Event}, X.get (g, k) = some e → ¬ phaseKind e.kind → False := by
    intro e he hk
    obtain ⟨pos, -, -, hev, -⟩ := store_good hpre hX hg he hσ hI
    exact hk (ev_kind hev)
  have hsp : a.loc.space = .global := hc.1.symm.trans hgl
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · rcases r with ⟨g', k'⟩ | ⟨⟨g', k'⟩, p⟩
    · obtain ⟨rfl, rfl⟩ : g' = g ∧ k' = k := Prod.mk.inj hr
      rcases hi with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, hw, -⟩ | ⟨old, new, pc, he⟩
      · exfalso
        obtain ⟨pos, hr', hl, hev, -⟩ := store_good hpre hX hg he hσ hI
        obtain ⟨t, row, c, m, -, -, -, rfl, -⟩ := ev_rd_inv hev
        cases hsp
      · exact .inr (.inl ⟨bs, hw, rfl⟩)
      · exact (key he (fun h => h)).elim
    · obtain ⟨rfl, rfl⟩ : g' = g ∧ k' = k := Prod.mk.inj hr
      obtain ⟨hw, hfp⟩ := hi
      cases hpw : p.writes with
      | true => exact ⟨hpw.symm, hfp⟩
      | false =>
        exfalso
        cases p with
        | readCopy =>
          rcases hfp with ⟨sp, ⟨pc, he⟩, -⟩ | ⟨pc, he⟩ <;> exact key he (fun h => h)
        | readLoad x y z =>
          obtain ⟨sp, addr, ⟨pc, he⟩, -⟩ := hfp
          exact key he (fun h => h)
        | readStore x y z =>
          obtain ⟨sp, addr, ⟨pc, he⟩, hrl, -⟩ := hfp
          obtain ⟨pos, hr', hl, hev, -⟩ := store_good hpre hX hg he hσ hI
          obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
          rw [(readLoc_range hrl).1] at hsp
          cases hsp
        | readPrefetch x y z =>
          obtain ⟨sp, addr, ⟨pc, he⟩, -⟩ := hfp
          exact key he (fun h => h)
        | oldStore x y z =>
          obtain ⟨sp, addr, ⟨pc, he⟩, hred, -⟩ := hfp
          obtain ⟨pos, hr', hl, hev, -⟩ := store_good hpre hX hg he hσ hI
          obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
          simp [tileSpec, storeSpec] at hred
        | oldElem j =>
          obtain ⟨sp, rr, ⟨pc, he⟩, -⟩ := hfp
          exact key he (fun h => h)
        | mmaRead isB idx =>
          obtain ⟨-, hfp⟩ := hfp
          rcases hfp with ⟨d, sp, acc, mask, ⟨pc, he⟩, -⟩ | ⟨c', k', cta, ⟨pc, he⟩, -⟩ <;>
            exact key he (fun h => h)
        | _ => first | (cases hpw; done) | exact hfp.elim
  · exfalso
    subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact key hnc (fun h => h)

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store

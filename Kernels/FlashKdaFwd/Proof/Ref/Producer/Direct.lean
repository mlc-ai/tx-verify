-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Exports
public import Kernels.FlashKdaFwd.Proof.Top.Wire

@[expose] public section

/-! # The Producer share of the direct safety facts

`Proof/Top/Wire.lean: DirectFacts` lists the fields of the safety facts that the protocol
contract does not give: footprints of memory accesses, operands of tensor copies, absence of
undefined-behaviour events. This file proves the share of the Producer phase (instructions 1403
to 2105, and the `bar.sync 0` at 1402 that enters it), in the shapes of the startup phase's
`Ref/Startup/Direct.lean`. Every theorem is about an operation whose issuing event is fired at
a followed state `Frame.stateAt (code L) X g k = some (some s)` of a thread of the load warp
that entered the phase (`Entered P L X g k0`, `k0 ≤ k`), and has the second alternative
`Left P L X g k` ("the thread has left the phase").

The phase touches memory in one way only (`touch_producer`, and `memTouches_producer` in the
vocabulary of `Execution.MemTouches`): the asynchronous loads of the tiles. A touched access is
one byte that the copy `tileLoad P L g tt i` of a tile `tt < T` and a position `i < 70` reads
(in global memory) or writes (in the shared window of the issuer's block). The phase has no
thread access, no `nc` read and no atomic: its other events are polls, arrivals and one
`bar.sync 0`.

* `memSpaces_producer`: field `memSpaces`.
* `sharedFrame_producer`: field `sharedFrame` (the destination of a load lies in the input
  buffers, bytes 32768 to 86912 of the window).
* `loadFill_producer`: field `loadFill` (every map of a tile load fills with zero and has
  bfloat16 or FP32 elements).
* `loadBounds_producer`: field `loadBounds` (only the loads of `v` and `beta` can select an
  element outside their tensor), from `tileLoad_bounds`.
* `globalReadFrame_producer`: field `globalReadFrame`, from `TileSource P L mem0`.
* `unionLoad_producer`: the field `load` of the protocol layer's `UnionFacts` for the loads of
  the phase, with the owner function `Owners.piece l = pieceOf ((l.addr - (L.sharedBase +
  32768)) % 18048)`.
* The control half of `loadNoUb` is `Exports.lean: noUb_producer`: an undefined-behaviour event
  at a followed state from the entry on belongs to a thread that has left the phase. The phase
  has no data instruction, so there is no data half.

`TileSource P L mem0` is the one fact not derived here: every global byte that a tile load reads
is allocated in the launch memory and is no byte of the output and no byte of the final state.
It is a property of the eight tensor maps, of the coordinates `coords P g tt i` and of the
precondition's layout of the inputs; the source side of the tensor loads is the work of the
`Ref/Source/` files. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (loadBytes)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **What an operation of the phase touches**: one byte that the load at a position `i < 70`
of a tile `tt < T` reads or writes. -/
def Touch (P : Params) (L : Launch) (g : Nat) (a : Acc) : Prop :=
  ∃ tt i, tt < tilesOf P g ∧ i < 70 ∧ a.size = 1 ∧ ∃ x y z,
    TensorCopy.readLoc (tileLoad P L g tt i) x y z = some a.loc ∨
      TensorCopy.writeLoc (tileLoad P L g tt i) x y z = some a.loc

/-- **The source footprint of the tile loads** (not derived in this file): every global byte
that the load at position `i` of a tile `tt` of a block reads is allocated in the launch memory
and is no output byte and no byte of the final state. -/
def TileSource (P : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ g < L.threads, ∀ tt < tilesOf P g, ∀ i < 70, ∀ x y z l,
    TensorCopy.readLoc (tileLoad P L g tt i) x y z = some l →
      mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) (hw : warp g = 4) {k0 k : Nat} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
include hpre hX hg hw hen hk0

/-- **What an event of the phase accesses or issues an access of.** -/
theorem touch_producer {e : Event} {a : Acc} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ha : AccessOf e a ∨ AsyncOf e a) :
    Touch P L g a ∨ Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, hr, hl, hev, -⟩ | h
  · refine .inl ?_
    obtain ⟨pc, kd⟩ := e
    cases pos with
    | entry =>
      cases hev
      rcases ha with ha | ha <;> exact ha.elim
    | poll c u =>
      obtain ⟨ok, h⟩ := hev
      cases h
      rcases ha with ha | ha <;> exact ha.elim
    | arrive c u =>
      cases hev
      rcases ha with ha | ha <;> exact ha.elim
    | tail j =>
      obtain ⟨ok, h⟩ := hev
      cases h
      rcases ha with ha | ha <;> exact ha.elim
    | load c u i =>
      have hk := hev
      simp only [Ev, Event.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      obtain ⟨tt, j, htt, hj, -, -, hsp, -⟩ := issue_shape hr hl hev
      rcases ha with ha | ha
      · exact ha.elim
      · rw [hsp] at ha
        exact ⟨tt, j, htt, hj, ha⟩
  · exact .inr h

/-- **What a memory operation issued in the phase touches** (`Execution.MemTouches`: thread
accesses, `nc` reads and the stages of asynchronous operations, pending or performed). -/
theorem memTouches_producer {r : AsyncCopy.Ref} {a : Acc} {s : D} (hr : r.issuer = (g, k))
    (ht : X.MemTouches r a) (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Touch P L g a ∨ Left P L X g k := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    exact touch_producer hpre hX hg hw hen hk0 he hσ ha
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact touch_producer hpre hX hg hw hen hk0 hnc hσ (.inl rfl)

/-- **`DirectFacts.memSpaces` for the Producer phase.** -/
theorem memSpaces_producer {r : AsyncCopy.Ref} {a : Acc} {s : D} (hr : r.issuer = (g, k))
    (ht : X.MemTouches r a) (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (a.loc.space = .shared ∨ a.loc.space = .global) ∨ Left P L X g k := by
  rcases memTouches_producer hpre hX hg hw hen hk0 hr ht hσ with
    ⟨tt, i, -, -, -, x, y, z, h | h⟩ | h
  · exact .inl (.inr (Execution.tensor_readLoc_global h))
  · exact .inl (.inl (writeLoc_range h).1)
  · exact .inr h

/-- **`DirectFacts.sharedFrame` for the Producer phase**: a shared byte the phase touches is a
byte of an input buffer (bytes 32768 to 86912) of the window of the issuer's own block. -/
theorem sharedFrame_producer {r : AsyncCopy.Ref} {a : Acc} {s : D} (hr : r.issuer = (g, k))
    (ht : X.MemTouches r a) (hsh : a.loc.space = .shared)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (a.loc.cta = g / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304) ∨ Left P L X g k := by
  rcases memTouches_producer hpre hX hg hw hen hk0 hr ht hσ with
    ⟨tt, i, -, hi, hs, x, y, z, h | h⟩ | h
  · rw [Execution.tensor_readLoc_global h] at hsh
    cases hsh
  · obtain ⟨⟨-, hc, -, -⟩, hlo, hhi, -⟩ := tileLoad_writeLoc hpre hi h
    have h3 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
    have hd := dstAbs_form i hi
    have hb : loadBytes i ≤ 512 := by
      unfold loadBytes
      split_ifs <;> decide
    refine .inl ⟨hc, ?_, ?_⟩
    · split_ifs at hd <;> omega
    · simp only [loadBytes] at hhi
      split_ifs at hd hhi <;> omega
  · exact .inr h

/-- **`DirectFacts.globalReadFrame` for the Producer phase**: a global byte the phase touches
(it writes none) is allocated and is no output byte and no byte of the final state. -/
theorem globalReadFrame_producer (hsrc : TileSource P L mem0) {r : AsyncCopy.Ref} {a : Acc}
    {l : Loc} {s : D} (hr : r.issuer = (g, k)) (ht : X.MemTouches r a) (hc : a.Covers l)
    (hgl : l.space = .global) (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l) ∨ Left P L X g k := by
  rcases memTouches_producer hpre hX hg hw hen hk0 hr ht hσ with
    ⟨tt, i, htt, hi, hs, x, y, z, h | h⟩ | h
  · obtain rfl : a.loc = l := Protocol.covers_one hs hc
    exact .inl (hsrc g hg tt htt i hi x y z _ h)
  · have h1 := (writeLoc_range h).1
    rw [← hc.1, hgl] at h1
    cases h1
  · exact .inr h

/-- **`DirectFacts.loadFill` for the Producer phase**: the map of every tile load fills
out-of-bounds elements with zero and has bfloat16 or FP32 elements. -/
theorem loadFill_producer {pc al : Nat} {sp : TensorCopy.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (sp.descriptor.fill = .zero ∧ sp.descriptor.format ≠ .f64) ∨ Left P L X g k := by
  rcases full_issue_producer hpre hX hg hw hen hk0 he hσ with
    ⟨tt, i, -, -, -, -, -, -, -, -, h1, h2, -⟩ | h
  · exact .inl ⟨h1, h2⟩
  · exact .inr h

/-- **`DirectFacts.loadBounds` for the Producer phase**: a tile load that selects an
out-of-bounds element through a large-class map is a load of the values `v` or of the gate
logits `beta`. -/
theorem loadBounds_producer {pc al : Nat} {sp : TensorCopy.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (TensorHasOob sp.descriptor sp.origin sp.rows → sp.descriptor.allocationClass = .large →
      (sp.descriptor.base = P.valuesBase ∧ P.allocation 0 = .large) ∨
        (sp.descriptor.base = P.logitsBase ∧ P.allocation 1 = .large)) ∨ Left P L X g k := by
  rcases full_issue_producer hpre hX hg hw hen hk0 he hσ with ⟨tt, i, htt, hi, -, rfl, -⟩ | h
  · exact .inl (tileLoad_bounds hpre hg htt hi)
  · exact .inr h

/-- **`UnionFacts.load` for the Producer phase** (`Proof/Protocol/UnionClass.lean`): a byte of
the union region that a tensor load of the phase writes is of the class `tile` of the load's
stage, for every choice of owner functions whose `piece` is `pieceOf` of the byte's offset in
its input buffer. -/
theorem unionLoad_producer {O : Protocol.Owners}
    (hO : ∀ l : Loc, O.piece l = pieceOf ((l.addr - (L.sharedBase + 32768)) % 18048))
    {pc al x y z c : Nat} {sp : TensorCopy.Spec} {l : Loc} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hwl : TensorCopy.writeLoc sp x y z = some l) (hu : Protocol.InUnion L c l) :
    Protocol.LoadClass L X O c g k sp l ∨ Left P L X g k := by
  rcases full_issue_producer hpre hX hg hw hen hk0 he hσ with
    ⟨tt, i, htt, hi, -, rfl, hm, -, hcnt, -, -, -, -, -, hbar, hpoll⟩ | h
  · obtain ⟨hin, -, -, hp⟩ := tileLoad_writeLoc hpre hi hwl
    obtain rfl : c = g / L.block := hu.2.1.symm.trans hin.2.1
    exact .inl (.tile (stage tt) hm hbar hin (by rw [hO, hp, hcnt]) hpoll)
  · exact .inr h

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer

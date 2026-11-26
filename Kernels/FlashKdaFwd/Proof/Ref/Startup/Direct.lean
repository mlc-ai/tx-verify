-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Contract
public import Kernels.FlashKdaFwd.Proof.Top.Wire

@[expose] public section

/-! # The startup share of the direct safety facts

`Proof/Top/Wire.lean: DirectFacts` lists the fields of the safety facts that the protocol
contract does not give: footprints of memory accesses, operands of tensor copies, absence of
undefined-behaviour events. This file proves the share of the startup phase (instructions 0 to
387) of the fields that concern it. Every theorem is about an operation whose issuing event is
fired at a followed state `Frame.stateAt (code L) X g k = some (some s)`, and has the second
alternative `Left P L X g k` ("the thread has left the startup phase").

The phase touches memory in two ways (`touch_startup`, and `memTouches_startup` in the
vocabulary of `Execution.MemTouches`): the 21 loads of the offsets array (eight bytes of an
entry `i ≤ N` in global memory) and the 16 asynchronous loads of the initial state (`stateSpec P
L g j`: source bytes in global memory, destination the `j`-th 4096-byte block of the state
buffer in the shared window of the issuer's block). It writes no global memory and has no
`nc` read, no thread write and no atomic.

* `memSpaces_startup`: field `memSpaces`.
* `sharedFrame_startup`: field `sharedFrame` (the destination of a load lies in the bytes
  32768 to 98304 of the window).
* `globalReadFrame_startup`: field `globalReadFrame`. The bytes of the offsets array are
  allocated and apart from the outputs by `Pre` (`offsets_frame`); for the source bytes of the
  16 loads the theorem takes `StateSource P L` (see below).
* `loadFill_startup`: field `loadFill` (the map of the initial state fills with zero and has
  FP32 elements).
* `loadBounds_startup`: field `loadBounds`, from `StateSource P L`.
* The control half of `computeNoUb` / `loadNoUb` / `storeNoUb` is `Exports.lean:
  noUb_startup`: an undefined-behaviour event at a followed state belongs to a thread that has
  left the phase.

`StateSource P L` is the one fact not derived here: the source footprint of the 16 loads (every
byte one of them reads is a byte of the initial-state array, and its box selects no element
outside the array). It is a property of the tensor map of the initial state and of the
coordinates `(8 j, 0, H * seq + head)`, announced as a generic lemma of `Ref/TensorLoad.lean`
(the Producer phase's file). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **What an operation of the phase touches**: eight bytes of an entry of the offsets array,
or one byte that a load of the initial state reads or writes. -/
def Touch (P : Params) (L : Launch) (g : Nat) (a : Acc) : Prop :=
  (∃ i ≤ P.sequences, a = { loc := P.offsetLoc i, size := 8 }) ∨
    ∃ j : Fin 16, a.size = 1 ∧ ∃ x y z,
      TensorCopy.readLoc (stateSpec P L g j.val) x y z = some a.loc ∨
        TensorCopy.writeLoc (stateSpec P L g j.val) x y z = some a.loc

/-- **The source footprint of the 16 loads of the initial state** (not derived in this file):
the box of each load selects no element outside the array, and every byte it reads is a byte of
the initial-state array. -/
def StateSource (P : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, ∀ j < 16,
    ¬ TensorHasOob (stateSpec P L g j).descriptor (stateSpec P L g j).origin
        (stateSpec P L g j).rows ∧
      ∀ x y z l, TensorCopy.readLoc (stateSpec P L g j) x y z = some l →
        ∃ k < P.stateBytes, l = ⟨.global, 0, P.initialBase + k⟩

/-- **The bytes of the offsets array are allocated and are no output**: a byte of the eight
bytes of entry `i ≤ N` has launch content (`Pre.offsets`) and is no byte of `out` and no byte
of the final state (the outputs do not overlap the inputs). -/
theorem offsets_frame (hpre : Pre P L mem0) {i : Nat} (hi : i ≤ P.sequences) {l : Loc}
    (hc : ({ loc := P.offsetLoc i, size := 8 } : Acc).Covers l) :
    mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  obtain ⟨sp, ct, ad⟩ := l
  simp only [Params.offsetLoc] at h1 h2 h3 h4
  subst h1 h2
  have hk : ad - (P.offsetsBase + 8 * i) < 8 := by omega
  have hl : (⟨.global, 0, ad⟩ : Loc) = (P.offsetLoc i).at (ad - (P.offsetsBase + 8 * i)) := by
    simp only [Params.offsetLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hl, hpre.offsets i hi _ hk]
    simp
  · intro ho
    obtain ⟨k, hk', he⟩ := Top.outputByte_range ho
    have hap := hpre.outputApartInputs.offsets
    simp only [Loc.mk.injEq, true_and] at he
    unfold Apart Params.offsetBytes at hap
    omega
  · intro ho
    obtain ⟨k, hk', he⟩ := Top.stateByte_range ho
    have hap := hpre.finalApartInputs.offsets
    simp only [Loc.mk.injEq, true_and] at he
    unfold Apart Params.offsetBytes at hap
    omega

/-- **The bytes of the initial-state array are allocated and are no output.** -/
theorem initial_frame (hpre : Pre P L mem0) {k : Nat} (hk : k < P.stateBytes) :
    mem0 ⟨.global, 0, P.initialBase + k⟩ ≠ none ∧ ¬ P.OutputByte ⟨.global, 0, P.initialBase + k⟩ ∧
      ¬ P.StateByte ⟨.global, 0, P.initialBase + k⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · -- byte `k` is byte `b` of entry `(v, f)` of plane `p = s * H + h`
    unfold Params.stateBytes at hk
    have hH := hpre.headsPos
    have hp : k / 65536 < P.sequences * P.heads := by omega
    have hs : k / 65536 / P.heads < P.sequences := Nat.div_lt_of_lt_mul (by
      rwa [Nat.mul_comm] at hp)
    have hh : k / 65536 % P.heads < P.heads := Nat.mod_lt _ hH
    have hv : k % 65536 / 512 < 128 := by omega
    have hf : k % 512 / 4 < 128 := by omega
    have hb : k % 4 < 4 := by omega
    have hpl : k / 65536 / P.heads * P.heads + k / 65536 % P.heads = k / 65536 := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod _ _
    have h := hpre.initialState _ hs _ hh ⟨_, hv⟩ ⟨_, hf⟩ _ hb
    have hl : (⟨.global, 0, P.initialBase + k⟩ : Loc) =
        (P.initialLoc (k / 65536 / P.heads) (k / 65536 % P.heads) ⟨_, hv⟩ ⟨_, hf⟩).at (k % 4) := by
      simp only [Params.initialLoc, Loc.at, Loc.mk.injEq, true_and, hpl]
      omega
    rw [hl, h]
    simp
  · intro ho
    obtain ⟨k', hk', he⟩ := Top.outputByte_range ho
    have hap := hpre.outputApartInputs.initial
    simp only [Loc.mk.injEq, true_and] at he
    unfold Apart at hap
    omega
  · intro ho
    obtain ⟨k', hk', he⟩ := Top.stateByte_range ho
    have hap := hpre.finalApartInputs.initial
    simp only [Loc.mk.injEq, true_and] at he
    unfold Apart at hap
    omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **What an event of the phase accesses or issues an access of.** -/
theorem touch_startup {k : Nat} {e : Event} {a : Acc} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ha : AccessOf e a ∨ AsyncOf e a) :
    Touch P L g a ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, -, -, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
    · obtain ⟨inst, ld, rfl⟩ := hev
      rcases ha with ha | ha <;> exact ha.elim
    · obtain ⟨v, ok, rfl⟩ := hev
      rcases ha with ha | ha <;> exact ha.elim
    · subst hev
      rcases ha with ha | ha <;> exact ha.elim
    · subst hev
      rcases ha with ha | ha <;> exact ha.elim
    · subst hev
      rcases ha with ha | ha <;> exact ha.elim
    · obtain ⟨i, hi, bs, hbs, rfl⟩ := hev
      rcases ha with ha | ha
      · exact .inl ⟨i, hi, ha⟩
      · exact ha.elim
    · subst hev
      rcases ha with ha | ha <;> exact ha.elim
    · subst hev
      rcases ha with ha | ha
      · exact ha.elim
      · exact .inr ⟨j, ha⟩
    · obtain ⟨ok, rfl⟩ := hev
      rcases ha with ha | ha <;> exact ha.elim
  · exact .inr h

/-- **What a memory operation issued in the phase touches** (`Execution.MemTouches`: thread
accesses, `nc` reads and the stages of asynchronous operations, pending or performed). -/
theorem memTouches_startup {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : Touch P L g a ∨ Left P L X g k := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    exact touch_startup hpre hX hg he hσ ha
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact touch_startup hpre hX hg hnc hσ (.inl rfl)

/-- **`DirectFacts.memSpaces` for the startup phase.** -/
theorem memSpaces_startup {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (a.loc.space = .shared ∨ a.loc.space = .global) ∨ Left P L X g k := by
  rcases memTouches_startup hpre hX hg hr ht hσ with (⟨i, -, rfl⟩ | ⟨j, -, x, y, z, h | h⟩) | h
  · exact .inl (.inr rfl)
  · exact .inl (.inr (Execution.tensor_readLoc_global h))
  · exact .inl (.inl (writeLoc_range h).1)
  · exact .inr h

/-- **`DirectFacts.sharedFrame` for the startup phase**: a shared byte the phase touches is a
byte of the state buffer (bytes 32768 to 98304) of the window of the issuer's own block. -/
theorem sharedFrame_startup {r : AsyncCopy.Ref} {a : Acc} {k : Nat} {s : D}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a) (hsh : a.loc.space = .shared)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (a.loc.cta = g / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304) ∨ Left P L X g k := by
  rcases memTouches_startup hpre hX hg hr ht hσ with (⟨i, -, rfl⟩ | ⟨j, hs, x, y, z, h | h⟩) | h
  · cases hsh
  · rw [Execution.tensor_readLoc_global h] at hsh
    cases hsh
  · obtain ⟨-, hc, hlo, hhi⟩ := writeLoc_range h
    have h8 : mapBytes 8 = 4096 := rfl
    have := j.isLt
    exact .inl ⟨hc, by omega, by omega⟩
  · exact .inr h

/-- **`DirectFacts.globalReadFrame` for the startup phase**: a global byte the phase touches
(it writes none) is allocated and is no output byte and no byte of the final state. -/
theorem globalReadFrame_startup (hsrc : StateSource P L) {r : AsyncCopy.Ref} {a : Acc}
    {l : Loc} {k : Nat} {s : D} (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hc : a.Covers l) (hgl : l.space = .global)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l) ∨ Left P L X g k := by
  rcases memTouches_startup hpre hX hg hr ht hσ with (⟨i, hi, rfl⟩ | ⟨j, hs, x, y, z, h | h⟩) | h
  · exact .inl (offsets_frame hpre hi hc)
  · obtain ⟨k', hk', hl⟩ := (hsrc g hg j.val j.isLt).2 x y z _ h
    obtain rfl : a.loc = l := covers_one hs hc
    rw [hl]
    exact .inl (initial_frame hpre hk')
  · have h1 := (writeLoc_range h).1
    rw [← hc.1, hgl] at h1
    cases h1
  · exact .inr h

/-- **`DirectFacts.loadFill` for the startup phase**: the map of the initial state fills
out-of-bounds elements with zero and its elements are FP32. -/
theorem loadFill_startup {k pc al : Nat} {sp : TensorCopy.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (sp.descriptor.fill = .zero ∧ sp.descriptor.format ≠ .f64) ∨ Left P L X g k := by
  rcases issue_startup hpre hX hg he hσ with ⟨j, -, -, rfl, -, -⟩ | h
  · exact .inl (loadSpec_fill P _ 8 _ _ _)
  · exact .inr h

/-- **`DirectFacts.loadBounds` for the startup phase**: a load of the initial state selects
no out-of-bounds element. -/
theorem loadBounds_startup (hsrc : StateSource P L) {k pc al : Nat} {sp : TensorCopy.Spec}
    {s : D} (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    ¬ TensorHasOob sp.descriptor sp.origin sp.rows ∨ Left P L X g k := by
  rcases issue_startup hpre hX hg he hσ with ⟨j, -, -, rfl, -, -⟩ | h
  · exact .inl (hsrc g hg j.val j.isLt).1
  · exact .inr h

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup

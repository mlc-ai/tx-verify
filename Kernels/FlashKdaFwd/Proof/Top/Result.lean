-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Safety
public import Lemmas.Kernel.Memory
public import Lemmas.Order.Order

@[expose] public section

/-! # The result, from stated premises (top-level skeleton)

`Correct.result` asks that the global memory after every complete consistent execution
satisfies `Post` (`Spec.lean`): the two bytes of every output element are the bytes of the
bfloat16 payload of the scaled inner product of the state after its token with the token's
query, the four bytes of every final-state entry are the bytes of the binary32 payload of the
state after the last token, and every other global byte is as before the launch. (`Post` is
stated on bytes, in the form in which `Pre` asks for the initial state; reading the bytes as
numbers, `memFloat`, is a corollary stated with the kernel's theorem.)

This file derives `Post` from the definition of the final memory (`IsFinal`: the final content
of a byte is the byte of the write that no other write of the byte follows, and the launch
content if no write covers it) and from kernel-specific facts about one consistent execution:

* two of the memory frames of the safety proof (`SafetyFacts`, `Top/Safety.lean`): every write
  to global memory lies in an output byte or a final-state byte (`writeFrame`), and no global
  byte has two writers (`globalWriteOnce`);
* the four fields of `ResultFacts`: in a complete execution every output byte and every
  final-state byte has a performed write (`outputWritten`, `stateWritten`), and a performed
  write of such a byte writes the byte of the specified number, stored as a floating-point
  payload (`outputValue`, `stateValue`).

The chain is "final byte, its one writer, the byte it wrote": with one writer per byte, the
final memory holds that writer's byte (`IsFinal.unique`), which the value premises say is the
payload byte of the specified number; and a byte no write covers keeps its launch content
(`IsFinal.unwritten`).

Who writes what, for the proofs of the fields. An output
element of a full tile (16 live tokens) is written by one byte write of one of the sixteen
tensor stores that the store warp's elected lane issues for the tile, and an element of the
partial last tile by a `st.global.b16` of that lane; both copy the output staging buffer, which
the compute warps filled with `stmatrix`. A final-state element is written by a byte write of
one of the sixteen tensor stores of the FP32 state buffer, which the compute threads filled
with their 128 `st.b32` each. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX Recurrence

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The kernel-specific facts about one consistent execution `X` from which, with two frames
of `SafetyFacts`, the postcondition follows.** -/
structure ResultFacts (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  /-- In a complete execution every byte of the output of every token of the batch has a
  performed write: the tensor stores of the full tiles have written all their bytes, and the
  store lane has passed the stores of the live rows of the partial last tile. -/
  outputWritten : Complete L X → ∀ s < P.sequences, ∀ h < P.heads, ∀ t < P.length s,
    ∀ v : Fin 128, ∀ k < 2, ∃ w a bs, X.MemWrites w a bs ∧ a.Covers ((P.outLoc s h t v).at k)
  /-- A performed write of a byte of the output of token `t` writes that byte of the bfloat16
  payload of the specified output `scale * ⟨state after token t, query t⟩`. -/
  outputValue : ∀ s < P.sequences, ∀ h < P.heads, ∀ t < P.length s, ∀ v : Fin 128, ∀ k < 2,
    ∀ w a bs, X.MemWrites w a bs → a.Covers ((P.outLoc s h t v).at k) →
      wbyte a bs ((P.outLoc s h t v).at k) =
        some ((Value.float .bf16 (P.output s h t v)).byteAt k)
  /-- In a complete execution every byte of the final state of every sequence and head has a
  performed write: the sixteen tensor stores of the state buffer have written all their
  bytes. -/
  stateWritten : Complete L X → ∀ s < P.sequences, ∀ h < P.heads, ∀ v k : Fin 128, ∀ b < 4,
    ∃ w a bs, X.MemWrites w a bs ∧ a.Covers ((P.stateLoc s h v k).at b)
  /-- A performed write of a byte of a final-state entry writes that byte of the binary32
  payload of the state after the last token of the sequence. -/
  stateValue : ∀ s < P.sequences, ∀ h < P.heads, ∀ v k : Fin 128, ∀ b < 4,
    ∀ w a bs, X.MemWrites w a bs → a.Covers ((P.stateLoc s h v k).at b) →
      wbyte a bs ((P.stateLoc s h v k).at b) =
        some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b)

/-- **The final content of a global byte that has a performed write is that write's byte**: it
is the byte's only writer. -/
theorem final_of_write (S : SafetyFacts P L mem0 X) {m : FinalMem} (hf : IsFinal L mem0 X m)
    {l : Loc} (hl : l.space = .global) {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites w a bs) (hc : a.Covers l) : m l = some (wbyte a bs l) :=
  hf.unique hw hc fun w' a' _ hw' hc' =>
    S.globalWriteOnce w' w a' a l hw'.intent hw.intent hc' hc hl

/-- **The postcondition from the premises**: the final memory of a complete execution holds
the specified outputs and final state, and nothing else in global memory changed. -/
theorem post_of_facts (S : SafetyFacts P L mem0 X) (R : ResultFacts P L mem0 X)
    (hd : Complete L X) {m : FinalMem} (hf : IsFinal L mem0 X m) : Post P mem0 m := by
  refine ⟨fun s hs h hh t ht v => ?_, fun s hs h hh v k => ?_, fun l hl hno hns => ?_⟩
  · intro k hk
    obtain ⟨w, a, bs, hw, hc⟩ := R.outputWritten hd s hs h hh t ht v k hk
    rw [final_of_write S hf rfl hw hc, R.outputValue s hs h hh t ht v k hk w a bs hw hc]
  · intro b hb
    obtain ⟨w, a, bs, hw, hc⟩ := R.stateWritten hd s hs h hh v k b hb
    rw [final_of_write S hf rfl hw hc, R.stateValue s hs h hh v k b hb w a bs hw hc]
  · refine hf.unwritten fun w a bs hw hc => ?_
    rcases S.writeFrame w a l hw.intent hc hl with ho | hst
    · exact hno ho
    · exact hns hst

end PTX.Kernels.FlashKdaFwd.Proof.Top

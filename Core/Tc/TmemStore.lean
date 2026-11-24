-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaLifetime
public import Core.Tc.TcPipeline
public import Core.Tc.TcDataAddress
public import Core.Thread.Access

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TMEM-STORE-VALUE — Tensor Memory stores and their completion
Statement: Register j of a `tcgen05.st` writes its 32-bit value to the cell that the fragment of the
  shape assigns to it. The write is ordered before a later event only through a later
  `tcgen05.wait::st` of the storing thread followed by tcgen05 ordering, or, for a later
  `tcgen05.ld` or `tcgen05.st` of the same warp, through the pipelined pairs of DEP-TC-PIPELINE.

Defs: TcMma.StoreCell, TcMma.StoreValue, TcMma.StoreDoneBefore, TcMma.storeDoneBefore_iff

Source:
- §9.7.18.2.3.1 (fragments of every shape)
- §9.7.18.8.4 (tcgen05.st)
- §9.7.18.6.1 (st is asynchronous)
- DEP-TC-PIPELINE (the pairs st→ld and st→st)
- §9.7.18.6.2.1.2 and §9.7.18.8.5 (wait::st)
- §9.7.18.6.3: "The asynchronous tcgen05 instructions that are ordered across threads in the same
    warp also form a tcgen05 pipeline."
- §9.7.18.6.4.2: "Example 1: tcgen05.st tcgen05.wait::st tcgen05.ld"
- §9.7.18.6.4.4 (completion handoff)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

Direction: reading

Applies: Represented tcgen05.st of every shape, in the storing thread's CTA

Premises: Register slot `j` is the cell of the store's recorded shape and address (`tcDataCell`,
  THREAD-TC-DATA-ADDRESS), with the register's 32-bit value read at issue.

Effect: Relations used by the Tensor Memory source, stability, conflict and lifetime rules. The
  direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the
  fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.
-/

/-- Store `st` writes `cell` (register slot `j`). -/
def StoreCell (L : Launch) (X : Execution) (st : EvId) (cell : Cell) : Prop :=
  ∃ address vals shape j, X.TSt st address vals shape ∧ j < vals.length ∧
    cell = tcDataCell L st.1 shape address j

/-- Store `st` writes `value` to `cell`. -/
def StoreValue (L : Launch) (X : Execution) (st : EvId) (cell : Cell) (value : Value) : Prop :=
  ∃ address vals shape j, X.TSt st address vals shape ∧ vals[j]? = some value ∧
    cell = tcDataCell L st.1 shape address j

/-- Store `st` is ordered before `e`: completed and observed, or pipelined with a later
load or store of the same warp (DEP-TC-PIPELINE). -/
def StoreDoneBefore (L : Launch) (X : Execution) (st e : EvId) : Prop :=
  (∃ address vals shape, X.TSt st address vals shape) ∧
    (WaitBefore L X .waitSt st e ∨ Pipelined L X .stWrite st .ldRead e ∨
      Pipelined L X .stWrite st .stWrite e)

/-- The form of `StoreDoneBefore` before the pipeline table was one definition. -/
theorem storeDoneBefore_iff {L : Launch} {X : Execution} {st e : EvId} :
    StoreDoneBefore L X st e ↔ (∃ address vals shape, X.TSt st address vals shape) ∧
      (WaitBefore L X .waitSt st e ∨
        (SameWarp L st.1 e.1 ∧ TcBefore L X st e ∧
          ((∃ address vals shape, X.TLd e address vals shape) ∨
            (∃ address vals shape, X.TSt e address vals shape)))) := by
  simp only [StoreDoneBefore, Pipelined]
  constructor
  · rintro ⟨h, hw | ⟨hs, hb, -, hl⟩ | ⟨hs, hb, -, ht⟩⟩
    · exact ⟨h, .inl hw⟩
    · exact ⟨h, .inr ⟨hs, hb, .inl hl⟩⟩
    · exact ⟨h, .inr ⟨hs, hb, .inr ht⟩⟩
  · rintro ⟨h, hw | ⟨hs, hb, hl | ht⟩⟩
    · exact ⟨h, .inl hw⟩
    · exact ⟨h, .inr (.inl ⟨hs, hb, h, hl⟩)⟩
    · exact ⟨h, .inr (.inr ⟨hs, hb, h, ht⟩)⟩

/-! ## THREAD-TC-CP-DECOMPRESS — the bytes a decompressing tcgen05.cp writes
Statement: A `tcgen05.cp` with `.b8x16.b4x16_p64` or `.b8x16.b6x16_p32` reads and places its source
  rows as the copy of the same shape without decompression, and each 16-byte chunk of a source row
  becomes 16 destination bytes: destination byte `i` holds element `i` of the chunk, a 4-bit element
  in bits 5 to 2 and a 6-bit element in bits 5 to 0, the other bits zero. The copy reads the same
  source bytes as the copy without decompression, padding included. A chunk is bytes `16 q` to
  `16 q + 15` of a row, and its bits are the little-endian number of those bytes (`chunkBits`).

Defs: TcCopy.chunkBits, TcCopy.decompressByte, TcCopy.decompressedWord, TcCopy.cpWord,
  TcCopy.cpWord_none

Source:
- §9.7.18.9.1.1: "A contiguous set of 16 elements of 4-bits each followed by 8 bytes of padding can
    be converted into 16 elements of 8-bits each as shown in Figure 197 ."
- §9.7.18.9.1.2: "A contiguous set of 16 elements of 6-bits each followed by 4 bytes of padding is
    decompressed into 16 elements of 8-bits each as shown in Figure 199 ."
- §9.7.18.9.2
- EXT-TCCP

Direction: reading

Applies: tcgen05.cp of every shape with `.b8x16.b6x16_p32` or `.b8x16.b4x16_p64`

Premises: The premises of THREAD-TC-CP-CELLS.

Effect: Value geometry only: the word of each destination cell is a function of the 16 source bytes
  of its chunk, known only when all 16 have a bit pattern.

Review: The hardware may skip the read of the padding bytes. Skipping it only adds conflicts in the
  model, which is stricter.
-/

/-- The 16 bytes of chunk `q` of row `row` (bytes recorded from one CTA) as a little-endian
number, if all have a bit pattern. -/
def _root_.PTX.TcCopy.chunkBits (s : TcCpShape) (bytes : List (Option Byte)) (row q : Nat) :
    Option Nat :=
  littleEndianBits ((List.range 16).map fun i => bytes.getD (row * s.rowBytes + 16 * q + i) none)

/-- Destination byte `i` of a chunk with bits `x` (EXT-TCCP). -/
def _root_.PTX.TcCopy.decompressByte : TcCpFmt → Nat → Nat → Nat
  | .b4x16p64, x, i => x / 2 ^ (4 * i) % 16 * 4
  | .b6x16p32, x, i => x / 2 ^ (6 * i) % 64

/-- The word of row `row`, column `col` of a decompressing copy: the four destination bytes of
its chunk at the word's position. -/
def _root_.PTX.TcCopy.decompressedWord (f : TcCpFmt) (s : TcCpShape) (bytes : List (Option Byte))
    (row col : Nat) : Option Value := do
  let x ← TcCopy.chunkBits s bytes row (4 * col / 16)
  let b (k : Nat) := TcCopy.decompressByte f x (4 * col % 16 + k)
  pure (.bits 32 (BitVec.ofNat 64 (b 0 + 256 * b 1 + 256 ^ 2 * b 2 + 256 ^ 3 * b 3)))

/-- The word a copy leaves at row `row`, column `col`. -/
def _root_.PTX.TcCopy.cpWord (c : TcCopy.Spec) (bytes : List (Option Byte)) (row col : Nat) :
    Option Value :=
  match c.fmt with
  | none => TcCopy.word c.shape bytes row col
  | some f => TcCopy.decompressedWord f c.shape bytes row col

/-- A copy without decompression leaves its source bytes in order (the form before
decompression was represented). -/
theorem _root_.PTX.TcCopy.cpWord_none {c : TcCopy.Spec} (h : c.fmt = none) :
    TcCopy.cpWord c = TcCopy.word c.shape := by
  funext bytes row col; simp [TcCopy.cpWord, h]

/-! ## DEP-TMEM-COPY-VALUE — Tensor Memory words written by tcgen05.cp
Statement: A `tcgen05.cp` writes, in each CTA of its group, the lanes its shape assigns to each
  source row by the row's columns at its address, each word holding its four source bytes from that
  CTA in order, or with decompression the four bytes THREAD-TC-CP-DECOMPRESS gives, and unknown if a
  source byte it depends on is unknown. Its completion is observed like that of an MMA, through a
  `tcgen05.commit`. A `tcgen05.shift` writes and reads the cells that THREAD-TC-SHIFT-CELLS gives;
  the words it leaves are DEP-TMEM-SHIFT-VALUE.

Defs: TcMma.CpCell, TcMma.CpValue, TcMma.ShiftCell, TcMma.ShiftReadCell

Source:
- §9.7.18.9.2 (tcgen05.cp)
- §9.7.18.6.2.1.1 (commit-based completion)
- THREAD-TC-CP-CELLS
- THREAD-TC-CP-DECOMPRESS

Direction: reading

Applies: Every represented tcgen05.cp (THREAD-TC-CP-CELLS, THREAD-TC-CP-DECOMPRESS) and
  tcgen05.shift

Premises: The copy's source bytes are its recorded asynchronous reads.

Effect: Writer and value relations used by the Tensor Memory source, stability, conflict and
  lifetime rules.
-/

/-- Copy `cp` writes `cell`. -/
def CpCell (X : Execution) (cp : EvId) (cell : Cell) : Prop :=
  ∃ c cta index lane, X.CpIssue cp c ∧ cta ∈ c.ctas ∧ index < c.shape.sourceBytes ∧
    lane ∈ c.shape.lanes (index / c.shape.rowBytes) ∧
    cell = TcCopy.cell c.shape c.address cta lane index

/-- Copy `cp` leaves `value` in `cell`: the word of its row and column read from the cell's CTA,
the `k`-th of the copy. -/
def CpValue (X : Execution) (cp : EvId) (cell : Cell) (value : Value) : Prop :=
  ∃ c k cta operands row col lane, X.CpIssue cp c ∧ c.ctas[k]? = some cta ∧
    X.async.mmaOperands cp = some operands ∧ row < c.shape.rows ∧ col < c.shape.rowBytes / 4 ∧
    lane ∈ c.shape.lanes row ∧
    cell = TcCopy.cell c.shape c.address cta lane (row * c.shape.rowBytes + 4 * col) ∧
      TcCopy.cpWord c (operands.a.drop (k * c.shape.sourceBytes)) row col = some value

/-- Shift `sh` writes `cell` (THREAD-TC-SHIFT-CELLS). -/
def ShiftCell (X : Execution) (sh : EvId) (cell : Cell) : Prop :=
  ∃ s, X.ShiftIssue sh s ∧ s.Writes cell

/-- Shift `sh` reads `cell` (THREAD-TC-SHIFT-CELLS). -/
def ShiftReadCell (X : Execution) (sh : EvId) (cell : Cell) : Prop :=
  ∃ s, X.ShiftIssue sh s ∧ s.Reads cell

end
end PTX.TcMma

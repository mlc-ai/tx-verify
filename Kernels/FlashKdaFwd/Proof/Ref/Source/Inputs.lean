-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Direct
public import Kernels.FlashKdaFwd.Math.Batches

@[expose] public section

/-! # The launch bytes the tensor loads read

The tensor loads of the kernel read four global arrays: the values `v`, the gate logits `beta`,
the workspace (six arrays) and the initial state. This file says, from the precondition `Pre`
alone, that every byte of these arrays is a *launch input byte* (`InputByte`): it is in global
memory, the launch gives it a value, and it is no byte of the output array `out` and no byte of
the final state (`Pre`: the two output arrays overlap no input array).

* `WriteFrame P X`: every global write of the execution is to `out` or to the final state. This
  is the field `writeFrame` of `Proof/Top/Wire.lean: DirectFacts`, with the same statement, taken
  as a hypothesis by the theorems about the content of the loads. With it a launch input byte is
  written by nothing (`InputByte.unwritten`).
* `values_input` (byte `k < 256` of the row of token `tok < T_total` and head `h < H`),
  `logits_input` (byte `k < 2` of element `i < H * T_total`), `rows_input`, `total_input`,
  `square_input` (a byte of slot `i` of one of the three `[16, 128]` bf16 arrays, of `g_total`,
  of one of the two `[16, 16]` bf16 arrays, when the workspace holds a tile at slot `i`),
  `initial_input` and `initial_byte` (a byte of the initial state, with its value: a byte of the
  FP32 payload of the entry).
* `slot_lt`: the workspace slot of a tile of a sequence is a slot of the workspace.

Words: `T_total` is the number of tokens of the packed batch (`Params.total`), `H` the number
of heads; a *slot* is the index of one tile's data in each workspace array; a *payload* is a
float value as the model keeps it in memory (`Value.float fmt x`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every global write is to an output array**: a write, performed or pending, that covers a
byte of global memory covers a byte of `out` or of the final state. The statement of
`DirectFacts.writeFrame`. -/
def WriteFrame (P : Params) (X : Execution) : Prop :=
  ∀ w a l, X.Intent w a true → a.Covers l → l.space = .global → P.OutputByte l ∨ P.StateByte l

/-- **A launch input byte**: a byte of global memory that the launch gives a value and that is
no byte of the output array and no byte of the final state. -/
def InputByte (P : Params) (mem0 : Mem0) (l : Loc) : Prop :=
  l.space = .global ∧ (∃ v, mem0 l = some (some v)) ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l

/-- A launch input byte is allocated and is no output: the conclusion of
`DirectFacts.globalReadFrame`. -/
theorem InputByte.frame {l : Loc} (h : InputByte P mem0 l) :
    mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l := by
  obtain ⟨-, ⟨v, hv⟩, h1, h2⟩ := h
  exact ⟨by rw [hv]; simp, h1, h2⟩

/-- **No write covers a launch input byte**, when every global write is to an output array. -/
theorem InputByte.unwritten {l : Loc} (h : InputByte P mem0 l) (hW : WriteFrame P X) :
    ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers l :=
  fun w dst _ hw hc => (hW w dst l hw.intent hc h.1).elim h.2.2.1 h.2.2.2

/-- A byte of a range that is apart from the two output arrays is no byte of `out` and no byte
of the final state. -/
theorem not_output_of_apart {base bytes a : Nat}
    (ho : Apart P.tokenBytes bytes P.outputBase base)
    (hf : Apart P.stateBytes bytes P.finalBase base) (h1 : base ≤ a) (h2 : a < base + bytes) :
    ¬ P.OutputByte ⟨.global, 0, a⟩ ∧ ¬ P.StateByte ⟨.global, 0, a⟩ := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := Top.outputByte_range h
    simp only [Loc.mk.injEq, true_and] at he
    unfold Apart at ho
    omega
  · intro h
    obtain ⟨k, hk, he⟩ := Top.stateByte_range h
    simp only [Loc.mk.injEq, true_and] at he
    unfold Apart at hf
    omega

/-! ### The values and the gate logits -/

/-- **A byte of the values `v`**: byte `k` of the 256-byte row of token `tok` and head `h`. -/
theorem values_input (hpre : Pre P L mem0) {tok h k : Nat} (ht : tok < P.total)
    (hh : h < P.heads) (hk : k < 256) :
    InputByte P mem0 ⟨.global, 0, P.valuesBase + 256 * (tok * P.heads + h) + k⟩ := by
  obtain ⟨s, hs, t, htl, he⟩ := Math.Batches.token_owner P.length ht
  obtain ⟨n, -, q, -, -, hbytes⟩ := hpre.values s hs h hh t htl ⟨k / 2, by omega⟩
  have hb := hbytes (k % 2) (Nat.mod_lt _ (by decide))
  rw [← he] at hb
  have hl : (P.valueLoc tok h ⟨k / 2, by omega⟩).at (k % 2) =
      ⟨.global, 0, P.valuesBase + 256 * (tok * P.heads + h) + k⟩ := by
    simp only [Params.valueLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  rw [hl] at hb
  have hm : (tok + 1) * P.heads ≤ P.total * P.heads := Nat.mul_le_mul_right _ ht
  rw [Nat.add_mul, Nat.one_mul] at hm
  refine ⟨rfl, ⟨_, hb⟩, not_output_of_apart hpre.outputApartInputs.values
    hpre.finalApartInputs.values (by omega) ?_⟩
  unfold Params.tokenBytes
  omega

/-- **A byte of the gate logits `beta`**: byte `k` of element `i` of the `[H, T_total]`
array. -/
theorem logits_input (hpre : Pre P L mem0) {i k : Nat} (hi : i < P.heads * P.total)
    (hk : k < 2) : InputByte P mem0 ⟨.global, 0, P.logitsBase + 2 * i + k⟩ := by
  have hh : i / P.total < P.heads := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have htk : i % P.total < P.total := Nat.mod_lt _ hpre.totalPos
  obtain ⟨s, hs, t, htl, he⟩ := Math.Batches.token_owner P.length htk
  obtain ⟨n, -, q, -, -, hbytes⟩ := hpre.logits s hs (i / P.total) hh t htl
  have hb := hbytes k hk
  rw [← he] at hb
  have hidx : i / P.total * P.total + i % P.total = i := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod i P.total
  have hl : (P.logitLoc (i / P.total) (i % P.total)).at k =
      ⟨.global, 0, P.logitsBase + 2 * i + k⟩ := by
    simp only [Params.logitLoc, Loc.at, Loc.mk.injEq, true_and]
    rw [hidx]
  rw [hl] at hb
  refine ⟨rfl, ⟨_, hb⟩, not_output_of_apart hpre.outputApartInputs.logits
    hpre.finalApartInputs.logits (by omega) ?_⟩
  unfold Params.logitBytes
  omega

/-! ### The workspace -/

/-- **The workspace slot of a tile of a sequence is a slot of the workspace.** -/
theorem slot_lt (hpre : Pre P L mem0) {s h b : Nat} (hs : s < P.sequences) (hh : h < P.heads)
    (hb : b < tiles (P.length s)) : P.slot s h b < P.slots := by
  have h1 := Math.Batches.monotone_tile P.length (show s + 1 ≤ P.sequences from hs)
  rw [Math.Batches.firstTile_succ] at h1
  have h2 := hpre.tilesFit
  have h3 : (h + 1) * P.totalTiles ≤ P.heads * P.totalTiles := Nat.mul_le_mul_right _ hh
  rw [Nat.add_mul, Nat.one_mul] at h3
  unfold Params.slot Params.slots
  omega

/-- A byte of the workspace is apart from the outputs. -/
theorem workspace_apart (hpre : Pre P L mem0) {a : Nat} (h1 : P.workspaceBase ≤ a)
    (h2 : a < P.workspaceBase + P.workspaceBytes) :
    ¬ P.OutputByte ⟨.global, 0, a⟩ ∧ ¬ P.StateByte ⟨.global, 0, a⟩ :=
  not_output_of_apart hpre.outputApartInputs.workspace hpre.finalApartInputs.workspace h1 h2

/-- **A byte of one of the three row arrays** (`k_decayed`, `q_decayed`, `k_restored`: array
`a` at the per-tile offset `4096 a`): byte `k` of the 4096 bytes of slot `i`. -/
theorem rows_input (hpre : Pre P L mem0) {i : Nat} {w : Tile} (hW : P.TileStored mem0 i w)
    (hi : i < P.slots) {a k : Nat} (ha : a < 3) (hk : k < 4096) :
    InputByte P mem0 ⟨.global, 0, P.array (4096 * a) + 4096 * i + k⟩ := by
  have key : ∀ (off : Nat) (x : Fin 16 → Row 128),
      (∀ t f, bf16At mem0 (P.rowLoc off i t f) (x t f)) →
      ∃ v, mem0 ⟨.global, 0, P.array off + 4096 * i + k⟩ = some (some v) := by
    intro off x hx
    have hb := hx ⟨k / 256, by omega⟩ ⟨k % 256 / 2, by omega⟩ (k % 2) (Nat.mod_lt _ (by decide))
    have hl : (P.rowLoc off i ⟨k / 256, by omega⟩ ⟨k % 256 / 2, by omega⟩).at (k % 2) =
        ⟨.global, 0, P.array off + 4096 * i + k⟩ := by
      simp only [Params.rowLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
    rw [hl] at hb
    exact ⟨_, hb⟩
  have hdef : ∃ v, mem0 ⟨.global, 0, P.array (4096 * a) + 4096 * i + k⟩ = some (some v) := by
    interval_cases a
    · exact key 0 _ hW.decayedKey
    · exact key 4096 _ hW.decayedQuery
    · exact key 8192 _ hW.restoredKey
  refine ⟨rfl, hdef, workspace_apart hpre ?_ ?_⟩ <;>
    simp only [Params.array, workspaceArray, Params.workspaceBytes, Params.slots] at * <;>
    interval_cases a <;> omega

/-- **A byte of `g_total`**: byte `k` of the 512 bytes of slot `i`. -/
theorem total_input (hpre : Pre P L mem0) {i : Nat} {w : Tile} (hW : P.TileStored mem0 i w)
    (hi : i < P.slots) {k : Nat} (hk : k < 512) :
    InputByte P mem0 ⟨.global, 0, P.array 12288 + 512 * i + k⟩ := by
  have hb := hW.totalDecay ⟨k / 4, by omega⟩ (k % 4) (Nat.mod_lt _ (by decide))
  have hl : (P.totalDecayLoc i ⟨k / 4, by omega⟩).at (k % 4) =
      ⟨.global, 0, P.array 12288 + 512 * i + k⟩ := by
    simp only [Params.totalDecayLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  rw [hl] at hb
  refine ⟨rfl, ⟨_, hb⟩, workspace_apart hpre ?_ ?_⟩ <;>
    simp only [Params.array, workspaceArray, Params.workspaceBytes, Params.slots] at * <;> omega

/-- **A byte of one of the two square arrays** (`INV`, `Mqk`: array `a` at the per-tile offset
`12800 + 512 a`): byte `k` of the 512 bytes of slot `i`. -/
theorem square_input (hpre : Pre P L mem0) {i : Nat} {w : Tile} (hW : P.TileStored mem0 i w)
    (hi : i < P.slots) {a k : Nat} (ha : a < 2) (hk : k < 512) :
    InputByte P mem0 ⟨.global, 0, P.array (12800 + 512 * a) + 512 * i + k⟩ := by
  have key : ∀ (off : Nat) (x : Matrix (Fin 16) (Fin 16) ℝ),
      (∀ t j, bf16At mem0 (P.squareLoc off i t j) (x t j)) →
      ∃ v, mem0 ⟨.global, 0, P.array off + 512 * i + k⟩ = some (some v) := by
    intro off x hx
    have hb := hx ⟨k / 32, by omega⟩ ⟨k % 32 / 2, by omega⟩ (k % 2) (Nat.mod_lt _ (by decide))
    have hl : (P.squareLoc off i ⟨k / 32, by omega⟩ ⟨k % 32 / 2, by omega⟩).at (k % 2) =
        ⟨.global, 0, P.array off + 512 * i + k⟩ := by
      simp only [Params.squareLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
    rw [hl] at hb
    exact ⟨_, hb⟩
  have hdef : ∃ v, mem0 ⟨.global, 0, P.array (12800 + 512 * a) + 512 * i + k⟩ =
      some (some v) := by
    interval_cases a
    · exact key 12800 _ hW.inverse
    · exact key 13312 _ hW.score
  refine ⟨rfl, hdef, workspace_apart hpre ?_ ?_⟩ <;>
    simp only [Params.array, workspaceArray, Params.workspaceBytes, Params.slots] at * <;>
    interval_cases a <;> omega

/-! ### The initial state -/

/-- **A byte of the initial state**, by offset in the array. -/
theorem initial_input (hpre : Pre P L mem0) {k : Nat} (hk : k < P.stateBytes) :
    InputByte P mem0 ⟨.global, 0, P.initialBase + k⟩ := by
  obtain ⟨h1, h2, h3⟩ := Startup.initial_frame hpre hk
  refine ⟨rfl, ?_, h2, h3⟩
  cases hm : mem0 ⟨.global, 0, P.initialBase + k⟩ with
  | none => exact absurd hm h1
  | some o =>
    -- the launch value is a byte of a payload (`Pre.initialState`), so it is defined
    unfold Params.stateBytes at hk
    have hH := hpre.headsPos
    have hp : k / 65536 < P.sequences * P.heads := by omega
    have hs : k / 65536 / P.heads < P.sequences := Nat.div_lt_of_lt_mul (by
      rwa [Nat.mul_comm] at hp)
    have hh : k / 65536 % P.heads < P.heads := Nat.mod_lt _ hH
    have hpl : k / 65536 / P.heads * P.heads + k / 65536 % P.heads = k / 65536 := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod _ _
    have h := hpre.initialState _ hs _ hh ⟨k % 65536 / 512, by omega⟩ ⟨k % 512 / 4, by omega⟩
      (k % 4) (Nat.mod_lt _ (by decide))
    have hl : (P.initialLoc (k / 65536 / P.heads) (k / 65536 % P.heads)
        ⟨k % 65536 / 512, by omega⟩ ⟨k % 512 / 4, by omega⟩).at (k % 4) =
        ⟨.global, 0, P.initialBase + k⟩ := by
      simp only [Params.initialLoc, Loc.at, Loc.mk.injEq, true_and, hpl]
      omega
    rw [hl, hm] at h
    exact ⟨_, h⟩

/-- **The value of a byte of the initial state**: byte `b` of the FP32 payload of entry
(value channel `v`, key feature `kf`) of sequence `s` and head `h`. -/
theorem initial_byte (hpre : Pre P L mem0) {s h : Nat} (hs : s < P.sequences) (hh : h < P.heads)
    (v kf : Fin 128) {b : Nat} (hb : b < 4) :
    mem0 ⟨.global, 0, P.initialBase + 65536 * (s * P.heads + h) + 512 * v.val + 4 * kf.val + b⟩ =
      some (some ((Value.float .f32 (P.initial s h v kf)).byteAt b)) :=
  hpre.initialState s hs h hh v kf b hb

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source

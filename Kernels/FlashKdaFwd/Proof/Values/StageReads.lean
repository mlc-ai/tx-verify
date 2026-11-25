-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Batches
public import Kernels.FlashKdaFwd.Proof.Values.Hyps
public import Kernels.FlashKdaFwd.Proof.Values.TileInputs

@[expose] public section

/-!
# What a compute lane reads from the input stage

The value induction (`Hyps.lean`) assumes what a lane of a compute warp reads in the tile loop:
`ScalarsRead` for the eighteen scalar loads of a tile and `RowsRead` for the row reads of its
44 `ldmatrix` instructions. This file derives the first, and the part of the second whose rows
are in the input stage, from the three contracts of `Contract.lean` and the launch
precondition `Pre P L mem0` of `Spec.lean` (`P` are the parameters of the launch, `L` the
launch, `mem0` the memory before it; `X` is the execution).

Words and names used below.

* A *compute warp* of thread block `c` has the first thread `w0 = c * L.block + 32 * w`, with
  the warp number `w < 4`; its *lane* `l < 32` is the thread `w0 + l`. The block works on the
  sequence `c % P.sequences` and the head `c / P.sequences`. A *tile* is 16 consecutive tokens
  of the sequence, its *rows*; the tile of a position `k` of the lane's trace is
  `ordinal X (w0 + l) k / 182`, the number of warp matrix events before the position divided by
  the 182 matrix instructions of a tile.
* The *input stage* of tile `b` is the 18048-byte buffer of shared memory at offset
  `32768 + 18048 * (b % 3)` that the tile's tensor loads fill. `stageByte P mem0 s h b o` is
  its byte at offset `o` as a function of the launch memory (`Contract.lean`). Its parts are
  the values `v` (offset 0), the gate logits `beta` (4096), the workspace arrays `k_decayed`
  (4224), `q_decayed` (8320), `k_restored` (12416), `g_total` (16512), `INV` (17024) and `Mqk`
  (17536).
* `tileInputs P mem0 s h b` (`TileInputs.lean`) are the real arrays of tile `b` of sequence `s`
  and head `h`, read off the launch memory.
* `ComputeRef` gives the address of a read (`loadRow`, `scalarLoad`) and the number of
  successful polls of the stage's "full" mbarrier before it (`polled`); `ReadBack.stage` turns
  the two into the bytes `stageByte`; `TileBound` says the tile of the read is a tile of the
  sequence, so the precondition names what the workspace holds there (`Pre.workspace`).
* A *bit pattern* is a finite bfloat16 number stored as a raw 16-bit integer (the form of `v`
  and `beta` in launch memory, `bf16Bits`); a *payload* is a number stored as a float value
  (the form of the workspace arrays, `bf16At` and `f32At`). `bf16Num` is the number of the bit
  pattern at a location.

Results.

* `scalar_read_of`, `scalars_read_of`: one scalar load, and `ScalarsRead`, for every family
  `xs` of real arrays whose `g_total` is that of the workspace and whose gate logits are
  `stageLogit`, the logits the stage holds.
* `scalars_read`: `ScalarsRead` for the family `tileInputs`.
* `rows_read_stage`: the statement of `RowsRead` for the family `tileInputs`, for every
  `ldmatrix` whose source is not `state_acc` (the sources `tilesA`, `restored` and `values` of
  `Loads.lean`).

The gate logits of `tileInputs` are defined as the stage holds them (`stageLogit`): `beta` is
one array `[heads, tokens]` and a tile loads 32 consecutive elements of it, so for a head that
is not the last one the padding rows past the end of the batch hold the logits of the first
tokens of the next head, and payload zeros only past the end of the whole array.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (tiles firstToken)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## Bit patterns and small facts -/

/-- Two bit patterns at one location are the same number. -/
private theorem bf16Bits_unique {m : Mem0} {l : Loc} {x y : ℝ} (hx : bf16Bits m l x)
    (hy : bf16Bits m l y) : x = y := by
  obtain ⟨n, hn, q, hq, rfl, hm⟩ := hx
  obtain ⟨n', hn', q', hq', rfl, hm'⟩ := hy
  have h0 := (hm 0 (by norm_num)).symm.trans (hm' 0 (by norm_num))
  have hb : BitVec.ofNat 64 n = BitVec.ofNat 64 n' := by
    simpa [Value.byteAt] using h0
  have hnn : n = n' := by
    have := congrArg BitVec.toNat hb
    simp only [BitVec.toNat_ofNat] at this
    omega
  subst hnn
  rw [hq] at hq'
  rw [Option.some.inj hq']

/-- The number of the bit pattern at a location that holds the pattern of `x` is `x`. -/
private theorem bf16Num_eq {m : Mem0} {l : Loc} {x : ℝ} (hx : bf16Bits m l x) :
    bf16Num m l = x := by
  have h : ∃ y : ℝ, bf16Bits m l y := ⟨x, hx⟩
  unfold bf16Num
  rw [dite_eq_left h]
  exact bf16Bits_unique h.choose_spec hx

private theorem loc_congr {sp : Space} {c x y : ℕ} (h : x = y) :
    (⟨sp, c, x⟩ : Loc) = ⟨sp, c, y⟩ := by rw [h]

private theorem map_range_two {α : Type} (f : ℕ → α) : (List.range 2).map f = [f 0, f 1] := rfl

/-! ## The bytes of a stage, by array

In each lemma the offset is split into the piece `p` of 256 bytes (eight features or channels),
the row `r` of the tile and the byte `i` of the row's 16 bytes in the piece. -/

section stage
variable (P) (mem0) (s h b : ℕ)

private theorem stageByte_values {p r i : ℕ} (hp : p < 16) (hr : r < 16) (hi : i < 16) :
    stageByte P mem0 s h b (256 * p + 16 * r + i) =
      if firstToken P.length s + 16 * b + r < P.total then
        (mem0 ⟨.global, 0, P.valuesBase +
          256 * ((firstToken P.length s + 16 * b + r) * P.heads + h) + 16 * p + i⟩).join
      else some ((Value.float .bf16 0).byteAt (i % 2)) := by
  have e1 : (256 * p + 16 * r + i) % 256 / 16 = r := by omega
  have e2 : (256 * p + 16 * r + i) / 256 = p := by omega
  have e3 : (256 * p + 16 * r + i) % 16 = i := by omega
  have e4 : (256 * p + 16 * r + i) % 2 = i % 2 := by omega
  simp only [stageByte]
  rw [ite_eq_left (by omega), e1, e2, e3, e4]

private theorem stageByte_logits {j : ℕ} (hj : j < 64) :
    stageByte P mem0 s h b (4096 + j) =
      if 8 * ((h * P.total + (firstToken P.length s + 16 * b)) / 8) + j / 2 <
          P.heads * P.total then
        (mem0 ⟨.global, 0, P.logitsBase +
          2 * (8 * ((h * P.total + (firstToken P.length s + 16 * b)) / 8) + j / 2) +
          j % 2⟩).join
      else some ((Value.float .bf16 0).byteAt (j % 2)) := by
  have e1 : (4096 + j - 4096) / 2 = j / 2 := by omega
  have e2 : (4096 + j) % 2 = j % 2 := by omega
  simp only [stageByte]
  rw [ite_eq_right (by omega), ite_eq_left (by omega), e1, e2]

/-- The arrays `k_decayed`, `q_decayed`, `k_restored` (`a` is 0, 1, 2): `base` is the offset of
the array in the stage and `off` its per-tile offset in the workspace. -/
private theorem stageByte_rows {a base off p r i : ℕ} (ha : a < 3)
    (hbase : base = 4224 + 4096 * a) (hoff : off = 4096 * a) (hp : p < 16) (hr : r < 16)
    (hi : i < 16) :
    stageByte P mem0 s h b (base + 256 * p + 16 * r + i) =
      (mem0 ⟨.global, 0, P.array off + 4096 * P.slot s h b + 256 * r + 16 * p + i⟩).join := by
  subst hbase hoff
  have e0 : (4224 + 4096 * a + 256 * p + 16 * r + i - 4224) / 4096 = a := by omega
  have e : (4224 + 4096 * a + 256 * p + 16 * r + i - 4224) % 4096 =
      256 * p + 16 * r + i := by omega
  have e1 : (256 * p + 16 * r + i) % 256 / 16 = r := by omega
  have e2 : (256 * p + 16 * r + i) / 256 = p := by omega
  have e3 : (256 * p + 16 * r + i) % 16 = i := by omega
  simp only [stageByte]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega), e0, e, e1, e2, e3]

private theorem stageByte_decay {j : ℕ} (hj : j < 512) :
    stageByte P mem0 s h b (16512 + j) =
      (mem0 ⟨.global, 0, P.array 12288 + 512 * P.slot s h b + j⟩).join := by
  have e : 16512 + j - 16512 = j := by omega
  simp only [stageByte]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega), e]

/-- The arrays `INV` and `Mqk` (`a` is 0, 1): `base` is the offset of the array in the stage
and `off` its per-tile offset in the workspace. -/
private theorem stageByte_squares {a base off p r i : ℕ} (ha : a < 2)
    (hbase : base = 17024 + 512 * a) (hoff : off = 12800 + 512 * a) (hp : p < 2) (hr : r < 16)
    (hi : i < 16) :
    stageByte P mem0 s h b (base + 256 * p + 16 * r + i) =
      (mem0 ⟨.global, 0, P.array off + 512 * P.slot s h b + 32 * r + 16 * p + i⟩).join := by
  subst hbase hoff
  have e0 : (17024 + 512 * a + 256 * p + 16 * r + i - 17024) / 512 = a := by omega
  have e : (17024 + 512 * a + 256 * p + 16 * r + i - 17024) % 512 =
      256 * p + 16 * r + i := by omega
  have e1 : (256 * p + 16 * r + i) % 256 / 16 = r := by omega
  have e2 : (256 * p + 16 * r + i) / 256 = p := by omega
  have e3 : (256 * p + 16 * r + i) % 16 = i := by omega
  simp only [stageByte]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), e0, e, e1, e2, e3]

/-- The two bytes of the gate logit of row `t`: the tile loads 32 elements of `beta` from the
index of its first token rounded down to 8, so row `t` is element
`(h * P.total + firstToken P.length s) % 8 + t` of the 32. -/
private theorem stageByte_logit {t k : ℕ} (ht : t < 16) (hk : k < 2) :
    stageByte P mem0 s h b
        (4096 + 2 * ((h * P.total + firstToken P.length s) % 8 + t) + k) =
      if h * P.total + (firstToken P.length s + 16 * b + t) < P.heads * P.total then
        (mem0 ((P.logitLoc h (firstToken P.length s + 16 * b + t)).at k)).join
      else some ((Value.float .bf16 0).byteAt k) := by
  have e1 : 8 * ((h * P.total + (firstToken P.length s + 16 * b)) / 8) +
      (2 * ((h * P.total + firstToken P.length s) % 8 + t) + k) / 2 =
      h * P.total + (firstToken P.length s + 16 * b + t) := by omega
  have e2 : (2 * ((h * P.total + firstToken P.length s) % 8 + t) + k) % 2 = k := by omega
  rw [Nat.add_assoc, stageByte_logits P mem0 s h b (by omega), e1, e2]
  rfl

end stage

/-! ## The thread-dependent part of an address

`bitsOff` (`Contract.lean`) is the sum of the weights of the set bits of the thread's index in
its block, here `32 * w + l`. -/

private theorem bitsOff_rows (w : ℕ) {l : ℕ} (hl : l < 32) :
    bitsOff [16, 32, 64, 128, 256, 0, 0] (32 * w + l) = 256 * (l / 16) + 16 * (l % 16) := by
  simp [bitsOff, List.zipIdx]
  omega

private theorem bitsOff_values {w l : ℕ} (hw : w < 4) (hl : l < 32) :
    bitsOff [16, 32, 64, 128, 256, 1024, 2048] (32 * w + l) =
      256 * (4 * w + l / 16) + 16 * (l % 16) := by
  simp [bitsOff, List.zipIdx]
  omega

private theorem bitsOff_restored (w : ℕ) {l : ℕ} (hl : l < 32) :
    bitsOff [16, 32, 64, 256, 128, 0, 0] (32 * w + l) =
      256 * (l / 8 % 2) + 16 * (l % 8 + 8 * (l / 16)) := by
  simp [bitsOff, List.zipIdx]
  omega

private theorem bitsOff_logit (w : ℕ) {l : ℕ} (hl : l < 32) :
    bitsOff [0, 0, 2, 4, 8, 0, 0] (32 * w + l) = 2 * (l / 4) := by
  simp [bitsOff, List.zipIdx]
  omega

private theorem bitsOff_decay (w : ℕ) {l : ℕ} (hl : l < 32) :
    bitsOff [0, 0, 4, 8, 16, 0, 0] (32 * w + l) = 4 * (l / 4) := by
  simp [bitsOff, List.zipIdx]
  omega

/-! ## What launch memory holds -/

/-- A byte of a `[slots, 16, 128]` workspace array of payloads: row `r`, feature
`f = 8 p + i / 2`. -/
private theorem rows_byte {m : Mem0} {off n : ℕ} {wt : Fin 16 → Recurrence.Row 128}
    (hst : ∀ t f, bf16At m (P.rowLoc off n t f) (wt t f)) {p r i f : ℕ} (hr : r < 16)
    (hf : f < 128) (e : f = 8 * p + i / 2) :
    (m ⟨.global, 0, P.array off + 4096 * n + 256 * r + 16 * p + i⟩).join =
      bf16Enc (wt ⟨r, hr⟩ ⟨f, hf⟩) (i % 2) := by
  have h := hst ⟨r, hr⟩ ⟨f, hf⟩ (i % 2) (by omega)
  have e' : (⟨.global, 0, P.array off + 4096 * n + 256 * r + 16 * p + i⟩ : Loc) =
      (P.rowLoc off n ⟨r, hr⟩ ⟨f, hf⟩).at (i % 2) :=
    loc_congr (by simp only [Params.rowLoc]; omega)
  rw [e', h]
  rfl

/-- A byte of a `[slots, 16, 16]` workspace array of payloads: row `r`, column
`f = 8 p + i / 2`. -/
private theorem squares_byte {m : Mem0} {off n : ℕ} {wt : Matrix (Fin 16) (Fin 16) ℝ}
    (hst : ∀ t j, bf16At m (P.squareLoc off n t j) (wt t j)) {p r i f : ℕ} (hr : r < 16)
    (hf : f < 16) (e : f = 8 * p + i / 2) :
    (m ⟨.global, 0, P.array off + 512 * n + 32 * r + 16 * p + i⟩).join =
      bf16Enc (wt ⟨r, hr⟩ ⟨f, hf⟩) (i % 2) := by
  have h := hst ⟨r, hr⟩ ⟨f, hf⟩ (i % 2) (by omega)
  have e' : (⟨.global, 0, P.array off + 512 * n + 32 * r + 16 * p + i⟩ : Loc) =
      (P.squareLoc off n ⟨r, hr⟩ ⟨f, hf⟩).at (i % 2) :=
    loc_congr (by simp only [Params.squareLoc]; omega)
  rw [e', h]
  rfl

/-- Byte `k` of entry `f` of `g_total`. -/
private theorem decay_byte {m : Mem0} {n : ℕ} {wt : Recurrence.Row 128}
    (hst : ∀ f, f32At m (P.totalDecayLoc n f) (wt f)) {f k : ℕ} (hf : f < 128) (hk : k < 4) :
    (m ⟨.global, 0, P.array 12288 + 512 * n + (4 * f + k)⟩).join =
      some ((Value.float .f32 (wt ⟨f, hf⟩)).byteAt k) := by
  have h := hst ⟨f, hf⟩ k hk
  have e : (⟨.global, 0, P.array 12288 + 512 * n + (4 * f + k)⟩ : Loc) =
      (P.totalDecayLoc n ⟨f, hf⟩).at k :=
    loc_congr (by simp only [Params.totalDecayLoc]; omega)
  rw [e, h]
  rfl

/-- Every element of `beta` is a bit pattern: the precondition names the elements by sequence
and token, and every token of the batch belongs to a sequence (`Math.Batches.token_owner`). -/
private theorem logit_bits (hpre : Pre P L mem0) {h tk : ℕ}
    (hlt : h * P.total + tk < P.heads * P.total) : ∃ x, bf16Bits mem0 (P.logitLoc h tk) x := by
  have hpos := hpre.totalPos
  have h1 : (h * P.total + tk) / P.total < P.heads :=
    Nat.div_lt_of_lt_mul (Nat.mul_comm P.heads P.total ▸ hlt)
  have h2 : (h * P.total + tk) % P.total < P.total := Nat.mod_lt _ hpos
  obtain ⟨s', hs', t', ht', e⟩ := Math.Batches.token_owner P.length h2
  have hb := hpre.logits s' hs' _ h1 t' ht'
  rw [← e] at hb
  have eloc : P.logitLoc ((h * P.total + tk) / P.total) ((h * P.total + tk) % P.total) =
      P.logitLoc h tk := by
    unfold Params.logitLoc
    rw [Nat.div_add_mod']
  rw [eloc] at hb
  exact ⟨_, hb⟩

/-- Every element of `v` is a bit pattern. -/
private theorem value_bits (hpre : Pre P L mem0) {h tk : ℕ} (hh : h < P.heads)
    (htk : tk < P.total) (v : Fin 128) : ∃ x, bf16Bits mem0 (P.valueLoc tk h v) x := by
  obtain ⟨s', hs', t', ht', e⟩ := Math.Batches.token_owner P.length htk
  have hb := hpre.values s' hs' h hh t' ht' v
  rw [← e] at hb
  exact ⟨_, hb⟩

/-! ## The lanes of a compute warp -/

/-- The thread `c * L.block + 32 * w + l` is in block `c`, where its index is `32 * w + l`; the
block works on sequence `c % P.sequences` and head `c / P.sequences`. -/
private theorem lane_facts (hpre : Pre P L mem0) {c w w0 l : ℕ} (hw : w < 4)
    (hw0 : w0 = c * L.block + 32 * w) (hl : l < 32) :
    (w0 + l) / L.block = c ∧ (w0 + l) % L.block = 32 * w + l ∧
      seqOf P L (w0 + l) = c % P.sequences ∧ headOf P L (w0 + l) = c / P.sequences := by
  have hblk := hpre.block
  have hdiv : (w0 + l) / L.block = c := by rw [hw0, hblk]; omega
  have hmod : (w0 + l) % L.block = 32 * w + l := by rw [hw0, hblk]; omega
  refine ⟨hdiv, hmod, ?_, ?_⟩
  · unfold seqOf
    rw [hdiv]
  · unfold headOf
    rw [hdiv]

/-! ## The scalar loads -/

/-- **The gate logit of row `t` of tile `b`** of sequence `s` and head `h`, as the input stage
holds it: the number of the bit pattern of `beta` at the token `firstToken P.length s + 16 * b
+ t` of head `h`, or zero when that element is past the end of the array `beta[heads, tokens]`.
For a row past the end of the batch that is not past the end of the array this is a logit of
the next head. -/
def stageLogit (P : Params) (mem0 : Mem0) (s h b t : ℕ) : ℝ :=
  if h * P.total + (firstToken P.length s + 16 * b + t) < P.heads * P.total then
    bf16Num mem0 (P.logitLoc h (firstToken P.length s + 16 * b + t))
  else 0

/-- The two classes of scalar loads of the tile loop, by load site: the sites 159 and 160 read
a gate logit and the sites 161 to 176 an entry of `g_total`; each with its entry of
`Gen.scalarForms` and its source. -/
private theorem scalar_site (i : Fin 178) (h1 : 159 ≤ i.val) (h2 : i.val < 177) :
    (i.val < 161 ∧
      ((Site.load i).pc, 2, 36864 + 16 * (i.val - 159), 2, [0, 0, 2, 4, 8, 0, 0]) ∈
        Gen.scalarForms ∧
      scalarSrc i.val = .logit (i.val - 159)) ∨
    (161 ≤ i.val ∧
      ((Site.load i).pc, 4, 49280 + 32 * (i.val - 161), 0, [0, 0, 4, 8, 16, 0, 0]) ∈
        Gen.scalarForms ∧
      scalarSrc i.val = .decay ((i.val - 161) / 2) ((i.val - 161) % 2)) := by
  obtain ⟨n, hn⟩ := i
  simp only at h1 h2
  interval_cases n <;> decide +revert

/-- **The bytes of one scalar load**, for a family `xs` of real arrays whose `g_total` is the
workspace's and whose gate logits are those of the stage (`stageLogit`): lane `l` of the
compute warp `w` of block `c`, at one of the eighteen scalar loads of a tile (the load sites
159 to 176), reads the bytes of the load's source for the arrays of its tile. -/
theorem scalar_read_of (hpre : Pre P L mem0) (F : Followed L mem0 X) (R : ComputeRef P L X)
    (B : ReadBack P L mem0 X) (hT : TileBound P L X) {c w w0 : ℕ} (hc : c < L.grid)
    (hw : w < 4) (hw0 : w0 = c * L.block + 32 * w) {xs : ℕ → Inputs}
    (hdecay : ∀ b < tiles (P.length (c % P.sequences)), ∀ f : Fin 128,
      (xs b).totalDecay f = (P.tile (c % P.sequences) (c / P.sequences) b).totalDecay f)
    (hlogit : ∀ b < tiles (P.length (c % P.sequences)), ∀ t < 16,
      (xs b).logit t = stageLogit P mem0 (c % P.sequences) (c / P.sequences) b t)
    {l k : ℕ} (hl : l < 32) {d : (code L (w0 + l)).D} {e : Event} {i : Fin 178}
    (hi : 159 ≤ i.val) (hi' : i.val < 177)
    (hσ : stateAt (code L) X (w0 + l) k = some (some d)) (hs : d.site = .load i)
    (he : X.get (w0 + l, k) = some e) :
    ∃ pc a bs, e = ⟨pc, .rd a bs⟩ ∧
      (scalarSrc i).Bytes (xs (ordinal X (w0 + l) k / 182)) l bs := by
  obtain ⟨hdiv, hmod, hseq, hhead⟩ := lane_facts hpre hw hw0 hl
  have hg : w0 + l < L.threads := lt_of_get F.consistent he
  have hcomp : (w0 + l) % L.block < 128 := by omega
  have hsS : c % P.sequences < P.sequences := Nat.mod_lt _ hpre.sequencesPos
  have hhH : c / P.sequences < P.heads := Nat.div_lt_of_lt_mul (hpre.grid ▸ hc)
  have hb : ordinal X (w0 + l) k / 182 < tiles (P.length (c % P.sequences)) := by
    have := hT (w0 + l) k d hcomp hσ (Or.inr ⟨i, hi, hi', hs⟩)
    rwa [tileCount, hseq] at this
  have hpc : d.site.pc = (Site.load i).pc := by rw [hs]
  rcases scalar_site i hi hi' with ⟨hlt161, hmem, hsrc⟩ | ⟨hge, hmem, hsrc⟩
  · -- a gate logit: two bytes of `beta`
    obtain ⟨a, bs, rfl, hsz, hloc⟩ :=
      R.scalarLoad (w0 + l) k d e _ _ _ _ _ hcomp hσ hmem hpc he
    have hpol := R.polled (w0 + l) k d _ hcomp hσ he (Or.inr ⟨_, _, _, _, hpc ▸ hmem⟩)
    have hG : gateOff P L (w0 + l) =
        ((c / P.sequences) * P.total + firstToken P.length (c % P.sequences)) % 8 := by
      unfold gateOff
      rw [hseq, hhead, Nat.mul_comm]
    rw [hG, hmod, bitsOff_logit w hl] at hloc
    have hbs := B.stage (w0 + l) k _ a bs _
      (4096 + 2 * (((c / P.sequences) * P.total + firstToken P.length (c % P.sequences)) % 8 +
        (l / 4 + 8 * (i.val - 159)))) hg hcomp he hpol
      (by rw [hloc]; exact loc_congr (by omega)) (Or.inl (by omega))
    rw [hsz, hseq, hhead, map_range_two] at hbs
    rw [stageByte_logit P mem0 _ _ _ (by omega) (by omega),
      stageByte_logit P mem0 _ _ _ (by omega) (by omega)] at hbs
    refine ⟨_, a, bs, rfl, ?_⟩
    rw [hsrc]
    have hx := hlogit _ hb (l / 4 + 8 * (i.val - 159)) (by omega)
    unfold stageLogit at hx
    show _ ∨ _
    by_cases hlt : (c / P.sequences) * P.total + (firstToken P.length (c % P.sequences) +
        16 * (ordinal X (w0 + l) k / 182) + (l / 4 + 8 * (i.val - 159))) < P.heads * P.total
    · rw [ite_eq_left hlt] at hx
      rw [ite_eq_left hlt, ite_eq_left hlt] at hbs
      obtain ⟨x, hbits⟩ := logit_bits hpre hlt
      rw [bf16Num_eq hbits] at hx
      obtain ⟨n, hn, q, hq, hqx, hm⟩ := hbits
      rw [hm 0 (by omega), hm 1 (by omega)] at hbs
      exact Or.inl ⟨n, hn, q, hq, hqx.trans hx.symm, hbs⟩
    · rw [ite_eq_right hlt] at hx
      rw [ite_eq_right hlt, ite_eq_right hlt] at hbs
      exact Or.inr ⟨hx, hbs⟩
  · -- an entry of `g_total`: four bytes of an FP32 payload
    obtain ⟨a, bs, rfl, hsz, hloc⟩ :=
      R.scalarLoad (w0 + l) k d e _ _ _ _ _ hcomp hσ hmem hpc he
    have hpol := R.polled (w0 + l) k d _ hcomp hσ he (Or.inr ⟨_, _, _, _, hpc ▸ hmem⟩)
    rw [hmod, bitsOff_decay w hl] at hloc
    have hf : 16 * ((i.val - 161) / 2) + l / 4 + 8 * ((i.val - 161) % 2) < 128 := by omega
    have hbs := B.stage (w0 + l) k _ a bs _
      (16512 + 4 * (16 * ((i.val - 161) / 2) + l / 4 + 8 * ((i.val - 161) % 2))) hg hcomp he hpol
      (by rw [hloc]; exact loc_congr (by omega)) (Or.inr (by omega))
    rw [hsz, hseq, hhead] at hbs
    refine ⟨_, a, bs, rfl, ?_⟩
    rw [hsrc]
    show bs = _
    have hst := (hpre.workspace _ hsS _ hhH _ hb).totalDecay
    rw [hbs, hdecay _ hb ⟨_, hf⟩]
    show _ = ((List.range 4).map _).map some
    rw [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [Nat.add_assoc, stageByte_decay P mem0 _ _ _ (by omega), decay_byte hst hf hj']
    rfl

/-- **The bytes of the scalar loads**, for a family `xs` as in `scalar_read_of`: the hypothesis
`ScalarsRead` of the value induction for the compute warp `w` of block `c`. -/
theorem scalars_read_of (hpre : Pre P L mem0) (F : Followed L mem0 X) (R : ComputeRef P L X)
    (B : ReadBack P L mem0 X) (hT : TileBound P L X) {c w w0 : ℕ} (hc : c < L.grid)
    (hw : w < 4) (hw0 : w0 = c * L.block + 32 * w) {xs : ℕ → Inputs}
    (hdecay : ∀ b < tiles (P.length (c % P.sequences)), ∀ f : Fin 128,
      (xs b).totalDecay f = (P.tile (c % P.sequences) (c / P.sequences) b).totalDecay f)
    (hlogit : ∀ b < tiles (P.length (c % P.sequences)), ∀ t < 16,
      (xs b).logit t = stageLogit P mem0 (c % P.sequences) (c / P.sequences) b t) :
    ScalarsRead (L := L) xs X w0 := fun _ hl _ _ _ _ hi hi' hσ hs he =>
  scalar_read_of hpre F R B hT hc hw hw0 hdecay hlogit hl hi hi' hσ hs he

/-- **The bytes of the scalar loads, for the arrays of the launch** (`tileInputs`): the
hypothesis `ScalarsRead` of the value induction for the compute warp `w` of block `c`. The gate
logits of `tileInputs` are by definition what the stage holds (`stageLogit`). -/
theorem scalars_read (hpre : Pre P L mem0) (F : Followed L mem0 X) (R : ComputeRef P L X)
    (B : ReadBack P L mem0 X) (hT : TileBound P L X) {c w w0 : ℕ} (hc : c < L.grid)
    (hw : w < 4) (hw0 : w0 = c * L.block + 32 * w) :
    ScalarsRead (L := L)
      (fun b => tileInputs P mem0 (c % P.sequences) (c / P.sequences) b) X w0 :=
  scalars_read_of hpre F R B hT hc hw hw0 (fun _ _ f => dite_eq_left f.isLt)
    (fun _ _ _ _ => rfl)

/-! ## The row reads of the input stage -/

section rows
variable {s h b : ℕ}

/-- A byte of `k_decayed` in the stage: the payload of row `r` and feature `f = 8 p + i / 2`
of the arrays of the tile. -/
private theorem kd_byte (T : P.TileStored mem0 (P.slot s h b) (P.tile s h b)) {p r i f : ℕ}
    (hr : r < 16) (hf : f < 128) (hi : i < 16) (e : f = 8 * p + i / 2) :
    stageByte P mem0 s h b (4224 + 256 * p + 16 * r + i) =
      bf16Enc ((tileInputs P mem0 s h b).decayedKey r f) (i % 2) := by
  rw [stageByte_rows P mem0 s h b (a := 0) (base := 4224) (off := 0) (p := p) (by omega)
      (by omega) (by omega) (by omega) hr hi,
    rows_byte T.decayedKey hr hf e]
  have ht : (tileInputs P mem0 s h b).decayedKey r f =
      (P.tile s h b).decayedKey ⟨r, hr⟩ ⟨f, hf⟩ := dite_eq_left ⟨hr, hf⟩
  rw [ht]

/-- A byte of `q_decayed` in the stage. -/
private theorem qd_byte (T : P.TileStored mem0 (P.slot s h b) (P.tile s h b)) {p r i f : ℕ}
    (hr : r < 16) (hf : f < 128) (hi : i < 16) (e : f = 8 * p + i / 2) :
    stageByte P mem0 s h b (8320 + 256 * p + 16 * r + i) =
      bf16Enc ((tileInputs P mem0 s h b).decayedQuery r f) (i % 2) := by
  rw [stageByte_rows P mem0 s h b (a := 1) (base := 8320) (off := 4096) (p := p) (by omega)
      (by omega) (by omega) (by omega) hr hi,
    rows_byte T.decayedQuery hr hf e]
  have ht : (tileInputs P mem0 s h b).decayedQuery r f =
      (P.tile s h b).decayedQuery ⟨r, hr⟩ ⟨f, hf⟩ := dite_eq_left ⟨hr, hf⟩
  rw [ht]

/-- A byte of `k_restored` in the stage. -/
private theorem rk_byte (T : P.TileStored mem0 (P.slot s h b) (P.tile s h b)) {p r i f : ℕ}
    (hr : r < 16) (hf : f < 128) (hi : i < 16) (e : f = 8 * p + i / 2) :
    stageByte P mem0 s h b (12416 + 256 * p + 16 * r + i) =
      bf16Enc ((tileInputs P mem0 s h b).restoredKey r f) (i % 2) := by
  rw [stageByte_rows P mem0 s h b (a := 2) (base := 12416) (off := 8192) (p := p) (by omega)
      (by omega) (by omega) (by omega) hr hi,
    rows_byte T.restoredKey hr hf e]
  have ht : (tileInputs P mem0 s h b).restoredKey r f =
      (P.tile s h b).restoredKey ⟨r, hr⟩ ⟨f, hf⟩ := dite_eq_left ⟨hr, hf⟩
  rw [ht]

/-- A byte of `INV` in the stage: the payload of row `r` and column `f = 8 p + i / 2`. -/
private theorem inv_byte (T : P.TileStored mem0 (P.slot s h b) (P.tile s h b)) {p r i f : ℕ}
    (hr : r < 16) (hf : f < 16) (hi : i < 16) (e : f = 8 * p + i / 2) :
    stageByte P mem0 s h b (17024 + 256 * p + 16 * r + i) =
      bf16Enc ((tileInputs P mem0 s h b).inverse r f) (i % 2) := by
  rw [stageByte_squares P mem0 s h b (a := 0) (base := 17024) (off := 12800) (p := p)
      (by omega) (by omega) (by omega) (by omega) hr hi,
    squares_byte T.inverse hr hf e]
  have ht : (tileInputs P mem0 s h b).inverse r f =
      (P.tile s h b).inverse ⟨r, hr⟩ ⟨f, hf⟩ := dite_eq_left ⟨hr, hf⟩
  rw [ht]

/-- A byte of `Mqk` in the stage. -/
private theorem mqk_byte (T : P.TileStored mem0 (P.slot s h b) (P.tile s h b)) {p r i f : ℕ}
    (hr : r < 16) (hf : f < 16) (hi : i < 16) (e : f = 8 * p + i / 2) :
    stageByte P mem0 s h b (17536 + 256 * p + 16 * r + i) =
      bf16Enc ((tileInputs P mem0 s h b).score r f) (i % 2) := by
  rw [stageByte_squares P mem0 s h b (a := 1) (base := 17536) (off := 13312) (p := p)
      (by omega) (by omega) (by omega) (by omega) hr hi,
    squares_byte T.score hr hf e]
  have ht : (tileInputs P mem0 s h b).score r f =
      (P.tile s h b).score ⟨r, hr⟩ ⟨f, hf⟩ := dite_eq_left ⟨hr, hf⟩
  rw [ht]

/-- The value of row `t` and channel `ch` of the arrays of a tile. -/
private theorem ti_value (P : Params) (mem0 : Mem0) (s h b : ℕ) {t ch : ℕ} (hch : ch < 128) :
    (tileInputs P mem0 s h b).value t ch =
      if firstToken P.length s + 16 * b + t < P.total then
        bf16Num mem0 (P.valueLoc (firstToken P.length s + 16 * b + t) h ⟨ch, hch⟩)
      else 0 := by
  by_cases ht : firstToken P.length s + 16 * b + t < P.total
  · rw [ite_eq_left ht]
    exact dite_eq_left ⟨ht, hch⟩
  · rw [ite_eq_right ht]
    exact dite_eq_right fun hc => ht hc.1

/-- **The row of `v` a lane reads from the stage** (`VRow`): lane `l` of warp `w` reads, for the
value block `bi`, the sixteen bytes of row `l % 16` in the piece `2 bi + 4 w + l / 16`: eight
bit patterns of the token of that row, or eight payload zeros when the token is past the end of
the batch. -/
private theorem values_row (hpre : Pre P L mem0) (hh : h < P.heads) {w bi l : ℕ} (hw : w < 4)
    (hbi : bi < 2) (hl : l < 32) :
    VRow (tileInputs P mem0 s h b) w bi l ((List.range 16).map fun i =>
      stageByte P mem0 s h b (256 * (2 * bi + 4 * w + l / 16) + 16 * (l % 16) + i)) := by
  have hrow : rowOfLane l = l % 16 := by unfold rowOfLane; omega
  have hch : ∀ j < 8, halfBase w bi 0 + 8 * (l / 16) + j < 128 := by
    intro j hj
    rw [halfBase_zero]
    omega
  unfold VRow
  rw [hrow]
  by_cases hlt : firstToken P.length s + 16 * b + l % 16 < P.total
  · left
    have key : ∀ j : Fin 8, ∃ n : ℕ, n < 65536 ∧
        (∃ y : ℚ, FloatFmt.bf16.decode n = some y ∧ (y : ℝ) =
          (tileInputs P mem0 s h b).value (l % 16) (halfBase w bi 0 + 8 * (l / 16) + j)) ∧
        ∀ k < 2, mem0 ((P.valueLoc (firstToken P.length s + 16 * b + l % 16) h
          ⟨halfBase w bi 0 + 8 * (l / 16) + j, hch j j.isLt⟩).at k) =
            some (some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt k)) := by
      intro j
      obtain ⟨x, hx⟩ := value_bits hpre hh hlt ⟨_, hch j j.isLt⟩
      have hv := ti_value P mem0 s h b (t := l % 16) (hch j j.isLt)
      rw [ite_eq_left hlt, bf16Num_eq hx] at hv
      obtain ⟨n, hn, q, hq, hqx, hm⟩ := hx
      exact ⟨n, hn, ⟨q, hq, hqx.trans hv.symm⟩, hm⟩
    choose n hn hy hm using key
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ → ℕ, ∀ j (hj : j < 8), n' j = n ⟨j, hj⟩ :=
      ⟨fun j => if hj : j < 8 then n ⟨j, hj⟩ else 0, fun j hj => dite_eq_left hj⟩
    refine ⟨n', fun j hj => ?_, ?_⟩
    · rw [hn' j hj]
      exact ⟨hn ⟨j, hj⟩, hy ⟨j, hj⟩⟩
    · refine List.map_congr_left fun i hi => ?_
      have hi' := List.mem_range.mp hi
      rw [stageByte_values P mem0 s h b (by omega) (by omega) hi', ite_eq_left hlt,
        hn' (i / 2) (by omega)]
      have e : (⟨.global, 0, P.valuesBase +
          256 * ((firstToken P.length s + 16 * b + l % 16) * P.heads + h) +
          16 * (2 * bi + 4 * w + l / 16) + i⟩ : Loc) =
          (P.valueLoc (firstToken P.length s + 16 * b + l % 16) h
            ⟨halfBase w bi 0 + 8 * (l / 16) + (⟨i / 2, by omega⟩ : Fin 8), hch _ (by omega)⟩).at
              (i % 2) :=
        loc_congr (by simp only [Params.valueLoc, halfBase_zero]; omega)
      rw [e, hm ⟨i / 2, by omega⟩ (i % 2) (by omega)]
      rfl
  · right
    refine ⟨fun j hj => ?_, List.map_congr_left fun i hi => ?_⟩
    · rw [ti_value P mem0 s h b (hch j hj), ite_eq_right hlt]
    · rw [stageByte_values P mem0 s h b (by omega) (by omega) (List.mem_range.mp hi),
        ite_eq_right hlt]
      rfl

end rows

/-- The address form of a load of the input stage, by its source: the constant, the
coefficient of the stage and the weights of the bits of the thread index (the entries of
`Gen.loadForms`, as a function of the source). -/
private def stageForm : LoadSrc → Option (ℕ × ℕ × List ℕ)
  | .tilesA (.keyBlock .kd m) => some (36992 + 512 * m, 18048, [16, 32, 64, 128, 256, 0, 0])
  | .tilesA (.keyBlock .qd m) => some (41088 + 512 * m, 18048, [16, 32, 64, 128, 256, 0, 0])
  | .tilesA .inv => some (49792, 18048, [16, 32, 64, 128, 256, 0, 0])
  | .tilesA .mqk => some (50304, 18048, [16, 32, 64, 128, 256, 0, 0])
  | .restored m => some (45184 + 512 * m, 18048, [16, 32, 64, 256, 128, 0, 0])
  | .values bi => some (32768 + 512 * bi, 18048, [16, 32, 64, 128, 256, 1024, 2048])
  | _ => none

/-- The indices of a source of the input stage are in range: a key block below 8, a value block
below 2. -/
private def srcOk : LoadSrc → Bool
  | .tilesA (.keyBlock _ m) => decide (m < 8)
  | .tilesA .inv => true
  | .tilesA .mqk => true
  | .restored m => decide (m < 8)
  | .values bi => decide (bi < 2)
  | _ => false

/-- The source is `state_acc`. -/
private def srcState : LoadSrc → Bool
  | .state _ _ => true
  | _ => false

/-- The generated lists agree with `stageForm`: each of the 44 loads reads `state_acc`, or has
a source of the stage with indices in range and the address form of that source. -/
private theorem load_check : ∀ j : Fin 44, srcState (loadSrc j.val) = true ∨
    (srcOk (loadSrc j.val) = true ∧ Gen.loadForms[j.val]? = stageForm (loadSrc j.val) ∧
      (stageForm (loadSrc j.val)).isSome = true) := by
  decide

private theorem load_form (j : Fin 44) (hns : ∀ bi m, loadSrc j ≠ .state bi m) :
    ∃ c0 st ws, Gen.loadForms[j.val]? = some (c0, st, ws) ∧ srcOk (loadSrc j) = true ∧
      stageForm (loadSrc j) = some (c0, st, ws) := by
  rcases load_check j with hst | ⟨hok, hf, hsome⟩
  · exfalso
    cases hsrc : loadSrc j.val with
    | state bi m => exact hns bi m hsrc
    | _ => simp [hsrc, srcState] at hst
  · obtain ⟨⟨c0, st, ws⟩, hv⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨c0, st, ws, hf.trans hv, hok, hv⟩

/-- **The row of a source of the input stage.** For a source with the address form
`(c0, st, ws)`, the row address of lane `l` of warp `w` in tile `b` is at an offset `o` of the
tile's stage, its sixteen bytes are inside one part of the stage that the tensor loads write,
and the bytes the stage holds there are the row of the source for the arrays of the tile. -/
private theorem stage_row (hpre : Pre P L mem0) {s h b w l : ℕ} (hs : s < P.sequences)
    (hh : h < P.heads) (hb : b < tiles (P.length s)) (hw : w < 4) (hl : l < 32) {src : LoadSrc}
    (hok : srcOk src = true) {c0 st : ℕ} {ws : List ℕ} (hf : stageForm src = some (c0, st, ws)) :
    ∃ o, c0 + st * (b % 3) + bitsOff ws (32 * w + l) = 32768 + 18048 * (b % 3) + o ∧
      (o + 16 ≤ 4160 ∨ 4224 ≤ o ∧ o + 16 ≤ 18048) ∧
      src.RowOk (tileInputs P mem0 s h b) w l
        ((List.range 16).map fun i => stageByte P mem0 s h b (o + i)) := by
  have T := hpre.workspace s hs h hh b hb
  cases src with
  | state bi m => simp [stageForm] at hf
  | tilesA M =>
    cases M with
    | keyBlock a m =>
      have hm : m < 8 := by simpa [srcOk] using hok
      cases a with
      | kd =>
        simp only [stageForm, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        refine ⟨4224 + 256 * (2 * m + l / 16) + 16 * (l % 8 + 8 * (l / 8 % 2)), ?_,
          Or.inr (by omega), ?_⟩
        · rw [bitsOff_rows w hl]
          omega
        · show (List.range 16).map _ = (List.range 16).map _
          refine List.map_congr_left fun i hi => ?_
          have hi' := List.mem_range.mp hi
          exact kd_byte T (by omega) (by omega) hi' (by omega)
      | qd =>
        simp only [stageForm, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        refine ⟨8320 + 256 * (2 * m + l / 16) + 16 * (l % 8 + 8 * (l / 8 % 2)), ?_,
          Or.inr (by omega), ?_⟩
        · rw [bitsOff_rows w hl]
          omega
        · show (List.range 16).map _ = (List.range 16).map _
          refine List.map_congr_left fun i hi => ?_
          have hi' := List.mem_range.mp hi
          exact qd_byte T (by omega) (by omega) hi' (by omega)
    | inv =>
      simp only [stageForm, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      refine ⟨17024 + 256 * (l / 16) + 16 * (l % 8 + 8 * (l / 8 % 2)), ?_, Or.inr (by omega), ?_⟩
      · rw [bitsOff_rows w hl]
        omega
      · show (List.range 16).map _ = (List.range 16).map _
        refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.mp hi
        exact inv_byte T (by omega) (by omega) hi' (by omega)
    | mqk =>
      simp only [stageForm, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      refine ⟨17536 + 256 * (l / 16) + 16 * (l % 8 + 8 * (l / 8 % 2)), ?_, Or.inr (by omega), ?_⟩
      · rw [bitsOff_rows w hl]
        omega
      · show (List.range 16).map _ = (List.range 16).map _
        refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.mp hi
        exact mqk_byte T (by omega) (by omega) hi' (by omega)
    | _ => simp [stageForm] at hf
  | restored m =>
    have hm : m < 8 := by simpa [srcOk] using hok
    simp only [stageForm, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hf
    refine ⟨12416 + 256 * (2 * m + l / 8 % 2) + 16 * (8 * (l / 8 / 2) + l % 8), ?_,
      Or.inr (by omega), ?_⟩
    · rw [bitsOff_restored w hl]
      omega
    · show (List.range 16).map _ = (List.range 16).map _
      refine List.map_congr_left fun i hi => ?_
      have hi' := List.mem_range.mp hi
      exact rk_byte T (by omega) (by omega) hi' (by omega)
  | values bi =>
    have hbi : bi < 2 := by simpa [srcOk] using hok
    simp only [stageForm, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hf
    refine ⟨256 * (2 * bi + 4 * w + l / 16) + 16 * (l % 16), ?_, Or.inl (by omega), ?_⟩
    · rw [bitsOff_values hw hl]
      omega
    · exact values_row hpre hh hw hbi hl

/-- **The rows the loads of the input stage read, for the arrays of the launch**
(`tileInputs`): the statement of `RowsRead` for the compute warp `w` of block `c`, for every
`ldmatrix` whose source is not `state_acc`. The lane's read event returns the row of the
load's source for the arrays of its tile: a row of payloads of `k_decayed`, `q_decayed`,
`k_restored`, `INV` or `Mqk`, or a row of `v` (`VRow`: bit patterns, or payload zeros for a
token past the end of the batch). -/
theorem rows_read_stage (hpre : Pre P L mem0) (F : Followed L mem0 X) (R : ComputeRef P L X)
    (B : ReadBack P L mem0 X) (hT : TileBound P L X) {c w w0 : ℕ} (hc : c < L.grid)
    (hw : w < 4) (hw0 : w0 = c * L.block + 32 * w) :
    ∀ l < 32, ∀ k d e (j : Fin 44), (∀ bi m, loadSrc j ≠ .state bi m) →
      stateAt (code L) X (w0 + l) k = some (some d) → d.site = .matrixLoad j →
      X.get (w0 + l, k) = some e →
      ∃ pc a row, e = ⟨pc, .rd a row⟩ ∧
        (loadSrc j).RowOk (tileInputs P mem0 (c % P.sequences) (c / P.sequences)
          (ordinal X (w0 + l) k / 182)) w l row := by
  intro l hl k d e j hns hσ hs he
  obtain ⟨hdiv, hmod, hseq, hhead⟩ := lane_facts hpre hw hw0 hl
  have hg : w0 + l < L.threads := lt_of_get F.consistent he
  have hcomp : (w0 + l) % L.block < 128 := by omega
  have hsS : c % P.sequences < P.sequences := Nat.mod_lt _ hpre.sequencesPos
  have hhH : c / P.sequences < P.heads := Nat.div_lt_of_lt_mul (hpre.grid ▸ hc)
  have hb : ordinal X (w0 + l) k / 182 < tiles (P.length (c % P.sequences)) := by
    have := hT (w0 + l) k d hcomp hσ (Or.inl ⟨j, hs⟩)
    rwa [tileCount, hseq] at this
  obtain ⟨a, bs, rfl, hsz, hloc⟩ := R.loadRow (w0 + l) k d e j hcomp hσ hs he
  have hpol := R.polled (w0 + l) k d _ hcomp hσ he (Or.inl ⟨j, hs⟩)
  obtain ⟨c0, st, ws, hform, hok, hsf⟩ := load_form j hns
  obtain ⟨o, ho, hrange, hrow⟩ := stage_row hpre hsS hhH hb hw hl hok hsf
  have hoff : loadOff j (ordinal X (w0 + l) k / 182) (32 * w + l) =
      32768 + 18048 * (ordinal X (w0 + l) k / 182 % 3) + o := by
    unfold loadOff
    rw [hform]
    exact ho
  rw [hmod, hoff] at hloc
  have hbs := B.stage (w0 + l) k _ a bs _ o hg hcomp he hpol hloc (by rw [hsz]; exact hrange)
  rw [hsz, hseq, hhead] at hbs
  exact ⟨_, a, bs, rfl, hbs ▸ hrow⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Values

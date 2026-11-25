-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Source.Address

@[expose] public section

/-! # The bytes of a load through each tensor map of the kernel

`Data/TensorMaps.lean` builds the nine tensor maps the kernel loads through from six shapes:
`tokenMap` (the values `v`), `logitMap` (the gate logits `beta`), `tileRowsMap` (the workspace
arrays `k_decayed`, `q_decayed`, `k_restored`), `totalDecayMap` (`g_total`), `tileSquareMap`
(`INV`, `Mqk`) and `stateMap` (the initial state). For a copy (`copyOf`, `Address.lean`) through
each shape this file gives, with the numbers of the shape filled in:

* `box_*`: the slots of its box (columns, rows, bytes per element);
* `read_*`: the global byte slot `(x, y, k)` is read from, for the box at the coordinates
  `v0, v1, v2` (`originOf`), and the condition under which the element exists (otherwise the
  slot is filled);
* `write_*`: the shared byte slot `(x, y, k)` is written to. Only `stateMap` has a swizzle
  (32 bytes): `write_state` gives the address through the kernel's own swizzle `swzAbs`.

Each is the generic lemma of `Address.lean` at the shape; nothing depends on the launch.

| shape | element | box (columns, rows) | element `(c, r, p)` of the array is at |
|---|---|---|---|
| `tokenMap` | bf16 | 8, 16 | `base + 2 c + 256 H r + 256 p` (`r` token, `p` head) |
| `logitMap` | bf16 | 32, 1 | `base + 2 c` |
| `tileRowsMap` | bf16 | 8, 16 | `base + 2 c + 256 r + 4096 p` (`p` slot) |
| `totalDecayMap` | f32 | 128, 1 | `base + 4 c + 512 p` (`p` slot) |
| `tileSquareMap` | bf16 | 8, 16 | `base + 2 c + 32 r + 512 p` (`p` slot) |
| `stateMap` | f32 | 8, 128 | `base + 4 c + 512 r + 65536 p` (`p` plane) | -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX TensorDescriptor
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

variable {origin3 : Fin 3 → Int} {origin2 : Fin 2 → Int} {origin1 : Fin 1 → Int} {x y k : Nat}

/-! ### `tokenMap`: the values -/

/-- The box of a values load: 8 features, 16 token rows, 2 bytes per element. -/
theorem box_token (base tokens heads : Nat) (cls : AllocationClass) :
    TensorTile.count (tokenMap base tokens heads cls).box 0 = 8 ∧
      TensorTile.rows (tokenMap base tokens heads cls).box = 16 ∧
      (tokenMap base tokens heads cls).format.bytes = 2 :=
  ⟨count0 _, rows3 (fun _ => rfl) rfl, rfl⟩

/-- The source byte of slot `(x, y, k)` of a values load at feature `v0`, token `v1`, head
`v2`: byte `k` of that element, when the feature, the token and the head exist. -/
theorem read_token (base tokens heads : Nat) (cls : AllocationClass) (v0 v1 v2 : Nat) (sb mb : Loc)
    (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc
        (copyOf (tokenMap base tokens heads cls) (originOf [v0, v1, v2]) sb mb) x y k =
      if v0 + x < 128 ∧ v1 + y < tokens ∧ v2 < heads then
        some ⟨.global, 0, base + ((v0 + x) * 2 + (v1 + y) * (256 * heads) + v2 * 256) + k⟩
      else none :=
  readLoc3 (d := tokenMap base tokens heads cls) (fun _ => rfl) rfl (v0 := v0) (v1 := v1)
    (v2 := v2) rfl rfl rfl sb mb hx hy hk

/-- The destination of slot `(x, y, k)` of a values load: 16-byte rows, no swizzle. -/
theorem write_token (base tokens heads : Nat) (cls : AllocationClass) (sb mb : Loc)
    (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.writeLoc (copyOf (tokenMap base tokens heads cls) origin3 sb mb) x y k =
      some ⟨sb.space, sb.cta, sb.addr + (y * 16 + x * 2 + k)⟩ := by
  obtain ⟨h0, h1, h2⟩ := box_token base tokens heads cls
  exact writeLoc_plain (d := tokenMap base tokens heads cls) rfl origin3 sb mb (h0 ▸ hx)
    (h1 ▸ hy) hk

/-! ### `logitMap`: the gate logits -/

/-- The box of the logits load: 32 elements, one row, 2 bytes per element. -/
theorem box_logit (base count : Nat) (cls : AllocationClass) :
    TensorTile.count (logitMap base count cls).box 0 = 32 ∧
      TensorTile.rows (logitMap base count cls).box = 1 ∧
      (logitMap base count cls).format.bytes = 2 :=
  ⟨count0 _, rfl, rfl⟩

/-- The source byte of slot `(x, 0, k)` of the logits load at element `v0`: byte `k` of
element `v0 + x`, when it is below the element count. -/
theorem read_logit (base count : Nat) (cls : AllocationClass) (v0 : Nat) (sb mb : Loc)
    (hx : x < 32) (hk : k < 2) :
    TensorCopy.readLoc (copyOf (logitMap base count cls) (originOf [v0]) sb mb) x 0 k =
      if v0 + x < count then some ⟨.global, 0, base + (v0 + x) * 2 + k⟩ else none :=
  readLoc1 (d := logitMap base count cls) (v0 := v0) rfl sb mb hx hk

/-- The destination of slot `(x, 0, k)` of the logits load: consecutive elements. -/
theorem write_logit (base count : Nat) (cls : AllocationClass) (sb mb : Loc) (hx : x < 32)
    (hk : k < 2) :
    TensorCopy.writeLoc (copyOf (logitMap base count cls) origin1 sb mb) x 0 k =
      some ⟨sb.space, sb.cta, sb.addr + (x * 2 + k)⟩ := by
  obtain ⟨h0, h1, h2⟩ := box_logit base count cls
  rw [writeLoc_plain (d := logitMap base count cls) rfl origin1 sb mb (h0 ▸ hx)
    (by rw [h1]; exact Nat.one_pos) hk, Nat.zero_mul, Nat.zero_add]
  rfl

/-! ### `tileRowsMap`: the three workspace arrays of 16 rows by 128 features -/

/-- The box of a row-array load: 8 features, 16 rows, 2 bytes per element. -/
theorem box_rows (base slots : Nat) (cls : AllocationClass) :
    TensorTile.count (tileRowsMap base slots cls).box 0 = 8 ∧
      TensorTile.rows (tileRowsMap base slots cls).box = 16 ∧
      (tileRowsMap base slots cls).format.bytes = 2 :=
  ⟨count0 _, rows3 (fun _ => rfl) rfl, rfl⟩

/-- The source byte of slot `(x, y, k)` of a row-array load at feature `v0`, row `v1`, slot
`v2`. -/
theorem read_rows (base slots : Nat) (cls : AllocationClass) (v0 v1 v2 : Nat) (sb mb : Loc)
    (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc
        (copyOf (tileRowsMap base slots cls) (originOf [v0, v1, v2]) sb mb) x y k =
      if v0 + x < 128 ∧ v1 + y < 16 ∧ v2 < slots then
        some ⟨.global, 0, base + ((v0 + x) * 2 + (v1 + y) * 256 + v2 * 4096) + k⟩
      else none :=
  readLoc3 (d := tileRowsMap base slots cls) (fun _ => rfl) rfl (v0 := v0) (v1 := v1)
    (v2 := v2) rfl rfl rfl sb mb hx hy hk

/-- The destination of slot `(x, y, k)` of a row-array load: 16-byte rows, no swizzle. -/
theorem write_rows (base slots : Nat) (cls : AllocationClass) (sb mb : Loc) (hx : x < 8)
    (hy : y < 16) (hk : k < 2) :
    TensorCopy.writeLoc (copyOf (tileRowsMap base slots cls) origin3 sb mb) x y k =
      some ⟨sb.space, sb.cta, sb.addr + (y * 16 + x * 2 + k)⟩ := by
  obtain ⟨h0, h1, h2⟩ := box_rows base slots cls
  exact writeLoc_plain (d := tileRowsMap base slots cls) rfl origin3 sb mb (h0 ▸ hx) (h1 ▸ hy) hk

/-! ### `totalDecayMap`: `g_total` -/

/-- The box of the `g_total` load: 128 elements, one row, 4 bytes per element. -/
theorem box_total (base slots : Nat) (cls : AllocationClass) :
    TensorTile.count (totalDecayMap base slots cls).box 0 = 128 ∧
      TensorTile.rows (totalDecayMap base slots cls).box = 1 ∧
      (totalDecayMap base slots cls).format.bytes = 4 :=
  ⟨count0 _, rows2 (fun _ => rfl) rfl, rfl⟩

/-- The source byte of slot `(x, 0, k)` of the `g_total` load at feature `v0`, slot `v1`. -/
theorem read_total (base slots : Nat) (cls : AllocationClass) (v0 v1 : Nat) (sb mb : Loc)
    (hx : x < 128) (hk : k < 4) :
    TensorCopy.readLoc
        (copyOf (totalDecayMap base slots cls) (originOf [v0, v1]) sb mb) x 0 k =
      if v0 + x < 128 ∧ v1 < slots then
        some ⟨.global, 0, base + ((v0 + x) * 4 + v1 * 512) + k⟩
      else none :=
  readLoc2 (d := totalDecayMap base slots cls) (fun _ => rfl) rfl (v0 := v0) (v1 := v1) rfl rfl
    sb mb hx hk

/-- The destination of slot `(x, 0, k)` of the `g_total` load: consecutive elements. -/
theorem write_total (base slots : Nat) (cls : AllocationClass) (sb mb : Loc) (hx : x < 128)
    (hk : k < 4) :
    TensorCopy.writeLoc (copyOf (totalDecayMap base slots cls) origin2 sb mb) x 0 k =
      some ⟨sb.space, sb.cta, sb.addr + (x * 4 + k)⟩ := by
  obtain ⟨h0, h1, h2⟩ := box_total base slots cls
  rw [writeLoc_plain (d := totalDecayMap base slots cls) rfl origin2 sb mb (h0 ▸ hx)
    (by rw [h1]; exact Nat.one_pos) hk, Nat.zero_mul, Nat.zero_add]
  rfl

/-! ### `tileSquareMap`: the two workspace arrays of 16 rows by 16 columns -/

/-- The box of a square-array load: 8 columns, 16 rows, 2 bytes per element. -/
theorem box_square (base slots : Nat) (cls : AllocationClass) :
    TensorTile.count (tileSquareMap base slots cls).box 0 = 8 ∧
      TensorTile.rows (tileSquareMap base slots cls).box = 16 ∧
      (tileSquareMap base slots cls).format.bytes = 2 :=
  ⟨count0 _, rows3 (fun _ => rfl) rfl, rfl⟩

/-- The source byte of slot `(x, y, k)` of a square-array load at column `v0`, row `v1`,
slot `v2`. -/
theorem read_square (base slots : Nat) (cls : AllocationClass) (v0 v1 v2 : Nat) (sb mb : Loc)
    (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc
        (copyOf (tileSquareMap base slots cls) (originOf [v0, v1, v2]) sb mb) x y k =
      if v0 + x < 16 ∧ v1 + y < 16 ∧ v2 < slots then
        some ⟨.global, 0, base + ((v0 + x) * 2 + (v1 + y) * 32 + v2 * 512) + k⟩
      else none :=
  readLoc3 (d := tileSquareMap base slots cls) (fun _ => rfl) rfl (v0 := v0) (v1 := v1)
    (v2 := v2) rfl rfl rfl sb mb hx hy hk

/-- The destination of slot `(x, y, k)` of a square-array load: 16-byte rows, no swizzle. -/
theorem write_square (base slots : Nat) (cls : AllocationClass) (sb mb : Loc) (hx : x < 8)
    (hy : y < 16) (hk : k < 2) :
    TensorCopy.writeLoc (copyOf (tileSquareMap base slots cls) origin3 sb mb) x y k =
      some ⟨sb.space, sb.cta, sb.addr + (y * 16 + x * 2 + k)⟩ := by
  obtain ⟨h0, h1, h2⟩ := box_square base slots cls
  exact writeLoc_plain (d := tileSquareMap base slots cls) rfl origin3 sb mb (h0 ▸ hx)
    (h1 ▸ hy) hk

/-! ### `stateMap`: the initial state -/

/-- The box of a state load: 8 key columns, 128 value rows, 4 bytes per element. -/
theorem box_state (base planes : Nat) (cls : AllocationClass) :
    TensorTile.count (stateMap base planes cls).box 0 = 8 ∧
      TensorTile.rows (stateMap base planes cls).box = 128 ∧
      (stateMap base planes cls).format.bytes = 4 :=
  ⟨count0 _, rows3 (fun _ => rfl) rfl, rfl⟩

/-- The source byte of slot `(x, y, k)` of a state load at key column `v0`, value row `v1`,
plane `v2`. -/
theorem read_state (base planes : Nat) (cls : AllocationClass) (v0 v1 v2 : Nat) (sb mb : Loc)
    (hx : x < 8) (hy : y < 128) (hk : k < 4) :
    TensorCopy.readLoc
        (copyOf (stateMap base planes cls) (originOf [v0, v1, v2]) sb mb) x y k =
      if v0 + x < 128 ∧ v1 + y < 128 ∧ v2 < planes then
        some ⟨.global, 0, base + ((v0 + x) * 4 + (v1 + y) * 512 + v2 * 65536) + k⟩
      else none :=
  readLoc3 (d := stateMap base planes cls) (fun _ => rfl) rfl (v0 := v0) (v1 := v1)
    (v2 := v2) rfl rfl rfl sb mb hx hy hk

/-- The destination of a state load, for a destination that is a multiple of 128: the kernel's
swizzle of the address without swizzle. -/
theorem write_state (base planes : Nat) (cls : AllocationClass) {sb : Loc} (mb : Loc)
    (hb : sb.addr % 128 = 0) (hx : x < 8) (hy : y < 128) (hk : k < 4) :
    TensorCopy.writeLoc (copyOf (stateMap base planes cls) origin3 sb mb) x y k =
      some ⟨sb.space, sb.cta, swzAbs (sb.addr + (y * 32 + x * 4 + k))⟩ := by
  obtain ⟨h0, h1, h2⟩ := box_state base planes cls
  exact writeLoc_b32 (d := stateMap base planes cls) rfl rfl origin3 mb hb (h0 ▸ hx) (h1 ▸ hy) hk

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Decoded

@[expose] public section

/-!
# `SparseAttnDecodeParams` bytes and the `ld.param` reads of the frozen program

The by-value parameter object `param_0` of the FlashMLA SM100 sparse decode head64 kernel
(`v41_h64_no_split`) is the `SparseAttnDecodeParams` of `csrc/params.h` (line 118, FlashMLA
commit 395cb3af), a 304-byte struct. This file fixes the field offsets of that struct, the
encoders for the little-endian bytes of a field, and the table `param0Reads` of the `ld.param`
reads the kernel performs on the object. The table is proved against the decoded program here;
`Audit/ParamReads.lean` adds the object-level facts that make those reads reads of `param_0`.

The offsets follow the default C++ ABI of the struct: `int`, `float` and the `ModelType` enums
occupy 4 bytes, pointers 8, `bool` 1, and the struct is 8-byte aligned with size 304, which is
exactly the size the PTX declares for `param_0[304]`. No field occupies the padding bytes 52-55,
124-127, 220-223, 233-239, 276-279 and 300-303. The second parameter object, `param_1`, is not
described by `params.h`: it is the 1024-byte `TmaParams` tensor-map object (`param1Bytes`).

The `float` fields are encoded by their binary32 pattern; the number such a pattern denotes is
`f32Value` of that pattern (`Core.Float.Format`), not its decimal spelling.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX

/-! ## Field offsets of `SparseAttnDecodeParams` -/

/-- Offset of `b` (`int`, params.h:119). -/
def bOff : Nat := 0
/-- Offset of `s_q` (`int`, params.h:120). -/
def sQOff : Nat := 4
/-- Offset of `h_q` (`int`, params.h:121). -/
def hQOff : Nat := 8
/-- Offset of `h_kv` (`int`, params.h:121). -/
def hKvOff : Nat := 12
/-- Offset of `d_qk` (`int`, params.h:122). -/
def dQkOff : Nat := 16
/-- Offset of `d_v` (`int`, params.h:122). -/
def dVOff : Nat := 20
/-- Offset of `sm_scale` (`float`, params.h:123). -/
def smScaleOff : Nat := 24
/-- Offset of `sm_scale_div_log2` (`float`, params.h:124). -/
def smScaleDivLog2Off : Nat := 28
/-- Offset of `num_blocks` (`int`, params.h:125). -/
def numBlocksOff : Nat := 32
/-- Offset of `page_block_size` (`int`, params.h:126). -/
def pageBlockSizeOff : Nat := 36
/-- Offset of `topk` (`int`, params.h:127). -/
def topkOff : Nat := 40
/-- Offset of `model_type` (`ModelType`, params.h:128). -/
def modelTypeOff : Nat := 44
/-- Offset of `extra_model_type` (`ModelType`, params.h:129). -/
def extraModelTypeOff : Nat := 48
/-- Offset of `q` (`bf16*`, params.h:132). -/
def qOff : Nat := 56
/-- Offset of `kv` (`bf16*`, params.h:133). -/
def kvOff : Nat := 64
/-- Offset of `indices` (`int*`, params.h:134). -/
def indicesOff : Nat := 72
/-- Offset of `topk_length` (`int*`, params.h:135). -/
def topkLengthOff : Nat := 80
/-- Offset of `attn_sink` (`float*`, params.h:136). -/
def attnSinkOff : Nat := 88
/-- Offset of `lse` (`float*`, params.h:139). -/
def lseOff : Nat := 96
/-- Offset of `out` (`bf16*`, params.h:140). -/
def outOff : Nat := 104
/-- Offset of `extra_num_blocks` (`int`, params.h:143). -/
def extraNumBlocksOff : Nat := 112
/-- Offset of `extra_page_block_size` (`int`, params.h:143). -/
def extraPageBlockSizeOff : Nat := 116
/-- Offset of `extra_topk` (`int`, params.h:143). -/
def extraTopkOff : Nat := 120
/-- Offset of `extra_kv` (`bf16*`, params.h:144). -/
def extraKvOff : Nat := 128
/-- Offset of `extra_indices` (`int*`, params.h:145). -/
def extraIndicesOff : Nat := 136
/-- Offset of `extra_topk_length` (`int*`, params.h:146). -/
def extraTopkLengthOff : Nat := 144
/-- Offset of `stride_q_b` (`int`, params.h:149). -/
def strideQBOff : Nat := 152
/-- Offset of `stride_q_s_q` (`int`, params.h:149). -/
def strideQSQOff : Nat := 156
/-- Offset of `stride_q_h_q` (`int`, params.h:149). -/
def strideQHQOff : Nat := 160
/-- Offset of `stride_kv_block` (`int`, params.h:150). -/
def strideKvBlockOff : Nat := 164
/-- Offset of `stride_kv_row` (`int`, params.h:150). -/
def strideKvRowOff : Nat := 168
/-- Offset of `stride_indices_b` (`int`, params.h:151). -/
def strideIndicesBOff : Nat := 172
/-- Offset of `stride_indices_s_q` (`int`, params.h:151). -/
def strideIndicesSQOff : Nat := 176
/-- Offset of `stride_lse_b` (`int`, params.h:152). -/
def strideLseBOff : Nat := 180
/-- Offset of `stride_lse_s_q` (`int`, params.h:152). -/
def strideLseSQOff : Nat := 184
/-- Offset of `stride_o_b` (`int`, params.h:153). -/
def strideOBOff : Nat := 188
/-- Offset of `stride_o_s_q` (`int`, params.h:153). -/
def strideOSQOff : Nat := 192
/-- Offset of `stride_o_h_q` (`int`, params.h:153). -/
def strideOHQOff : Nat := 196
/-- Offset of `stride_extra_kv_block` (`int`, params.h:154). -/
def strideExtraKvBlockOff : Nat := 200
/-- Offset of `stride_extra_kv_row` (`int`, params.h:154). -/
def strideExtraKvRowOff : Nat := 204
/-- Offset of `stride_extra_indices_b` (`int`, params.h:155). -/
def strideExtraIndicesBOff : Nat := 208
/-- Offset of `stride_extra_indices_s_q` (`int`, params.h:155). -/
def strideExtraIndicesSQOff : Nat := 212
/-- Offset of `num_sm` (`int`, params.h:157). -/
def numSmOff : Nat := 216
/-- Offset of `stream` (`stream_t`, a pointer; params.h:158). -/
def streamOff : Nat := 224
/-- Offset of `enable_split_kv` (`bool`, params.h:161). -/
def enableSplitKvOff : Nat := 232
/-- Offset of `lse_accum` (`float*`, params.h:162). -/
def lseAccumOff : Nat := 240
/-- Offset of `o_accum` (`float*`, params.h:163). -/
def oAccumOff : Nat := 248
/-- Offset of `stride_lse_accum_split` (`int`, params.h:164). -/
def strideLseAccumSplitOff : Nat := 256
/-- Offset of `stride_lse_accum_s_q` (`int`, params.h:164). -/
def strideLseAccumSQOff : Nat := 260
/-- Offset of `stride_o_accum_split` (`int`, params.h:165). -/
def strideOAccumSplitOff : Nat := 264
/-- Offset of `stride_o_accum_s_q` (`int`, params.h:165). -/
def strideOAccumSQOff : Nat := 268
/-- Offset of `stride_o_accum_h_q` (`int`, params.h:165). -/
def strideOAccumHQOff : Nat := 272
/-- Offset of `tile_scheduler_metadata_ptr` (`DecodingSchedMeta*`, params.h:166). -/
def tileSchedulerMetadataPtrOff : Nat := 280
/-- Offset of `num_splits_ptr` (`int*`, params.h:167). -/
def numSplitsPtrOff : Nat := 288
/-- Offset of `num_sm_parts` (`int`, params.h:168). -/
def numSmPartsOff : Nat := 296

/-- Bytes of the `param_0` object: `sizeof(SparseAttnDecodeParams)`, which the PTX declares as
`param_0[304]`. -/
def param0Bytes : Nat := 304

/-- Bytes of the `param_1` object: the eight 128-byte tensor descriptors of `TmaParams`, which
the PTX declares as `param_1[1024]`. -/
def param1Bytes : Nat := 1024

/-! ## Little-endian field encoders -/

/-- Byte `k` (little-endian) of the number `x`: byte 0 is the low byte. -/
def leByte (x k : Nat) : BitVec 8 := BitVec.ofNat 8 (x / 256 ^ k)

/-- Byte `k < 4` of an `int` field: its value as a little-endian 32-bit word. -/
def leInt32 (x k : Nat) : BitVec 8 := leByte x k

/-- Byte `k < 4` of a `float` field: the little-endian bytes of its binary32 pattern. The number
they encode is `f32Value` of the pattern, `none` for a NaN pattern. -/
def leF32 (bits k : Nat) : BitVec 8 := leByte bits k

/-- Byte `k < 8` of a pointer field: the pointer value as a little-endian 64-bit word. -/
def lePtr (a k : Nat) : BitVec 8 := leByte a k

/-! ## The `ld.param` reads of the frozen program -/

/-- One memory access of the decoded program into the parameter space: its position, access
kind, address base, byte offset and width in bytes. -/
structure ParamAccess where
  pc : Nat
  kind : MemKind
  base : AddrBase
  /-- The byte offset in the parameter object. -/
  off : Int
  /-- The number of bytes the access moves. -/
  width : Nat
  deriving DecidableEq, Repr

/-- The number of bytes one memory access moves: its element width times its vector count. -/
def accessBytes (a : MemAccess) : Nat := a.elem.width * a.vec / 8

/-- The register that holds the address of `param_0` (`%rd2` in the PTX), loaded by the
`mov.b64` at pc 0. -/
def param0AddrReg : Nat := 2991

/-- The register that holds the address of `param_1` (`%rd1` in the PTX). -/
def param1AddrReg : Nat := 2990

/-- The name of the first declared parameter object, `param_0`. -/
def param0Name : String := (Decoded.metadata.paramObjects.headD ⟨"", 0, 0, 0⟩).name

/-- The name of the second declared parameter object, `param_1`. -/
def param1Name : String := ((Decoded.metadata.paramObjects.drop 1).headD ⟨"", 0, 0, 0⟩).name

/-- The move instruction of `ins`, when the instruction is a move. -/
def moveOf (ins : Instr) : Option MoveInstr :=
  match ins.op with
  | .move m => some m
  | _ => none

/-- Every memory access of `code` into the parameter space, in program order. -/
def paramAccesses (code : List Instr) : List ParamAccess :=
  code.zipIdx.filterMap fun (ins, pc) =>
    match ins.op with
    | .mem a =>
      if a.space == some .param then
        some ⟨pc, a.kind, a.addr.base, a.addr.off, accessBytes a⟩
      else none
    | _ => none

/-- The parameter-space accesses of the frozen program: 44 `ld.param` reads, every one of them
through the `param_0` address register `%rd2` (register 2991). -/
theorem paramAccesses_eq :
    paramAccesses Decoded.kernel.code =
      [⟨146, .load, .reg 2991 64, 28, 4⟩, ⟨147, .load, .reg 2991 64, 88, 8⟩,
      ⟨151, .load, .reg 2991 64, 8, 4⟩, ⟨158, .load, .reg 2991 64, 0, 4⟩,
      ⟨163, .load, .reg 2991 64, 80, 8⟩, ⟨170, .load, .reg 2991 64, 40, 4⟩,
      ⟨176, .load, .reg 2991 64, 144, 8⟩, ⟨183, .load, .reg 2991 64, 120, 4⟩,
      ⟨1159, .load, .reg 2991 64, 8, 4⟩, ⟨1167, .load, .reg 2991 64, 96, 8⟩,
      ⟨1169, .load, .reg 2991 64, 180, 4⟩, ⟨1171, .load, .reg 2991 64, 184, 4⟩,
      ⟨1858, .load, .reg 2991 64, 0, 4⟩, ⟨1861, .load, .reg 2991 64, 80, 8⟩,
      ⟨1862, .load, .reg 2991 64, 40, 4⟩, ⟨1863, .load, .reg 2991 64, 144, 8⟩,
      ⟨1864, .load, .reg 2991 64, 120, 4⟩, ⟨2170, .load, .reg 2991 64, 0, 4⟩,
      ⟨2173, .load, .reg 2991 64, 80, 8⟩, ⟨2174, .load, .reg 2991 64, 40, 4⟩,
      ⟨2175, .load, .reg 2991 64, 144, 8⟩, ⟨2176, .load, .reg 2991 64, 120, 4⟩,
      ⟨2332, .load, .reg 2991 64, 0, 4⟩, ⟨2335, .load, .reg 2991 64, 164, 4⟩,
      ⟨2336, .load, .reg 2991 64, 200, 4⟩, ⟨2337, .load, .reg 2991 64, 80, 8⟩,
      ⟨2338, .load, .reg 2991 64, 40, 4⟩, ⟨2339, .load, .reg 2991 64, 144, 8⟩,
      ⟨2340, .load, .reg 2991 64, 120, 4⟩, ⟨2341, .load, .reg 2991 64, 72, 8⟩,
      ⟨2342, .load, .reg 2991 64, 172, 4⟩, ⟨2343, .load, .reg 2991 64, 176, 4⟩,
      ⟨2345, .load, .reg 2991 64, 136, 8⟩, ⟨2346, .load, .reg 2991 64, 208, 8⟩,
      ⟨2349, .load, .reg 2991 64, 36, 4⟩, ⟨2355, .load, .reg 2991 64, 116, 4⟩,
      ⟨2587, .load, .reg 2991 64, 0, 4⟩, ⟨2590, .load, .reg 2991 64, 80, 8⟩,
      ⟨2591, .load, .reg 2991 64, 144, 8⟩, ⟨2609, .load, .reg 2991 64, 0, 4⟩,
      ⟨2612, .load, .reg 2991 64, 80, 8⟩, ⟨2613, .load, .reg 2991 64, 40, 4⟩,
      ⟨2614, .load, .reg 2991 64, 144, 8⟩, ⟨2615, .load, .reg 2991 64, 120, 4⟩] := by
  decide +kernel

/-- The `ld.param` reads of the frozen program: byte offset, width in bytes, and the
`SparseAttnDecodeParams` field read (the `ld.param.v2.b32` at offset 208 reads the two
`stride_extra_indices` words in one access). -/
def param0Reads : List (Nat × Nat × String) :=
  [(0, 4, "b"), (8, 4, "h_q"), (28, 4, "sm_scale_div_log2"), (36, 4, "page_block_size"),
    (40, 4, "topk"), (72, 8, "indices"), (80, 8, "topk_length"), (88, 8, "attn_sink"),
    (96, 8, "lse"), (116, 4, "extra_page_block_size"), (120, 4, "extra_topk"),
    (136, 8, "extra_indices"), (144, 8, "extra_topk_length"), (164, 4, "stride_kv_block"),
    (172, 4, "stride_indices_b"), (176, 4, "stride_indices_s_q"), (180, 4, "stride_lse_b"),
    (184, 4, "stride_lse_s_q"), (200, 4, "stride_extra_kv_block"),
    (208, 8, "stride_extra_indices_b, stride_extra_indices_s_q")]

/-- Every read of the program is listed in `param0Reads`: the table has no missing
`(offset, width)` pair. -/
theorem param0Reads_complete :
    ((paramAccesses Decoded.kernel.code).map (fun a => (a.off.toNat, a.width))).all
        (fun p => (param0Reads.map fun r => (r.1, r.2.1)).contains p) = true := by
  rw [paramAccesses_eq]
  decide

/-- Every entry of `param0Reads` is a read of the program: the table lists no pair the kernel
does not perform. -/
theorem param0Reads_sound :
    (param0Reads.map (fun r => (r.1, r.2.1))).all
        (fun p =>
          ((paramAccesses Decoded.kernel.code).map fun a => (a.off.toNat, a.width)).contains p) =
      true := by
  rw [paramAccesses_eq]
  decide

/-- Every read lies inside the 304-byte object: it covers bytes `offset` to
`offset + width - 1`. -/
theorem param0Reads_bounds :
    param0Reads.all (fun r => r.1 + r.2.1 ≤ param0Bytes) = true := by
  decide

/-- Every parameter-space access of the program is a load: the kernel performs no store, atomic,
reduction or uniform load in the parameter space. -/
theorem paramAccesses_loads :
    (paramAccesses Decoded.kernel.code).map (fun a => a.kind) = List.replicate 44 .load := by
  rw [paramAccesses_eq]
  decide

/-- Every parameter-space access of the program uses `param_0`'s address register. This also
excludes a direct parameter-object base: `AddrBase.param` would not be `.reg param0AddrReg 64`. -/
theorem paramAccesses_base :
    (paramAccesses Decoded.kernel.code).map (fun a => a.base) =
      List.replicate 44 (.reg param0AddrReg 64) := by
  rw [paramAccesses_eq]
  decide

/-- No parameter-space access of the program, and so no `ld.param`, reads through `param_1`'s
address register. -/
theorem param1_notRead :
    (paramAccesses Decoded.kernel.code).all
        (fun a => a.base != .reg param1AddrReg 64) = true := by
  rw [paramAccesses_eq]
  decide

end PTX.Kernels.FlashMlaSparseDecodeH64

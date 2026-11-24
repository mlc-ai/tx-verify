-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode

/-! `tcgen05.ld .pack::16b` and `tcgen05.st .unpack::16b` (THREAD-TC-PACK16, EXT-TMEM-LANE-FIELD):
decoding, the cells of the packed fragments, the registers a packed load returns and the slot
values an unpacking store records, and the rejected forms. -/
namespace PTX.Tests.TcPack16
noncomputable section

private def env : Decode.Env := { classes := [⟨"r".toList, 8, 32⟩], labels := [], params := [] }

private def unmodeled : Except String Op → Bool
  | .ok (.unmodeled _) => true
  | _ => false

/-! ## Decoding -/

example : Decode.op env "tcgen05.ld.sync.aligned.32x32b.x2.pack::16b.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"]] =
    .ok (.tcLd [1, 2] 0 (.packed16 .s32x32b)) := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.16x128b.x1.pack::16b.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"]] =
    .ok (.tcLd [1, 2] 0 (.packed16 .s16x128b)) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x64b.x1.unpack::16b.b32"
    [.address [.register "r0"], .vector [.register "r1"]] =
    .ok (.tcSt 0 [.reg 1] (.packed16 .s16x64b)) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x256b.x1.unpack::16b.b32"
    [.address [.register "r0"],
      .vector [.register "r1", .register "r2", .register "r3", .register "r4"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2, .reg 3, .reg 4] (.packed16 .s16x256b)) := rfl
-- `.16x32bx2` with packing decodes without a representation.
example : unmodeled (Decode.op env "tcgen05.ld.sync.aligned.16x32bx2.x1.pack::16b.b32"
    [.vector [.register "r1"], .address [.register "r0"], .literal "8"]) = true := rfl
example : unmodeled (Decode.op env "tcgen05.st.sync.aligned.16x32bx2.x1.unpack::16b.b32"
    [.address [.register "r0"], .literal "8", .vector [.register "r1"]]) = true := rfl
-- Rejected: a vector length that is not `.num` repetitions of the shape.
example : (Decode.op env "tcgen05.ld.sync.aligned.16x128b.x1.pack::16b.b32"
    [.vector [.register "r1"], .address [.register "r0"]]).toOption = none := rfl
-- The packed forms have THREAD-TC.
example : (Op.tcLd [1] 0 (.packed16 .s32x32b)).rule = some .threadTc := rfl
example : (Op.tcSt 0 [.reg 1] (.packed16 .s32x32b)).rule = some .threadTc := rfl

/-! ## Cells -/

-- A launch of one CTA of 128 threads.
private def L : Launch := { grid := 1, block := 128, params := fun _ => none }

-- `.32x32b`: register `j` of thread lane 5 is columns `c + 2 j` and `c + 2 j + 1` of lane 5.
example : tcDataCell L 5 (.packed16 .s32x32b) 16 0 = ⟨0, 5, 16⟩ := rfl
example : tcDataCell L 5 (.packed16 .s32x32b) 16 1 = ⟨0, 5, 17⟩ := rfl
example : tcDataCell L 5 (.packed16 .s32x32b) 16 2 = ⟨0, 5, 18⟩ := rfl
example : tcDataCell L 5 (.packed16 .s32x32b) 16 3 = ⟨0, 5, 19⟩ := rfl
-- `.16x128b`: thread lane 6 (unpacked register 0 at lane 1, column 2) uses columns 4 and 5.
example : tcDataCell L 6 .s16x128b 0 0 = ⟨0, 1, 2⟩ := rfl
example : tcDataCell L 6 (.packed16 .s16x128b) 0 0 = ⟨0, 1, 4⟩ := rfl
example : tcDataCell L 6 (.packed16 .s16x128b) 0 1 = ⟨0, 1, 5⟩ := rfl
-- Its register 1 (unpacked lane 9, column 2) uses columns 4 and 5 of lane 9.
example : tcDataCell L 6 (.packed16 .s16x128b) 0 2 = ⟨0, 9, 4⟩ := rfl
-- Warp 1 uses its own chunk.
example : tcDataCell L 37 (.packed16 .s32x32b) (32 * 2 ^ 16 + 8) 1 = ⟨0, 37, 9⟩ := rfl
-- The packed shape of a single-access shape is accepted; of `.16x32bx2` or nested, not.
example : tcDataAddressOk L 0 (.packed16 .s16x256b) 0 = true := rfl
example : tcDataAddressOk L 0 (.packed16 (.s16x32bx2 4)) 0 = false := rfl
example : tcDataAddressOk L 0 (.packed16 (.packed16 .s32x32b)) 0 = false := rfl
-- The register count is that of the unpacked shape (Table 59).
example : (TcShape.packed16 .s16x256b).countOk 8 = true := rfl
example : (TcShape.packed16 .s16x256b).countOk 2 = false := rfl

/-! ## Values -/

private def w (n : Nat) : Value := .bits 32 (BitVec.ofNat 64 n)
private def h (n : Nat) : Value := .bits 16 (BitVec.ofNat 64 n)

-- A packed load: register 0 is the low halves of slots 0 and 1, register 1 those of 2 and 3.
example : TcPack16.pack [w 0xAAAA1111, w 0xBBBB2222, w 3, w 4] =
    [.pair (.slice (w 0xAAAA1111) 0 2) (.slice (w 0xBBBB2222) 0 2),
      .pair (.slice (w 3) 0 2) (.slice (w 4) 0 2)] := rfl
-- The halves keep the low two bytes of each word.
example : (((TcPack16.pack [w 0xAAAA1111, w 0xBBBB2222]).headD (w 0)).byteAt 1) =
    (w 0xAAAA1111).byteAt 1 := rfl
example : (((TcPack16.pack [w 0xAAAA1111, w 0xBBBB2222]).headD (w 0)).byteAt 2) =
    (w 0xBBBB2222).byteAt 0 := rfl
-- A 2-byte word (an unpacked FP16 value) is kept as it is.
example : TcPack16.pack [h 7, h 9] = [.pair (h 7) (h 9)] := rfl
-- An unpacking store: slot `2 j` holds bytes 0 and 1 of register `j`, slot `2 j + 1` bytes 2, 3.
example : TcPack16.unpack [w 0xBBBB2222] = [.slice (w 0xBBBB2222) 0 2, .slice (w 0xBBBB2222) 2 2] :=
  rfl
example : ((TcPack16.unpack [w 0xBBBB2222]).getD 1 (w 0)).byteAt 0 = (w 0xBBBB2222).byteAt 2 :=
  rfl
-- A stored slot value is two bytes wide, so it fixes only the low two bytes of its word.
example : ((TcPack16.unpack [w 1]).map Value.bytes) = [2, 2] := rfl
-- Unpack then pack returns the register's bytes.
example : ((TcPack16.pack (TcPack16.unpack [w 0x12345678])).headD (w 0)).toBytes =
    (w 0x12345678).toBytes := rfl

/-! ## Per-form lemmas -/

example {L : Launch} {g : Nat} {t : TState} {ds : List Nat} {ta : Nat} :
    tcTmpl L g t (.tcLd ds ta .s32x32b none) = ofExec (do
      unless L.block % 32 = 0 do throw .noRule
      unless TcShape.s32x32b.countOk ds.length do throw .noRule
      let a ← readBits L g t 32 (.reg ta)
      unless tcDataAddressOk L g .s32x32b a.toNat do throw .noRule
      pure (.tcLd a.toNat ds.length .s32x32b fun vals => setRegs (next t) ds vals)) :=
  tcTmpl_tcLd_none (by intro s h; cases h)

end
end PTX.Tests.TcPack16

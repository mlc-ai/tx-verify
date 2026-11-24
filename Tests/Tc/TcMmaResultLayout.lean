-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Lemmas.Tcgen05.TcMmaResultLayout

namespace PTX.Tests.TcMmaResultLayout
open TcMma

private def smem : TcShared.Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩
private def layoutA : OperandSpec :=
  ⟨⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩, smem, smem, 6, 7, none,
    {}⟩
private def layoutB : OperandSpec :=
  { layoutA with descriptor := { layoutA.descriptor with m := 128 } }

example : resultCell layoutA 64 0 0 = some ⟨6, 0, 64⟩ := rfl
example : resultCell layoutA 64 127 255 = some ⟨6, 127, 319⟩ := rfl
example : resultCell layoutA 64 128 0 = some ⟨7, 0, 64⟩ := rfl
example : resultCell layoutA 64 255 255 = some ⟨7, 127, 319⟩ := rfl
-- For M=128, the right half of N occupies upper datapath lanes, not extra columns.
example : resultCell layoutB 64 0 127 = some ⟨6, 0, 191⟩ := rfl
example : resultCell layoutB 64 0 128 = some ⟨6, 64, 64⟩ := rfl
example : resultCell layoutB 64 63 255 = some ⟨6, 127, 191⟩ := rfl
example : resultCell layoutB 64 64 0 = some ⟨7, 0, 64⟩ := rfl
example : resultCell layoutB 64 127 255 = some ⟨7, 127, 191⟩ := rfl
-- FP16 D occupies one word per value too, rather than doubling elements per column.
example : resultCell { layoutA with descriptor := { layoutA.descriptor with kind :=
                                                                            .f16 .f16 .f16 } }
    64 0 1 = some ⟨6, 0, 65⟩ := rfl

example : resultCell layoutA 256 255 255 = some ⟨7, 127, 511⟩ := rfl
example : resultCell layoutA 257 0 0 = none := rfl
example : resultCell layoutB 384 127 255 = some ⟨7, 127, 511⟩ := rfl
example : resultCell layoutB 385 0 0 = none := rfl
example : resultCell layoutA 65536 0 0 = none := rfl
example : resultCell layoutA 0 256 0 = none := rfl
example : resultCell layoutB 0 0 256 = none := rfl

-- Group-2 masks number the even CTA's 128 lanes before the odd CTA's 128 lanes.
example : writeCell layoutA 64 [0,0,0,0,1,0,0,0] 128 0 = none := rfl
example : writeCell layoutA 64 [0,0,0,0,1,0,0,0] 0 0 = some ⟨6,0,64⟩ := rfl
-- Mask word 2 disables an upper-half lane in the even CTA's Layout B.
example : writeCell layoutB 64 [0,0,1,0,0,0,0,0] 0 128 = none := rfl
example : writeCell layoutB 64 [0,0,1,0,0,0,0,0] 64 0 = some ⟨7,0,64⟩ := rfl
example : writeCell layoutA 0 [0,0,0,0] 0 0 = none := rfl

-- cta_group::1, M = 128 (Layout D): every row is a lane of the issuer's CTA, every
-- column of N is a column; four mask words cover its 128 lanes.
private def layoutD : OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, smem, smem, 5, 5, none,
    {}⟩
example : resultColumns layoutD.descriptor = 8 := rfl
example : resultCell layoutD 64 0 0 = some ⟨5, 0, 64⟩ := rfl
example : resultCell layoutD 64 127 7 = some ⟨5, 127, 71⟩ := rfl
example : resultCell layoutD 64 128 0 = none := rfl
example : resultCell layoutD 64 0 8 = none := rfl
example : resultCell layoutD 505 0 0 = none := rfl
example : writeCell layoutD 64 [0,0,0,0] 127 7 = some ⟨5, 127, 71⟩ := rfl
example : writeCell layoutD 64 [0,0,0,2] 97 0 = none := rfl
example : writeCell layoutD 64 [0,0,0,2] 96 0 = some ⟨5, 96, 64⟩ := rfl
example : writeCell layoutD 64 [0,0,0,0,0,0,0,0] 0 0 = none := rfl
-- A group-1 f16 MMA with M = 128 uses the same Layout D.
example : resultCell { layoutD with descriptor := ⟨.one, .f16 .f16 .f32, 128, 8, false,
    false, false, false, false⟩ } 0 3 5 = some ⟨5, 3, 5⟩ := rfl

-- The execution query uses the instruction's actual masks and parameters.
noncomputable section
private def X : Execution where
  tr := fun _ => [⟨0, .tc (.mma 64 layoutB true [0,0,1,0,0,0,0,0])⟩]
  rf := fun _ _ => none
example : X.MmaCell (0, 0) ⟨7,0,64⟩ :=
  ⟨64, layoutB, true, [0,0,1,0,0,0,0,0], 64, 0, ⟨0, rfl⟩, rfl⟩
end

end PTX.Tests.TcMmaResultLayout

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcSharedDescriptor

namespace PTX.Tests.TcSharedDescriptor
open TcShared

private def prod : Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩

-- Actual fixed bits in the production descriptor; source addresses are added later.
example : decode 4611756662049472512 = some prod := rfl
example : decode (4611756662049472512 + 64) = some { prod with start := 1024 } := rfl
example : decode (4611756662049472512 + 8256) = some { prod with start := 132096 } := rfl
example : decode (4611756662049472512 + 66) = some { prod with start := 1056 } := rfl
example : decode (4611756662049472512 + 2112) = some { prod with start := 33792 } := rfl

-- Decode each independent field; base offset is not required to be zero.
example : decode (2 ^ 46 + 3 + 5 * 2 ^ 16 + 7 * 2 ^ 32 + 6 * 2 ^ 49) =
    some ⟨48, 80, 112, 6, false, false, .none⟩ := rfl
example : decode (2 ^ 46 + 2 ^ 52) = some ⟨0, 0, 0, 0, true, false, .none⟩ := rfl
example : decode (2 ^ 46 + 2 ^ 53) = some ⟨0, 0, 0, 0, false, true, .none⟩ := rfl

-- Table 49 codes are not the log2 of the swizzle width.
example : decode (2 ^ 46) = some ⟨0, 0, 0, 0, false, false, .none⟩ := rfl
example : decode (2 ^ 46 + 2 ^ 61) = some ⟨0, 0, 0, 0, false, false, .b128x32⟩ := rfl
example : decode (2 ^ 46 + 2 * 2 ^ 61) = some ⟨0, 0, 0, 0, false, false, .b128⟩ := rfl
example : decode (2 ^ 46 + 4 * 2 ^ 61) = some ⟨0, 0, 0, 0, false, false, .b64⟩ := rfl
example : decode (2 ^ 46 + 6 * 2 ^ 61) = some ⟨0, 0, 0, 0, false, false, .b32⟩ := rfl
example : Swizzle.offset .b128x32 128 = 160 := rfl
example : Swizzle.offset .b128 128 = 144 := rfl
example : Swizzle.sectors .b128x32 = 8 := rfl

-- Invalid modes, reserved bits, version bits and a word wider than 64 bits.
example : decode (2 ^ 46 + 3 * 2 ^ 61) = none := rfl
example : decode (2 ^ 46 + 5 * 2 ^ 61) = none := rfl
example : decode (2 ^ 46 + 7 * 2 ^ 61) = none := rfl
example : decode (2 ^ 46 + 2 ^ 15) = none := rfl
example : decode (2 ^ 46 + 2 ^ 31) = none := rfl
example : decode (2 ^ 46 + 2 ^ 54) = none := rfl
example : decode 0 = none := rfl
example : decode (2 ^ 47) = none := rfl
example : decode (2 ^ 46 + 2 ^ 64) = none := rfl

end PTX.Tests.TcSharedDescriptor

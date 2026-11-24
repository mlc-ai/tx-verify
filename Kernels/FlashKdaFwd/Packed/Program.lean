-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Decode.Compose
public import Kernels.FlashKdaFwd.Packed.Decode.Source
public import Kernels.FlashKdaFwd.Packed.Decode.Part0
public import Kernels.FlashKdaFwd.Packed.Decode.Part1
public import Kernels.FlashKdaFwd.Packed.Decode.Part2
public import Kernels.FlashKdaFwd.Packed.Decode.Part3
public import Kernels.FlashKdaFwd.Packed.Decode.Part4
public import Kernels.FlashKdaFwd.Packed.Decode.Part5
public import Kernels.FlashKdaFwd.Packed.Decode.Part6
public import Kernels.FlashKdaFwd.Packed.Decode.Part7
import Mathlib.Tactic.FinCases

@[expose] public section
namespace FlashKda.Packed
open PTX

set_option maxRecDepth 60000

def decoded : Except String Kernel :=
  let m := Generated.FlashKdaPacked.module
  Decode.kernelIn m.globals m.functions[0]!

private theorem windows (j : Fin 30) :
    (Transfers.slice (j.val*128) (min 128 (3835-j.val*128))).isSome = true := by
  fin_cases j
  · exact Transfers.decodes_0
  · exact Transfers.decodes_128
  · exact Transfers.decodes_256
  · exact Transfers.decodes_384
  · exact Transfers.decodes_512
  · exact Transfers.decodes_640
  · exact Transfers.decodes_768
  · exact Transfers.decodes_896
  · exact Transfers.decodes_1024
  · exact Transfers.decodes_1152
  · exact Transfers.decodes_1280
  · exact Transfers.decodes_1408
  · exact Transfers.decodes_1536
  · exact Transfers.decodes_1664
  · exact Transfers.decodes_1792
  · exact Transfers.decodes_1920
  · exact Transfers.decodes_2048
  · exact Transfers.decodes_2176
  · exact Transfers.decodes_2304
  · exact Transfers.decodes_2432
  · exact Transfers.decodes_2560
  · exact Transfers.decodes_2688
  · exact Transfers.decodes_2816
  · exact Transfers.decodes_2944
  · exact Transfers.decodes_3072
  · exact Transfers.decodes_3200
  · exact Transfers.decodes_3328
  · exact Transfers.decodes_3456
  · exact Transfers.decodes_3584
  · exact Transfers.decodes_3712

theorem full_decode_count : decoded.toOption.map (fun k => k.code.length) = some 3835 := by
  apply Transfers.assemble (m := prepared) (width := 128) (by decide) source_count
  intro j hj
  exact windows ⟨j, by omega⟩

theorem exists_kernel : decoded.toOption.isSome = true := by
  have h := congrArg Option.isSome full_decode_count
  simpa only [Option.isSome_map, Option.isSome_some] using h

private theorem get_ok (d : Except String Kernel) (h : d.toOption.isSome = true) :
    d = .ok (d.toOption.get h) := by
  cases d with
  | error e => cases h
  | ok k => rfl

theorem decoded_kernel : ∃ k, decoded = .ok k :=
  ⟨_, get_ok decoded exists_kernel⟩

noncomputable def kernel : Kernel := Classical.choose decoded_kernel

theorem decode_eq : decoded = .ok kernel := Classical.choose_spec decoded_kernel

theorem code_length : kernel.code.length = 3835 := by
  have h := full_decode_count
  rw [decode_eq] at h
  exact Option.some.inj h

theorem instructions {pc n : Nat} (h : pc+n ≤ 3835) :
    Transfers.slice pc n = some ((kernel.code.drop pc).take n) :=
  Transfers.from_whole pc n decode_eq (code_length ▸ h)

theorem code_window {pc n : Nat} {xs : List Instr} (fit : pc+n ≤ 3835)
    (read : Transfers.slice pc n = some xs) : (kernel.code.drop pc).take n = xs :=
  Option.some.inj ((instructions fit).symm.trans read)

theorem fetch {pc n i : Nat} {xs : List Instr} (fit : pc+n ≤ 3835) (hi : i < n)
    (read : Transfers.slice pc n = some xs) : kernel.code[pc+i]? = xs[i]? := by
  have h := congrArg (fun ys : List Instr => ys[i]?) (code_window fit read)
  simpa only [List.getElem?_take_of_lt hi, List.getElem?_drop] using h

end FlashKda.Packed

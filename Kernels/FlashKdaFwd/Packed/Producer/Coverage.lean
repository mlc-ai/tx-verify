-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Checks0
public import Kernels.FlashKdaFwd.Packed.Producer.Checks1
public import Kernels.FlashKdaFwd.Packed.Producer.Checks2
public import Kernels.FlashKdaFwd.Packed.Producer.Checks3

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX

private def spans : List (Nat × Nat) :=
  [(48,80), (128,128), (256,64), (320,1), (321,63), (384,128), (512,128), (640,128),
   (768,128), (896,128), (1024,128), (1152,128), (1280,128), (1408,3), (1411,1),
   (1412,23), (1435,1), (1436,100), (1536,128), (1664,128), (1792,90), (1882,1),
   (1883,37), (1920,128), (2048,68), (2116,1), (2117,59), (2176,128), (2304,128),
   (2432,128), (2560,128), (2688,128), (2816,128), (2944,52), (2996,1), (2997,1),
   (2998,74), (3072,128), (3200,128), (3328,128), (3456,128), (3584,128), (3712,65),
   (3777,1), (3778,57)]

private theorem verified : spans.all (fun s => window s.1 s.2 == some true) = true := by
  simp only [spans,List.all_cons,List.all_nil,
    window_48, window_128, window_256, window_320, window_321,
    window_384, window_512, window_640, window_768, window_896,
    window_1024, window_1152, window_1280, window_1408, window_1411,
    window_1412, window_1435, window_1436, window_1536, window_1664,
    window_1792, window_1882, window_1883, window_1920, window_2048,
    window_2116, window_2117, window_2176, window_2304, window_2432,
    window_2560, window_2688, window_2816, window_2944, window_2996,
    window_2997, window_2998, window_3072, window_3200, window_3328,
    window_3456, window_3584, window_3712, window_3777, window_3778]
  rfl

theorem certified {pc : Nat} {i : Instr} (low : 48 ≤ pc) (atPc : kernel.code[pc]? = some i) :
    accepts pc i = true := by
  have high : pc < 3835 := by
    have h := (List.getElem?_eq_some_iff.mp atPc).1
    rwa [code_length] at h
  have covers : spans.any (fun s => decide (s.1 ≤ pc ∧ pc < s.1+s.2)) = true := by
    simp only [spans,List.any_cons,List.any_nil,Bool.or_eq_true,decide_eq_true_eq]
    omega
  obtain ⟨⟨lo,n⟩,member,inside⟩ := List.any_eq_true.mp covers
  have fits : spans.all (fun s => decide (s.1+s.2 ≤ 3835)) = true := by decide
  exact at_window (beq_iff_eq.mp (List.all_eq_true.mp verified _ member))
    (of_decide_eq_true (List.all_eq_true.mp fits _ member))
    (of_decide_eq_true inside).1 (of_decide_eq_true inside).2 atPc

end FlashKda.Packed.ProducerControl

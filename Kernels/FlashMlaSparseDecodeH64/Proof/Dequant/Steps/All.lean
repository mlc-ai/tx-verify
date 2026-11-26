-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Head
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Row3
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Tail
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part042
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part043
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part044
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part045
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part046
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part047
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part048
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part049
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part050
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part051
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part052

@[expose] public section

/-! # Every state of warpgroup 2's control machine steps

`stepAt`: the obligation of every state, by its site, under `Pre` (the set-up's parameter
loads). -/

/-! # Warpgroup 2's obligations in row 0 of a block (pcs 2695–2919)

The scale load (`scale 0`, four elements), the eight raw-word loads (`raw 0 s`, any payload
continues) and the eight chunk stores (`store 0 s`); the float runs between them write data
registers only and are havocked, the chunk addresses are stepped exactly. -/

/-! # Warpgroup 2's obligations in row 2 of a block (pcs 3145–3369)

The scale load (`scale 2`, four elements), the eight raw-word loads (`raw 2 s`, any payload
continues) and the eight chunk stores (`store 2 s`); the float runs between them write data
registers only and are havocked, the chunk addresses are stepped exactly. -/

/-! # Warpgroup 2's obligations in row 1 of a block (pcs 2920–3144)

The scale load (`scale 1`, four elements), the eight raw-word loads (`raw 1 s`, any payload
continues) and the eight chunk stores (`store 1 s`); the float runs between them write data
registers only and are havocked, the chunk addresses are stepped exactly. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The scale load of row 1, element by element. -/
theorem stepAt_scale1 (d : D) (hs : d.site = .scale 1) : (code P L g w).StepAtU d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  dsimp only at hs; subst hs
  refine scaleAt rfl (by rfl) Flow.code_2920 rfl rfl rfl rfl rfl (by decide +kernel) ?_
  dq_seg

/-- The raw-word loads of row 1. -/
theorem stepAt_raw1 (d : D) (s : Fin 8) (hs : d.site = .raw 1 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · raw_at Flow.code_2954
  · raw_at Flow.code_2962
  · raw_at Flow.code_2985
  · raw_at Flow.code_3009
  · raw_at Flow.code_3033
  · raw_at Flow.code_3057
  · raw_at Flow.code_3081
  · raw_at Flow.code_3105

/-- The chunk stores of row 1. -/
theorem stepAt_store1 (d : D) (s : Fin 8) (hs : d.site = .store 1 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · st_at Flow.code_2977
  · st_at Flow.code_3001
  · st_at Flow.code_3025
  · st_at Flow.code_3049
  · st_at Flow.code_3073
  · st_at Flow.code_3097
  · st_at Flow.code_3121
  · st_at Flow.code_3144

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The scale load of row 2, element by element. -/
theorem stepAt_scale2 (d : D) (hs : d.site = .scale 2) : (code P L g w).StepAtU d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  dsimp only at hs; subst hs
  refine scaleAt rfl (by rfl) Flow.code_3145 rfl rfl rfl rfl rfl (by decide +kernel) ?_
  dq_seg

/-- The raw-word loads of row 2. -/
theorem stepAt_raw2 (d : D) (s : Fin 8) (hs : d.site = .raw 2 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · raw_at Flow.code_3179
  · raw_at Flow.code_3187
  · raw_at Flow.code_3210
  · raw_at Flow.code_3234
  · raw_at Flow.code_3258
  · raw_at Flow.code_3282
  · raw_at Flow.code_3306
  · raw_at Flow.code_3330

/-- The chunk stores of row 2. -/
theorem stepAt_store2 (d : D) (s : Fin 8) (hs : d.site = .store 2 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · st_at Flow.code_3202
  · st_at Flow.code_3226
  · st_at Flow.code_3250
  · st_at Flow.code_3274
  · st_at Flow.code_3298
  · st_at Flow.code_3322
  · st_at Flow.code_3346
  · st_at Flow.code_3369

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The scale load of row 0, element by element. -/
theorem stepAt_scale0 (d : D) (hs : d.site = .scale 0) : (code P L g w).StepAtU d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  dsimp only at hs; subst hs
  refine scaleAt rfl (by rfl) Flow.code_2695 rfl rfl rfl rfl rfl (by decide +kernel) ?_
  dq_seg

/-- The raw-word loads of row 0. -/
theorem stepAt_raw0 (d : D) (s : Fin 8) (hs : d.site = .raw 0 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · raw_at Flow.code_2729
  · raw_at Flow.code_2737
  · raw_at Flow.code_2760
  · raw_at Flow.code_2784
  · raw_at Flow.code_2808
  · raw_at Flow.code_2832
  · raw_at Flow.code_2856
  · raw_at Flow.code_2880

/-- The chunk stores of row 0. -/
theorem stepAt_store0 (d : D) (s : Fin 8) (hs : d.site = .store 0 s) :
    (code P L g w).StepAtU d := by
  dq_site
  fin_cases s
  · st_at Flow.code_2752
  · st_at Flow.code_2776
  · st_at Flow.code_2800
  · st_at Flow.code_2824
  · st_at Flow.code_2848
  · st_at Flow.code_2872
  · st_at Flow.code_2896
  · st_at Flow.code_2919

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- **Warpgroup 2's control machine steps from every state.** -/
theorem stepAt (hp : Pre P L m) (d : D) : (code P L g w).StepAtU d := by
  cases hs : d.site with
  | smr => exact stepAt_smr hp d hs
  | lenA => exact stepAt_lenA d hs
  | lenB => exact stepAt_lenB d hs
  | wq => exact stepAt_wq d hs
  | wraw => exact stepAt_wraw d hs
  | wsv => exact stepAt_wsv d hs
  | scale r =>
    fin_cases r
    · exact stepAt_scale0 d hs
    · exact stepAt_scale1 d hs
    · exact stepAt_scale2 d hs
    · exact stepAt_scale3 d hs
  | raw r s =>
    fin_cases r
    · exact stepAt_raw0 d s hs
    · exact stepAt_raw1 d s hs
    · exact stepAt_raw2 d s hs
    · exact stepAt_raw3 d s hs
  | store r s =>
    fin_cases r
    · exact stepAt_store0 d s hs
    · exact stepAt_store1 d s hs
    · exact stepAt_store2 d s hs
    · exact stepAt_store3 d s hs
  | fpx => exact stepAt_fpx d hs
  | arrD => exact stepAt_arrD d hs
  | arrF => exact stepAt_arrF d hs
  | bar => exact stepAt_bar d hs
  | exit => exact stepAt_exit d hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control

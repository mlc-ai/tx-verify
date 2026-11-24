-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Preparation0
public import Kernels.FlashKdaFwd.Packed.Producer.Preparation1

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX

theorem preparation_site {pc : Nat} {i : Instr} (lo : 315 ≤ pc) (hi : pc < 1402)
    (site : kernel.code[pc]? = some i) : preservesDispatch i = true := by
  by_cases h315 : pc < 320
  · exact inPreparationWindow preparation_315 (by decide) (by omega) (by omega) site
  by_cases h320 : pc < 321
  · exact inPreparationWindow preparation_320 (by decide) (by omega) (by omega) site
  by_cases h321 : pc < 384
  · exact inPreparationWindow preparation_321 (by decide) (by omega) (by omega) site
  by_cases h384 : pc < 512
  · exact inPreparationWindow preparation_384 (by decide) (by omega) (by omega) site
  by_cases h512 : pc < 640
  · exact inPreparationWindow preparation_512 (by decide) (by omega) (by omega) site
  by_cases h640 : pc < 768
  · exact inPreparationWindow preparation_640 (by decide) (by omega) (by omega) site
  by_cases h768 : pc < 896
  · exact inPreparationWindow preparation_768 (by decide) (by omega) (by omega) site
  by_cases h896 : pc < 1024
  · exact inPreparationWindow preparation_896 (by decide) (by omega) (by omega) site
  by_cases h1024 : pc < 1152
  · exact inPreparationWindow preparation_1024 (by decide) (by omega) (by omega) site
  by_cases h1152 : pc < 1280
  · exact inPreparationWindow preparation_1152 (by decide) (by omega) (by omega) site
  exact inPreparationWindow preparation_1280 (by decide) (by omega) hi site

end FlashKda.Packed.ProducerControl

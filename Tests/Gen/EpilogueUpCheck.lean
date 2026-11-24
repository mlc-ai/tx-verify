-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Gen.EpilogueUp
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Machine

@[expose] public section

/-! # The generated value table agrees with the output warp's hand-written one

`Tools/machine_gen.py` generates, from the PTX alone, the entries of the registers that the
first scan round's `up` steps and tile count assign once (`Tests/Gen/epilogue_up.json`). At
every register of the output warp's table (`partials`, `tilesOf`) the generated entry is the
hand-written one by `rfl`: the generated table mirrors the code in the same vocabulary. -/

namespace PTX.Tests.Gen.EpilogueUp
open PTX PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue

theorem upFirst_partials (L : Launch) (g : Nat) (d : D) :
    ∀ r ∈ [2317, 2320, 2323, 2326, 7221],
      (upFirst (laneW L g) d.tl d.u1 d.u2 d.u4 d.u8 d.u16).lookup r =
        (partials L g d 2317 3 7221).lookup r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl) <;> rfl

theorem tilesFirst_tilesOf (dn w : BitVec 64) :
    (tilesFirst w dn).lookup 7220 = some (.bits 32 (tilesOf dn w)) := rfl

end PTX.Tests.Gen.EpilogueUp

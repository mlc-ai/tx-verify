-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Iface.QueryTile
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryCovered
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryStore
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryWord

@[expose] public section

/-! # The query tile as the prologue stores it

Every query store writes a word of two bf16 numbers or zero (`query_word`), no location is stored
twice (`query_once`), and every byte of the tile of an MMA's CTA is stored (`query_covered`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX

/-- **The query tile as the prologue stores it.** -/
theorem query_tile {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) : Iface.QueryTile L X where
  word he := Prologue.Export.query_word hp hX hf he
  once he he' loc := Prologue.Export.query_once hp hX hf words he he' loc
  covered mma inq cta := query_covered hp hX hf mma inq cta

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values

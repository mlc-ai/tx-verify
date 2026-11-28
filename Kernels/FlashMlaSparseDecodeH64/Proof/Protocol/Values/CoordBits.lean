-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.CoordRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.StoreWr
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Use
import Lemmas.Data.RebuildBits

@[expose] public section

/-! # The coordinate words the TMA lane reads are 32-bit words

Each byte `i` of a coordinate word the TMA lane reads is the byte of an index lane's write of four
bytes (`coord_read_byte`), the bytes of a 32-bit value (`index_wr_bits`), so the word rebuilds
(`rebuild_bits32`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The TMA warp's reads rebuild 32-bit words.** -/
theorem coord_words_bits (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : CoordInputs L X) : CoordWordsBits L X := by
  intro g k pc a bs he hat
  obtain ⟨-, s, ⟨q, hq, jj, hjj, hl', hsz⟩, -⟩ := tma_rdUse hp hX hFw he hat
  have hlen : bs.length = a.size := ((hX.rf (.thread (g, k)) a bs (Or.inl ⟨pc, he⟩)).1)
  refine rebuild_bits32 (by omega) fun i hi => ?_
  obtain ⟨s', u, q', jj', gw, kw, pcw, aw, bsw, hq', hjj', ⟨hl2, hs2⟩, -, hget, hatw,
    ⟨hawl, hawz⟩, -, -, -, hbytes⟩ := coord_read_byte hp hX hFw hR hI hB hN he hat
  have hbyte := hbytes i (by omega)
  rcases index_wr_bits hp hX hFw hget hatw with ⟨z, hz, -⟩ | ⟨z, -, h1⟩
  · refine ⟨z, ?_⟩
    rw [hbyte, wbyte, hz]
    have hd : (a.loc.at i).addr - aw.loc.addr = i := by
      rw [hl2, hawl]
      simp only [Loc.at, wsLoc]
      omega
    rw [hd]
    simp [Value.toBytes, Value.bytes, Value.byteAt, hi]
  · omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

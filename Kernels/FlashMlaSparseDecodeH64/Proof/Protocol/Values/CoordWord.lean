-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.CoordRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.StoreWr
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Use
import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # The word a coordinate read returns is the index lane's stored word

The four bytes a coordinate read of the TMA lane returns are the bytes of one 32-bit write of the
index lane `2 q + jj / 2` (`coord_read_byte` at every byte), so the read's word is the written
word `z` (`coord_read_val`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A coordinate read returns the word of the write it reads.** -/
theorem coord_read_val (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : CoordInputs L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.TmaAt L g pc) :
    ∃ (s : Fin 4) (u q jj gw kw pcw : Nat) (aw : Acc) (z : BitVec 64), q < 16 ∧ jj < 4 ∧
      MemRow.WsAcc L (g / L.block) (221728 + 256 * s.val + 16 * q + 4 * jj) 4 a ∧
      gw = g / L.block * L.block + 224 + (2 * q + jj / 2) ∧
      X.get (gw, kw) = some ⟨pcw, .wr aw (Value.bits 32 z).toBytes⟩ ∧ MbarRow.IndexAt L gw pcw ∧
      aw.size = 4 ∧
      okPolls (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u + 1 ∧
      ((X.tr gw).take kw).countP idxWr =
        (2 + if (L.tidOf gw).x % 4 = 0 then 1 else 0) * (4 * u + s.val) + jj % 2 ∧
      rdVal ⟨pc, .rd a bs⟩ = .bits 32 z := by
  obtain ⟨s, u, q, jj, gw, kw, pcw, aw, bsw, hq, hjj, ⟨hl, hsz⟩, hgw, hget, hatw, ⟨hawl, hawz⟩,
    hv1, -, hcnt, hbytes⟩ := coord_read_byte hp hX hFw hR hI hB hN he hat
  have hlen : bs.length = a.size := ((hX.rf (.thread (g, k)) a bs (Or.inl ⟨pc, he⟩)).1)
  rcases index_wr_bits hp hX hFw hget hatw with ⟨z, hz, -⟩ | ⟨z, -, h1⟩
  · have hbs : bs = (Value.bits 32 z).toBytes.map some := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < 4
      · rw [hbytes i (by omega), wbyte, hz]
        have hd : (a.loc.at i).addr - aw.loc.addr = i := by
          rw [hl, hawl]
          simp only [Loc.at, wsLoc]
          omega
        rw [hd, List.getElem?_map, List.getElem?_eq_getElem
          (l := (Value.bits 32 z).toBytes) (by simp [Value.toBytes, Value.bytes, hi])]
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
        simp [Value.toBytes, Value.bytes]
        omega
    refine ⟨s, u, q, jj, gw, kw, pcw, aw, z, hq, hjj, ⟨hl, hsz⟩, hgw, ?_, hatw, hawz, hv1, hcnt, ?_⟩
    · rw [← hz]; exact hget
    · simp only [rdVal]
      rw [hbs, PTX.Proof.rebuild_scalar (by simp [Value.bytes]) (by simp [Value.byteAt])]
      rfl
  · omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

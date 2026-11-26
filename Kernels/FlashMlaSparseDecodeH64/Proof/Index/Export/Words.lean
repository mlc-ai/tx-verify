-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.PairWord

@[expose] public section

/-! # The index warp's pair loads read 32-bit words

A pair load of the index warp (pcs `2403`, `2429`, `2501`, `2517`) reads the four bytes of a word
of the lane's index row (`index_mainPairAddr`, `index_extraPairAddr`), which `Pre` allocates
(`idxInput`, `extraIdxInput`) and which the read-only assumption returns (`rebuild_word`): the bytes
the read records rebuild to a 32-bit word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A main pair load's payload is a 32-bit word.** -/
theorem index_mainPairWord (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩) (hpc : pc = 2403 ∨ pc = 2429) :
    ∃ y, rebuild 3 bs = .ok (.bits 32 y) := by
  obtain ⟨b, el, -, -, -, hlt, hsz, hloc⟩ := index_mainPairAddr hp hX hFw he hpc
  exact ⟨_, main_pair_word hp hX he hpc hlt hsz hloc⟩

/-- **An extra pair load's payload is a 32-bit word.** -/
theorem index_extraPairWord (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩) (hpc : pc = 2501 ∨ pc = 2517) :
    ∃ y, rebuild 3 bs = .ok (.bits 32 y) := by
  obtain ⟨b, el, -, -, -, hlt, hsz, hloc⟩ := index_extraPairAddr hp hX hFw he hpc
  exact ⟨_, extra_pair_word hp hX he hpc hlt hsz hloc⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

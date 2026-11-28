-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.PairCore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The index warp's pair loads read the row's int32 words: the cores

At a pair load whose access is word `j` of the lane's index row (`main_pair_core`,
`extra_pair_core`), which `Pre` allocates (`idxInput`, `extraIdxInput`) and which the read-only
assumption returns (`rebuild_acc`), the bytes the read records rebuild to the int32 word of the
row's index (`main_pair_word`, `extra_pair_word`). No `Follow` is used. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A read-only word** (`rebuild_word` for a load whose access has any flags). -/
theorem rebuild_acc (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {pc addr n : Nat} {a : Acc} {bs : List (Option Byte)} (hget : X.get i = some ⟨pc, .nc a bs⟩)
    (hsite : ncLoads.contains pc = true) (hloc : a.loc = ⟨.global, 0, addr⟩) (hsz : a.size = 4)
    (hmem : ∀ k < 4, m ⟨.global, 0, addr + k⟩ = some (some (word32Byte n k))) :
    rebuild 3 bs = .ok (b32 n) := by
  have hc := hX.asm Assumptions.ncReadOnly (by simp [Assumptions.all])
  obtain ⟨hlen, hbytes⟩ := hc i pc a bs hget hsite
  have heq : bs = (b32 n).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hv := hbytes k (by omega) _ (by
        have := hmem k hk
        rw [show a.loc.at k = ⟨.global, 0, addr + k⟩ by rw [hloc]; rfl]
        exact this)
      simp only [Execution.initialByte, Option.getD_some] at hv
      rw [hv]
      simp [Value.toBytes, b32, word32Byte, List.getElem?_range hk, Value.bytes]
    · have hb : bs.length = 4 := by rw [hlen, hsz]
      rw [List.getElem?_eq_none (by omega)]
      symm
      apply List.getElem?_eq_none
      simpa [Value.toBytes, b32, Value.bytes] using Nat.le_of_not_gt hk
  rw [heq]
  exact rebuild_scalar (show 0 < 4 by decide) rfl


/-- **A main pair load's payload is the int32 word of its index.** -/
theorem main_pair_word (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩) (hpc : pc = 2403 ∨ pc = 2429) {b el : Nat}
    (hlt : 64 * b + 2 * (tidOf L g % 32) + el < P.topk) (hsz : a.size = 4)
    (hloc : a.loc = ⟨.global, 0, P.indicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * P.topk +
        (64 * b + 2 * (tidOf L g % 32) + el))⟩) :
    rebuild 3 bs = .ok (b32 (i32Bits (P.idx (ctaidY L g) (ctaidX L g)
      (64 * b + 2 * (tidOf L g % 32) + el)))) := by
  obtain ⟨hx, hy⟩ := ctaid_lt hp g
  have hs : ncLoads.contains pc = true := by rcases hpc with rfl | rfl <;> decide
  exact rebuild_acc hX he hs hloc hsz fun k hk => hp.idxInput _ hy _ hx _ hlt k hk

/-- **An extra pair load's payload is the int32 word of its index.** -/
theorem extra_pair_word (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .nc a bs⟩) (hpc : pc = 2501 ∨ pc = 2517) {b el : Nat}
    (hlt : 64 * b + 2 * (tidOf L g % 32) + el < P.extra_topk) (hsz : a.size = 4)
    (hloc : a.loc = ⟨.global, 0, P.extraIndicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) *
        P.extra_topk + (64 * b + 2 * (tidOf L g % 32) + el))⟩) :
    rebuild 3 bs = .ok (b32 (i32Bits (P.extraIdx (ctaidY L g) (ctaidX L g)
      (64 * b + 2 * (tidOf L g % 32) + el)))) := by
  obtain ⟨hx, hy⟩ := ctaid_lt hp g
  have hpos : 0 < P.extra_topk := by omega
  have hs : ncLoads.contains pc = true := by rcases hpc with rfl | rfl <;> decide
  rcases hp.extraIdxInput with h0 | ⟨-, h⟩
  · omega
  · exact rebuild_acc hX he hs hloc hsz fun k hk => h _ hy _ hx _ hlt k hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

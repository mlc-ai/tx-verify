-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvCopies
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvByte
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyOrigin
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyCount
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadSlab
import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Kernels.InklingRelDecode.Proof.Protocol.KV.Ready
import Kernels.InklingRelDecode.Proof.Protocol.KV.PollCount

@[expose] public section

/-! # A copy of the ring is the copy of one block, its use is the block over three

Every tensor copy to the ready barrier of slot `σ` is the copy of a box of the slab `h` of the
block `n` of its CTA's split, to the half `hh` of the K (`isV = 0`) or V tile, in slot `n % 3`
(the loader's copy at its loop counter `n`, or a prologue preload of block `n < 3`), and the use of
the slot it is a copy of is `n / 3`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The box a copy lands in is in one slot of the ring. -/
private theorem slot_of_box (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {g k pc a sp σ s0 isV h hh col row} (_hV : isV ≤ 1) (_hH : h ≤ 1)
    (_hhh : hh ≤ 1) (s3 : s0 < 3) (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = Iface.kvReadyLoc L (g / L.block) σ)
    (hsp : sp = Lib.kvCopySpec Q (g / L.block) col row
      (L.sharedBase + 32768 * s0 + 16384 * hh + 98304 * isV + 8192 * h) sp.mbar) :
    σ.val = s0 := by
  obtain ⟨l0, h0⟩ := copy_first Q (g / L.block) col row
    (L.sharedBase + 32768 * s0 + 16384 * hh + 98304 * isV + 8192 * h) sp.mbar
  rw [← hsp] at h0
  obtain ⟨-, -, lo, hi⟩ := Lib.copy_foot Q _ _ _ _ _ (hsp ▸ h0)
  obtain ⟨-, slot⟩ := copy_dest hp hX hf he hm h0
  unfold Iface.InSlot at slot
  have := σ.isLt
  omega

/-- **A tensor copy to the ready barrier of slot `σ` is the copy of a box of one block**. -/
theorem copy_block (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X) {g k pc a sp}
    {σ : Fin 3} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (bar : sp.mbar = Iface.kvReadyLoc L (g / L.block) σ) :
    ∃ n isV h hh : Nat, n % 3 = σ.val ∧
      SingleTmaRing.copyUse X ((KV.decl Q L X (g / L.block)).slot σ) (g, k) = n / 3 ∧
      isV ≤ 1 ∧ h ≤ 1 ∧ hh ≤ 1 ∧
      2 * (Q.splits * n + (L.ctaidOf (g / L.block)).get .x) + h <
        2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z) ∧
      sp = Lib.kvCopySpec Q (g / L.block)
        ((L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * isV + 64 * hh)
        (Q.page ((L.ctaidOf (g / L.block)).get .z)
          (2 * (Q.splits * n + (L.ctaidOf (g / L.block)).get .x) + h) * Q.pageRows +
          (L.ctaidOf (g / L.block)).get .y * Q.headRows)
        (L.sharedBase + 32768 * σ.val + 16384 * hh + 98304 * isV + 8192 * h) sp.mbar := by
  have hg := Frame.lt_of_get hX he
  have hcg : g / L.block < L.grid :=
    Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  have hyp := KV.ready_slot hp hX hf rows init hcg σ
  have cls := hyp.issue he bar
  unfold SingleTmaRing.copyUse
  rcases cls with ⟨hcp, -⟩ | ⟨hδ, i, hi⟩
  · have warp : g % L.block / 32 = 6 := by
      have := (KV.leader_warp (X := X) hp hcg (by omega : 6 < 8)).2.2
      rw [hcp.trans rfl]
      exact this
    obtain ⟨site, pos, cnt, hσ⟩ := Loader.Export.copy_count hp hX hf he warp bar
    have site' : pc ∈ [2389, 2391, 2394, 2396, 2404, 2406, 2410, 2412] := site
    obtain ⟨j, D, hj, hD, hl, hsp⟩ := Loader.Export.copy_slab_at hp hX hf he site'
    have idx := Iface.copyIndex_lt site
    have nopre : ¬ (((KV.decl Q L X (g / L.block)).slot σ).δ = 1 ∧
        ∃ i, (g, k) = ((KV.decl Q L X (g / L.block)).slot σ).pCp i) := by
      rintro ⟨hδ, i, hi⟩
      exact (hyp.pre_ne hδ).2 i (by rw [← hi]; exact hcp)
    simp only [nopre, ↓reduceIte]
    have off : Iface.copyOff pc = 8192 * (Iface.copyIndex pc / 4) +
        98304 * (Iface.copyIndex pc / 2 % 2) + 16384 * (Iface.copyIndex pc % 2) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at site'
      rcases site' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have hjσ : j % 3 = σ.val := by
      have : σ.val = (Iface.preloadCount Q L (g / L.block) +
        pollRound 2374 ((X.tr g).take k) - 1) % 3 := hσ
      omega
    refine ⟨j, Iface.copyIndex pc / 2 % 2, Iface.copyIndex pc / 4, Iface.copyIndex pc % 2,
      hjσ, ?_, by omega, by omega, by omega, hl, ?_⟩
    · have bar' : sp.mbar = ((KV.decl Q L X (g / L.block)).slot σ).full := bar
      rw [bar'] at cnt
      change ((X.tr g).take k).countP (issuesTo ((KV.decl Q L X (g / L.block)).slot σ).full) /
        8 + KV.preload Q L (g / L.block) σ = j / 3
      rw [cnt]
      unfold Iface.ringVisits KV.preload
      have pc3 : Iface.preloadCount Q L (g / L.block) ≤ 3 := Nat.min_le_left _ _
      have := σ.isLt
      split_ifs <;> omega
    · have eq : D = L.sharedBase + 32768 * σ.val + 16384 * (Iface.copyIndex pc % 2) +
          98304 * (Iface.copyIndex pc / 2 % 2) + 8192 * (Iface.copyIndex pc / 4) := by
        rw [hD, hjσ, off]
        omega
      rw [eq] at hsp
      exact hsp
  · have hgl : g = KV.leader L X (g / L.block) (i.val / 4) := congrArg Prod.fst hi
    have ilt : i.val < 8 := i.isLt
    have warp : g % L.block / 32 < 2 := by
      have := (KV.leader_warp (X := X) hp hcg (by omega : i.val / 4 < 8)).2.2
      rw [← hgl] at this
      omega
    have pre : ((KV.decl Q L X (g / L.block)).slot σ).δ = 1 ∧
        ∃ i, (g, k) = ((KV.decl Q L X (g / L.block)).slot σ).pCp i := ⟨hδ, i, hi⟩
    simp only [pre, and_self, ↓reduceIte]
    have site : pc ∈ [211, 217, 226, 231, 253, 259, 268, 273, 295, 301, 310, 315] := by
      rcases Lib.tensor_issue_site hX he with h | h
      · exact h
      · have := Loader.Export.copy_warp hp hX hf he h
        omega
    obtain ⟨b, isV, h, hh, hV, hH, hhh, hl, hsp⟩ := Prologue.Export.preload_slab_at hp hX hf he site
    have hσb : σ.val = b.val :=
      slot_of_box hp hX hf hV hH hhh b.isLt he bar hsp
    have e : 2 * (Q.splits * b.val + (L.ctaidOf (g / L.block)).get .x) + h =
        2 * ((L.ctaidOf (g / L.block)).get .x + b.val * Q.splits) + h := by
      ring
    have := b.isLt
    refine ⟨b.val, isV, h, hh, by omega, by omega, hV, hH, hhh, by rw [e]; exact hl, ?_⟩
    rw [e, hσb]
    exact hsp

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values

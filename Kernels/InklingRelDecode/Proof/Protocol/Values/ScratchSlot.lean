-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchEqual
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchSample
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchAgree
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchLater
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleOrdinal
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly
import Kernels.InklingRelDecode.Proof.Softmax.Export.PollKeep

@[expose] public section

/-! # A scratch read returns the bytes of one scratch store of its warp and round

The four bytes a lane reads at pc 2252 are the bytes of the payload of one scratch store of pc
2250, issued by a lane of the warp the reading lane's index modulo four names, in the reader's
round: the stores that supply the bytes are in one warp's slot at one barrier ordinal, so they
write the same bytes (`stores_equal`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Shared Softmax.Export Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A scratch read returns the bytes of one scratch store**, of the warp and the round of the
reader. -/
theorem scratch_slot (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (agree : ∀ n, StoreAgree L X n) (equal : WarpStoresEqual L X)
    {g j a bs} (read : X.get (g, j) = some ⟨2252, .rd a bs⟩) :
    ∃ h u dst ys, X.get (h, u) = some ⟨2250, .wr dst ys⟩ ∧ (∀ b < 4, bs[b]? = some ys[b]?) ∧
      h / L.block = g / L.block ∧ h % L.block / 32 % 4 = g % L.block % 4 ∧
      pollRound 1257 ((X.tr h).take u) = pollRound 1257 ((X.tr g).take j) := by
  have lg := data_site hp hX read (by simp) (by dsimp; decide) (by dsimp; decide)
  obtain ⟨u, rfl, sync⟩ := read_sync hp hX read
  have ord : barOrdinal X g (u + 1) = barOrdinal X g u + 1 := by
    unfold barOrdinal
    rw [List.take_add_one, show (X.tr g)[u]? = _ from sync, List.countP_append]
    rfl
  have uni := rescale_agree_by hp hX hf (fun m _ => agree m) sync (by simp) rfl rfl lg
  have pub := scratch_next_publication hp hX hf read
    (fun h' ch lh' n' lt' => uni h' g ch lh' rfl lg n' lt')
  obtain ⟨whereRead, size⟩ := scratch_read hp hX read
  have sample : ∀ b < 4, ∃ h u' dst ys,
      ScratchByte L X g (u + 1) b a bs (barOrdinal X g u) h u' dst ys :=
    fun b hb => scratch_sample hp hX read ord pub (by omega)
  have warp : ∀ {b h u' dst ys}, ScratchByte L X g (u + 1) b a bs (barOrdinal X g u) h u' dst ys →
      h % L.block / 32 % 4 = g % L.block % 4 := fun s => by
    obtain ⟨l1, -⟩ := scratch_store hp hX s.store
    have e := (l1.symm.trans s.addr).trans whereRead
    have := (Loc.mk.inj e).2.2
    have hb := hp.block
    simp only [hb] at this ⊢
    omega
  obtain ⟨h0, u0, d0, y0, s0⟩ := sample 0 (by omega)
  have peer := scratch_peer_round hp hX hf read s0.sync s0.cta s0.low s0.epoch
    (visits_equal hp hX sync s0.sync s0.cta s0.low s0.epoch
      (fun h' ch lh' n' lt' => uni h' g ch lh' rfl lg n' lt'))
  refine ⟨h0, u0, d0, y0, s0.store, fun b hb => ?_, s0.cta, warp s0, ?_⟩
  · obtain ⟨h1, u1, d1, y1, s1⟩ := sample b hb
    have hw : h1 % L.block / 32 = h0 % L.block / 32 := by
      have := warp s1
      have := warp s0
      have := s0.low
      have := s1.low
      have hb := hp.block
      simp only [hb] at *
      omega
    rw [s1.value, stores_equal hp hX hf equal (fun n _ => agree n) s1.store s0.store
      (s1.cta.trans s0.cta.symm) hw (by rw [← ord_store s1.store, ← ord_store s0.store,
        s1.epoch, s0.epoch])]
  · have a1 := poll_keep s0.store (by show 2250 ≠ 1257; omega)
    have a2 := poll_keep sync (by show 2251 ≠ 1257; omega)
    rw [← a1, peer.2, a2]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values

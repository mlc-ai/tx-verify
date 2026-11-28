-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PvStore
import Lemmas.Tcgen05.TcProgramOrder
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcMmaSource

@[expose] public section

/-! # The order of a PV MMA against the accumulator load and the rescale store of a round

A PV MMA of ordinal `b` (its `b`-th poll of the probability slot) follows the accumulator load and
the rescale store of every round `r < b`, and every PV MMA of ordinal at most `r` is done before
the load of round `r`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.MbarRing PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A PV MMA of ordinal `b > r` follows the accumulator load of round `r`.** -/
public theorem ld_pv_big (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh r gq kq jp}
    {d s acc mask b}
    (he : X.get (t, k0) = some ⟨2260, .tc (.ld a vals sh)⟩)
    (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1)
    (gw : X.get (gq, kq) = some ⟨Lib.pvIssue jp, .tc (.mma d s acc mask)⟩)
    (cw : t / L.block = gq / L.block) (pb : pollRound 2510 ((X.tr gq).take kq) = b)
    (big : r < b) : ReadBefore L X .ld (t, k0) (gq, kq) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t / L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  have hg := Frame.lt_of_get hX gw
  obtain ⟨lead, -⟩ := mma_leader hp hX hf gw
  have lead2 : Protocol.KV.leader L X (t / L.block) 7 = gq := by rw [cw]; exact lead
  have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 r)) kq
  change okPolls ((Object.prob (MbarRow.slot2 r)).loc L (gq / L.block)) ((X.tr gq).take kq) =
    (Object.prob (MbarRow.slot2 r)).visits (pollRound 2510 ((X.tr gq).take kq)) at cnt
  rw [pb, ← cw] at cnt
  have vis : (Object.prob (MbarRow.slot2 r)).visits b = (b + 2 - 1 - r % 2) / 2 := rfl
  have hk : kq < (X.tr gq).length := (List.getElem?_eq_some_iff.mp gw).1
  have lt := Proof.Export.tc_data_lane hp hX hf he rfl
  have := ld_before_mma hp hX hf safe base rows init words hc he (.inr rfl) lt rfl s1
    (k := kq) (by rw [lead2]; exact hk) (by rw [lead2, cnt, vis]; omega)
  rw [lead2] at this
  exact .inl this

/-- **A PV MMA of ordinal `b ≤ r` is done before the accumulator load of round `r`.** -/
public theorem ld_pv_small (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh r gq kq jp}
    {d s acc mask b}
    (he : X.get (t, k0) = some ⟨2260, .tc (.ld a vals sh)⟩)
    (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1)
    (gw : X.get (gq, kq) = some ⟨Lib.pvIssue jp, .tc (.mma d s acc mask)⟩)
    (cw : t / L.block = gq / L.block) (pb : pollRound 2510 ((X.tr gq).take kq) = b)
    (small : b ≤ r) : WriteBefore L X (gq, kq) (t, k0) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t / L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  have hg := Frame.lt_of_get hX gw
  obtain ⟨lead, -⟩ := mma_leader hp hX hf gw
  have lead2 : Protocol.KV.leader L X (t / L.block) 7 = gq := by rw [cw]; exact lead
  obtain ⟨-, -, -, -, -, -, warp, -⟩ := Mma.Export.pv_block hp hX hf base gw ⟨jp, rfl⟩
  have pv : Lib.pvIssue jp ∈ [2530, 2533, 2535, 2537, 2539, 2541, 2543, 2545] := by
    fin_cases jp <;> decide
  obtain ⟨r0, -, s1', s2, -, -, rpos⟩ := Proof.Export.ld_round hp hX hf base he rfl (.inr rfl)
  have r1 := rpos rfl
  have lt := Proof.Export.tc_data_lane hp hX hf he rfl
  have hr0 : r0 = r := by omega
  subst hr0
  simp at s2
  have lpos := Protocol.Scalar.count rows ht Object.done k0
  change okPolls (Object.done.loc L (t / L.block)) ((X.tr t).take k0) =
    Object.done.visits (pollRound 2239 ((X.tr t).take k0)) at lpos
  rw [s2] at lpos
  have vis : Object.done.visits r0 = (r0 + 1 - 1 - 0) / 1 := rfl
  obtain ⟨jp', pcj, pj, acq, scj, hjk, hwj, hq⟩ := UnitHandoff.exists_poll
    (m := Object.done.loc L (t / L.block)) (h := t) (f := k0) (c := b - 1)
    (by rw [lpos, vis]; omega)
  have few := pv_commits_before hp hX hf rows words (c := t / L.block) hg gw pv warp pb
  have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  exact .inl (.inl (mma_done_lane hp hX hf safe rows init words hc (o := Object.done)
    (Or.inr rfl) lt rfl hwj hq gw (by rw [← lead2, cw]) (by dsimp only; omega)
    (.single (.inl (po_of_source_not_access rfl hjk lent (by rw [hwj]; rfl))))))

/-- Every rescale store follows an accumulator load of its own round in its thread. -/
def RescaleLd (X : Execution) : Prop :=
  ∀ t k a vals sh, X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩ →
    ∃ kl < k, ∃ a' ov sh', X.get (t, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩ ∧
      pollRound 1257 ((X.tr t).take kl) = pollRound 1257 ((X.tr t).take k)

/-- **A PV MMA of ordinal `b > r` follows the rescale store of round `r`.** -/
public theorem store_pv_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t sk a vals sh r gq kq jp}
    {d s acc mask b}
    (hy : X.get (t, sk) = some ⟨2328, .tc (.st a vals sh)⟩)
    (rd : pollRound 1257 ((X.tr t).take sk) = r + 1)
    (gw : X.get (gq, kq) = some ⟨Lib.pvIssue jp, .tc (.mma d s acc mask)⟩)
    (cw : t / L.block = gq / L.block) (pb : pollRound 2510 ((X.tr gq).take kq) = b)
    (big : r < b) : StoreDoneBefore L X (t, sk) (gq, kq) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX hy
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t / L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  have hg := Frame.lt_of_get hX gw
  obtain ⟨lead, -⟩ := mma_leader hp hX hf gw
  have lead2 : Protocol.KV.leader L X (t / L.block) 7 = gq := by rw [cw]; exact lead
  have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 r)) kq
  change okPolls ((Object.prob (MbarRow.slot2 r)).loc L (gq / L.block)) ((X.tr gq).take kq) =
    (Object.prob (MbarRow.slot2 r)).visits (pollRound 2510 ((X.tr gq).take kq)) at cnt
  rw [pb, ← cw] at cnt
  have vis : (Object.prob (MbarRow.slot2 r)).visits b = (b + 2 - 1 - r % 2) / 2 := rfl
  have hk : kq < (X.tr gq).length := (List.getElem?_eq_some_iff.mp gw).1
  have lt := Proof.Export.tc_data_lane hp hX hf hy rfl
  have := store_before_mma hp hX hf safe base rows init words hc hy (.inr rfl) lt rfl rd
    (k := kq) (by rw [lead2]; exact hk) (by rw [lead2, cnt, vis]; omega)
  rw [lead2] at this
  exact this

/-- **A PV MMA of ordinal `b ≤ r` is written before the rescale store of round `r`.** -/
public theorem pv_store_small (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (tie : RescaleLd X)
    {t sk a vals sh r gq kq jp} {d s acc mask b}
    (hy : X.get (t, sk) = some ⟨2328, .tc (.st a vals sh)⟩)
    (rd : pollRound 1257 ((X.tr t).take sk) = r + 1)
    (gw : X.get (gq, kq) = some ⟨Lib.pvIssue jp, .tc (.mma d s acc mask)⟩)
    (cw : t / L.block = gq / L.block) (pb : pollRound 2510 ((X.tr gq).take kq) = b)
    (small : b ≤ r) : WriteBefore L X (gq, kq) (t, sk) := by
  obtain ⟨kl, lk, a', ov, sh', he, same⟩ := tie t sk a vals sh hy
  have ht := Frame.lt_of_get hX hy
  have wl := ld_pv_small hp hX hf safe base rows init he (r := r) (by omega) gw cw pb small
  have lenq : sk < (X.tr t).length := (List.getElem?_eq_some_iff.mp hy).1
  have ldst : ReadBefore L X .ld (t, kl) (t, sk) := .inr ⟨TcMma.sameWarp_self ht,
    .inl (baseCausality_of_tc_po he rfl lk lenq), ⟨_, _, _, _, he⟩, ⟨_, _, _, _, hy⟩⟩
  have ne : (t, sk) ≠ (t, kl) := fun h => by simp at h; omega
  rcases pv_store_order hp hX hf safe base rows init (gq, kq) (t, sk) _ d _ s acc mask _ _ gw
    ⟨jp, rfl⟩ hy cw.symm with h | h
  · exact .inl (.inl h)
  · exact absurd ((h.tcStep.trans (wl.tcStep.trans (ldst.tcStep ne)))) (tcStep_acyclic hX hG _)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values

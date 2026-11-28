-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Life.Exit
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Protocol.KV.Ready
import Kernels.InklingRelDecode.Proof.Protocol.KV.PollCount
import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyCount
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Prologue.Export.CopyFoot
import Kernels.InklingRelDecode.Proof.Mma.Export.ShuffleTotal
import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Lemmas.Protocol.SingleTmaRing.Order

@[expose] public section

/-! # A tensor load's arrival finishes before its CTA exits

The kernel's tensor loads (the prologue's preloads and the loader's copies) complete on `kv_ready`
of their CTA, which the MMA warp polls for every block. A load whose CTA exited is observed by a
successful poll of its mbarrier by a lane of the CTA (`LoadObserved`), and an observed update
finishes before the polling lane's exit (`observed_finished`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

variable {L : Launch} {m : Mem0} {X : Execution}

/-- **Every tensor load of an exited CTA is observed** by a successful poll of its mbarrier by a
lane of the CTA. -/
def LoadObserved (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc a s, X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ → CtaExited L X (g / L.block) →
    ∃ h j acq ws, h / L.block = g / L.block ∧
      WaitObserves X (.async (g, k) (.notify .load)) (h, j) s.mbar acq ws

/-- **`LoadNotified`** from the observation of every tensor load. -/
theorem load_notified (hX : Consistent L kernel Assumptions.all m X) (hobs : LoadObserved L X) :
    LoadNotified L kernel Assumptions.all X := by
  rintro ⟨g, k⟩ a s ⟨pc, he⟩ hx
  obtain ⟨h, j, acq, ws, hhc, hw⟩ := hobs g k pc a s he hx
  have := observed_finished hX hw (by simpa [hhc] using hx)
  simpa [hhc] using this


/-- The ready polls of the MMA warp's leader number the visits of its poll rounds. -/
private theorem ready_visits {Q : Params} {c y : Nat} (rows : MbarRows Q L X)
    (hy : y < L.threads) (warp : y % L.block / 32 = 7) (cta : y / L.block = c) (σ : Fin 3) :
    okPolls (KV.Ring.ready.obj L c σ) (X.tr y) = (pollRound 2462 (X.tr y) + 2 - σ.val) / 3 := by
  have := KV.poll_count (r := .ready) rows hy warp σ (X.tr y).length
  rw [cta, List.take_length] at this
  rw [this]
  simp only [KV.Ring.start, KV.Ring.site, MbarRow.roundAt, List.take_length, KV.visits]
  have := σ.isLt
  omega

/-- **Every tensor load of an exited CTA is observed** by the poll of `kv_ready` of the MMA warp's
leader with as many earlier polls as the copy's use of the slot: the leader polled every block. -/
theorem load_observed {Q : Params} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (hu : NoUbOutside L X) : LoadObserved L X := by
  intro g k pc a s he hx
  have hg := Frame.lt_of_get hX he
  obtain ⟨c, hcg⟩ : ∃ c, g / L.block = c := ⟨_, rfl⟩
  have hc : c < L.grid :=
    hcg ▸ Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  obtain ⟨hy, cy, wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7 < 8)
  obtain ⟨-, -, w6⟩ := KV.leader_warp (X := X) hp hc (by decide : 6 < 8)
  rw [hcg] at hx ⊢
  obtain ⟨σ, bar0⟩ : ∃ σ : Fin 3, s.mbar = Iface.kvReadyLoc L (g / L.block) σ := by
    rcases Lib.tensor_issue_site hX he with pre | wk
    · obtain ⟨σ, bar, -⟩ := Prologue.Export.preload_dest hp hX he pre
      exact ⟨σ, bar⟩
    · obtain ⟨σ, bar, -⟩ := Loader.Export.copy_dest hp hX hf he wk
      exact ⟨σ, bar⟩
  have hm : s.mbar = KV.Ring.ready.obj L c σ := by rw [bar0, hcg]; rfl
  obtain ⟨pcx, hl⟩ := hx _ hy cy
  rw [List.getLast?_eq_getElem?] at hl
  have polls := Mma.Export.exited_polls hp hX hf (fun h => Protocol.Shared.role_bytes hp hX h) hu wy
    (show X.get (KV.leader L X c 7, (X.tr (KV.leader L X c 7)).length - 1) = _ from hl)
  rw [cy] at polls
  have whole : pollRound 2462 ((X.tr (KV.leader L X c 7)).take
      ((X.tr (KV.leader L X c 7)).length - 1)) ≤ pollRound 2462 (X.tr (KV.leader L X c 7)) :=
    (List.take_sublist _ _).countP_le
  have total := ready_visits rows hy wy cy σ
  have H := KV.ready_slot hp hX hf rows init hc σ
  have pre3 : Iface.preloadCount Q L c ≤ 3 := Nat.min_le_left ..
  have preb : Iface.preloadCount Q L c ≤ Lib.blocksOf Q L c := by
    exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  have σlt := σ.isLt
  have use : SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (g, k) <
      okPolls (KV.Ring.ready.obj L c σ) (X.tr (KV.leader L X c 7)) := by
    rw [total]
    rcases H.issue he hm with ⟨hcp, -⟩ | ⟨hδ, i, hi⟩
    · have warp6 : g % L.block / 32 = 6 := by
        rw [show g = KV.leader L X c 6 from hcp]; exact w6
      obtain ⟨site, pos, cnt, hσ⟩ := Loader.Export.copy_count hp hX hf he warp6 bar0
      have blk := Loader.Export.copy_block hp hX hf he site
      have idx := Iface.copyIndex_lt site
      rw [hcg] at cnt hσ blk
      rw [hm] at cnt
      have cu : SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (g, k) ≤
          ((X.tr g).take k).countP (issuesTo (KV.Ring.ready.obj L c σ)) / 8 +
            KV.preload Q L c σ := by
        unfold SingleTmaRing.copyUse
        split_ifs
        · exact Nat.zero_le _
        · exact le_rfl
      refine lt_of_le_of_lt cu ?_
      rw [cnt]
      simp only [Iface.ringVisits, KV.preload] at *
      by_cases hs : σ.val < Iface.preloadCount Q L c <;> simp only [hs, ite_true, ite_false] <;>
        omega
    · have zero : SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (g, k) = 0 := by
        simp [SingleTmaRing.copyUse, hδ, hi]
      have one : KV.preload Q L c σ = 1 := hδ
      rw [zero]
      simp only [KV.preload] at one
      split_ifs at one; omega
  obtain ⟨pcw, p, acq, sc, get, cnt⟩ := MbarRing.Poll.nth_spec (X := X)
    (m := KV.Ring.ready.obj L c σ) (g := KV.leader L X c 7) use
  obtain ⟨n, m', hn, hw⟩ := SingleTmaRing.copy_observed hX KV.slot_fits H he hm get cnt
  obtain ⟨rfl, o, a', -, ⟨pc', hi'⟩, hmb, -⟩ :
      n = .async (g, k) (.notify .load) ∧ NotifyOn X (g, k) .load m' := hn
  rw [he] at hi'
  obtain ⟨-, rfl⟩ := Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj hi'))
  exact ⟨KV.leader L X c 7, _, true, sc, cy, hmb ▸ hw⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life

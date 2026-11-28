-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Pred
import Lemmas.Kernel.UbLast
import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # The proxy fence before a raw release

A dequant lane's arrival on `rawFree s` (site `arrF`, pc 3599) is its event two after its proxy
fence `fence.proxy.async.shared::cta` (site `fpx`, pc 3595), with its arrival on `dequantReady`
(site `arrD`) between (`dequant_freeFence`): the state before an `arrF` state is an `arrD` state
and the one before an `arrD` state an `fpx` state (`succ_site`), and a warpgroup-2 state past the
set-up follows a warpgroup-2 state (`deq_pred`: the startup enters the role at its first site).
The raw ring's reuse order (`Protocol/Shared/Raw.lean`) takes the fence between a lane's raw
reads of a block and its release of the block's slot. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- No load or store steps to an arrival. -/
private theorem next_ne :
    (∀ r s, Dequant.Control.rawNext r s ≠ .arrF ∧ Dequant.Control.rawNext r s ≠ .arrD) ∧
    ∀ r s, Dequant.Control.storeNext r s ≠ .arrF ∧ Dequant.Control.storeNext r s ≠ .arrD := by
  decide

/-- The sites before `arrF` and `arrD`. -/
private theorem succ_site {d' d : Dequant.Control.D} {f : Event}
    (h : Dequant.Control.succ P L g d' f = some (some d)) :
    (d.site = .arrF → d'.site = .arrD) ∧ (d.site = .arrD → d'.site = .fpx) := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d'
  have key : d.site ≠ .arrF ∧ d.site ≠ .arrD →
      (d.site = .arrF → site = .arrD) ∧ (d.site = .arrD → site = .fpx) :=
    fun ⟨h1, h2⟩ => ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  cases site
  case fpx => simp only [Dequant.Control.succ, Option.some.injEq] at h; subst h; simp
  case arrD => simp only [Dequant.Control.succ, Option.some.injEq] at h; subst h; simp
  all_goals
    apply key
    simp only [Dequant.Control.succ, Dequant.Control.poll, Dequant.Control.dataRd,
      Dequant.Control.afterSmr, Dequant.Control.afterA, Dequant.Control.loopEntry,
      Dequant.Control.advance, Dequant.Control.scaleNext, Code.ncNext] at h
    repeat' split at h
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst h
    all_goals first | exact next_ne.1 _ _ | exact next_ne.2 _ _ | (constructor <;> simp)

/-- **The fence before a raw release**: a dequant lane's arrival on `rawFree s` at index `ia` is
two events after its proxy fence `fence.proxy.async.shared::cta`, with an arrival between. -/
theorem dequant_freeFence (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {ia pc tx cnt c : Nat} {s : Fin 2} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (he : X.get (g, ia) = some ⟨pc, .arrive (mbarLoc L c (.rawFree s)) tx cnt rel sc⟩) :
    ∃ jf, ia = jf + 2 ∧ X.IsProxyFence (g, jf) (.async (some (.shared .cta))) none ∧
      ∃ pc' l' tx' cnt' rel' sc',
        X.get (g, jf + 1) = some ⟨pc', .arrive l' tx' cnt' rel' sc'⟩ := by
  have hg := Frame.lt_of_get hX he
  have hin := wg2_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩)))
  simp only [Dequant.inRole, decide_eq_true_eq] at hin
  have hub : ∀ fl, Kind.arrive (mbarLoc L c (.rawFree s)) tx cnt rel sc ≠ .ub fl :=
    fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc
    ⟨hin.1, Nat.lt_succ_of_le hin.2⟩
  have hsF : d.site = .arrF := by
    obtain ⟨site, el, ac, l0, l1, cnt', sb, pb⟩ := d
    cases site with
    | arrF => rfl
    | arrD =>
      simp only [Dequant.EvK, Kind.arrive.injEq] at hk
      have h1 := hk.1.trans (Dequant.ready_loc hp sb)
      simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff] at h1
      cases MbarFam.off_inj h1.2.2
    | lenA | lenB | wq | wraw | wsv | scale _ | raw _ _ | store _ _ =>
      simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv] at hk
    | smr | fpx | bar | exit => simp [Dequant.EvK] at hk
  obtain ⟨i, rfl⟩ := deq_pred_index hσ
  obtain ⟨f1, hf1, -⟩ := deq_earlier_ev hX he (Nat.lt_succ_self i)
  obtain ⟨d1, n1, hs1, hn1⟩ := deq_pred hFw hg hf1 hσ (by rw [hsF]; decide)
  have hsD := (succ_site hn1).1 hsF
  obtain ⟨jf, rfl⟩ := deq_pred_index hs1
  obtain ⟨f2, hf2, hub2⟩ := deq_earlier_ev hX he (by omega : jf < jf + 1 + 1)
  obtain ⟨d2, n2, hs2, hn2⟩ := deq_pred hFw hg hf2 hs1 (by rw [hsD]; decide)
  have hsP := (succ_site hn2).2 hsD
  obtain ⟨f1', hf1', hub1⟩ := deq_earlier_ev hX he (Nat.lt_succ_self (jf + 1))
  rw [hf1] at hf1'
  cases hf1'
  obtain ⟨-, hk1⟩ := deq_ev hp hX hFw hf1 hub1 hs1
  obtain ⟨-, hk2⟩ := deq_ev hp hX hFw hf2 hub2 hs2
  obtain ⟨site1, el1, ac1, l01, l11, c1, sb1, pb1⟩ := d1
  obtain ⟨site2, el2, ac2, l02, l12, c2, sb2, pb2⟩ := d2
  simp only at hsD hsP
  subst hsD hsP
  simp only [Dequant.EvK] at hk1 hk2
  obtain ⟨pc1, k1⟩ := f1
  obtain ⟨pc2, k2⟩ := f2
  simp only at hk1 hk2
  subst hk1 hk2
  exact ⟨jf, rfl, ⟨pc2, hf2⟩, pc1, _, _, _, _, _, hf1⟩

/-- **The fence before a dequantized-ready release**: a dequant lane's arrival on
`dequantReady s` at index `ia` is the event after its proxy fence
`fence.proxy.async.shared::cta`. -/
theorem dequant_readyFence (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {ia pc tx cnt c : Nat} {s : Fin 2} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (he : X.get (g, ia) = some ⟨pc, .arrive (mbarLoc L c (.dequantReady s)) tx cnt rel sc⟩) :
    ∃ jf, ia = jf + 1 ∧ X.IsProxyFence (g, jf) (.async (some (.shared .cta))) none := by
  have hg := Frame.lt_of_get hX he
  have hin := wg2_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩)))
  simp only [Dequant.inRole, decide_eq_true_eq] at hin
  have hub : ∀ fl, Kind.arrive (mbarLoc L c (.dequantReady s)) tx cnt rel sc ≠ .ub fl :=
    fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc
    ⟨hin.1, Nat.lt_succ_of_le hin.2⟩
  have hsD : d.site = .arrD := by
    obtain ⟨site, el, ac, l0, l1, cnt', sb, pb⟩ := d
    cases site with
    | arrD => rfl
    | arrF =>
      simp only [Dequant.EvK, Kind.arrive.injEq] at hk
      have h1 := hk.1.trans (Dequant.free_loc hp sb)
      simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff] at h1
      cases MbarFam.off_inj h1.2.2
    | lenA | lenB | wq | wraw | wsv | scale _ | raw _ _ | store _ _ =>
      simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv] at hk
    | smr | fpx | bar | exit => simp [Dequant.EvK] at hk
  obtain ⟨i, rfl⟩ := deq_pred_index hσ
  obtain ⟨f1, hf1, hub1⟩ := deq_earlier_ev hX he (Nat.lt_succ_self i)
  obtain ⟨d1, n1, hs1, hn1⟩ := deq_pred hFw hg hf1 hσ (by rw [hsD]; decide)
  have hsP := (succ_site hn1).2 hsD
  obtain ⟨-, hk1⟩ := deq_ev hp hX hFw hf1 hub1 hs1
  obtain ⟨site1, el1, ac1, l01, l11, c1, sb1, pb1⟩ := d1
  simp only at hsP
  subst hsP
  simp only [Dequant.EvK] at hk1
  obtain ⟨pc1, k1⟩ := f1
  simp only at hk1
  subst hk1
  exact ⟨i, rfl, ⟨pc1, hf1⟩⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

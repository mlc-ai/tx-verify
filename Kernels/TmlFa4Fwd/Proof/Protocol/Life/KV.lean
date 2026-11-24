-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Exit
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Lemmas.Flow.NthEv
import Lemmas.Kernel.SharedLifetime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The K/V ring's asynchronous uses end before their CTA's exit

At its exit a loader lane has polled each empty slot once more than it has arrived on the full slot
(the drain, `ld_exit`). So for an arrive-on of use `u` the poll of use `u + 1` of the empty slot
observes the release of use `u` by the MMA lane `c`, which follows `c`'s poll of the full slot of
use `u` (`kv_use_polled`): that poll observes the arrive-ons of the use (`arrives_finished`), whose
tracked copies have written (`rows_finished`), and the drain's poll the release
(`kv_empty_finished`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A use of the ring that a loader lane of an exited CTA has published**: the lane of warp 12
that releases the slot has polled its full barrier for the use and released it, and the loader
lane's drain observes the release. -/
theorem kv_use_polled (hg : g < L.threads) (hx : CtaExited L X (g / L.block)) (s : Fin 3)
    {y u : Nat} (hy : LdLane L g y)
    (hu : u + 1 ≤ (X.tr y).countP (arriveOnTo (kvF L g s))) : ∃ c, MmaIn L g c ∧
    (∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (kvE L g s) →
        i.1 = c) ∧
    (∃ j pc par acq sc, X.get (c, j) = some ⟨pc, .wait (kvF L g s) par true acq sc⟩ ∧
      ∀ z, LdLane L g z → ∃ i pci, X.get (z, i) = some ⟨pci, .asyncArrive (kvF L g s) true⟩ ∧
        ((X.tr z).take i).countP (arriveOnTo (kvF L g s)) = u ∧
        X.async.arrived (z, i) = true ∧
        WaitObserves X (.async (z, i) .arriveOn) (c, j) (kvF L g s) acq sc) ∧
    ∃ j pc par acq sc, X.get (y, j) = some ⟨pc, .wait (kvE L g s) par true acq sc⟩ ∧
      ∃ i pci sp rank, X.get (c, i) = some ⟨pci, .tc (.commit sp)⟩ ∧ sp.mbar = kvE L g s ∧
        ((X.tr c).take i).countP (commitsTo (kvE L g s)) = u ∧
        WaitObserves X (.async (c, i) (.tcNotify rank)) (y, j) (kvE L g s) acq sc := by
  obtain ⟨hyc, hyw⟩ := id hy
  have hyl := thread_lt_of_cta hg hyc
  obtain ⟨pcx, hxy⟩ := exit_of_exited hx hyl hyc
  obtain ⟨A, hpoll, -, -⟩ := ld_exit hp hX hFw hyw hxy
  have hps := hpoll s
  rw [obj_cta hyc, obj_cta hyc] at hps
  have hlast : (X.tr y).countP (arriveOnTo (kvF L g s)) =
      ((X.tr y).take ((X.tr y).length - 1)).countP (arriveOnTo (kvF L g s)) := by
    have hl : (X.tr y).length - 1 < (X.tr y).length := (List.getElem?_eq_some_iff.mp hxy).1
    conv_lhs => rw [← List.take_length (l := X.tr y),
      show (X.tr y).length = (X.tr y).length - 1 + 1 by omega, List.take_add_one]
    have hxy' : (X.tr y)[(X.tr y).length - 1]? = some ⟨pcx, .exit⟩ := hxy
    rw [hxy', Option.toList_some, List.countP_append]
    simp [arriveOnTo]
  obtain ⟨j, pc, par, acq, sc, hj, hje, hjn⟩ := nth_poll (X := X) (g := y)
    (k := (X.tr y).length - 1) (l := kvE L g s) (n := u + 1) (by
      change u + 1 + 1 ≤ okPolls (obj L g (56 + 8 * s.val)) _
      rw [hps]
      change u + 1 ≤ _ at hu
      have : ((X.tr y).take ((X.tr y).length - 1)).countP
          (arriveOnTo (obj L g (32 + 8 * s.val))) =
            (X.tr y).countP (arriveOnTo (kvF L g s)) := hlast.symm
      omega)
  obtain ⟨c, hc, hcm, -, hfull, hempty⟩ := kvHandoff hp hX hFw g hg s
  obtain ⟨i, pci, sp, rank, hie, hmb, hcnt, hpl, hob, -⟩ := hempty hy hje hjn
  obtain ⟨j', pc', par', acq', sc', hj', hje', hjn'⟩ := nth_poll (X := X) (g := c) (k := i)
    (l := kvF L g s) (n := u) hpl
  refine ⟨c, hc, fun h1 h2 => hcm h1 h2, ⟨j', pc', par', acq', sc', hje', fun z hz => ?_⟩,
    j, pc, par, acq, sc, hje, i, pci, sp, rank, hie, hmb, hcnt, hob⟩
  obtain ⟨a, rfl⟩ := ldLane_prod hz
  obtain ⟨i', pci', h1, h2, h3, h4⟩ := hfull hje' hjn' a
  exact ⟨i', pci', h1, h2, h3, h4⟩

/-- **The K/V rings' arrive-ons end before their CTA's exit.** -/
theorem arrives_finished : ArrivesFinished L kernel Assumptions.all X := by
  rintro ⟨h, k⟩ l noinc ⟨pc, he⟩ hpres hx
  have hni : ∀ c, (⟨pc, .asyncArrive l noinc⟩ : Event).kind ≠ .mbInit l c := fun _ h => by cases h
  have hm : Frame.MbarOf ⟨pc, .asyncArrive l noinc⟩ l := rfl
  have hg := Frame.lt_of_get hX he
  have h16 := Prologue.warpIndex_lt hp h
  obtain ⟨hw, s, rfl, rfl⟩ : (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) ∧
      ∃ s : Fin 3, l = obj L h (32 + 8 * s.val) ∧ noinc = true := by
    rcases show Prologue.warpIndex L h < 8 ∨
        (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) ∨ Prologue.warpIndex L h = 12 ∨
        Prologue.warpIndex L h = 13 ∨
        (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) by omega with
      hw | hw | hw | hw | hw
    · rcases soft_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
    · rcases corr_mbar_use hp hX hFw hw.1 hw.2 he hm hni with ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;>
        cases hk
    · rcases mma_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk, _⟩ <;>
        cases hk
    · rcases epi_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, hk, _⟩ | ⟨_, _, hk, _⟩ <;> cases hk
    · rcases ld_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, _, _, hk⟩ | ⟨o, ho, hl, hk⟩ |
        ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, _, hk, _⟩ <;> cases hk
      rcases ho with rfl | rfl | rfl
      · exact ⟨hw, 0, hl, rfl⟩
      · exact ⟨hw, 1, hl, rfl⟩
      · exact ⟨hw, 2, hl, rfl⟩
  have hy : LdLane L h h := ⟨rfl, hw⟩
  have hsu : arriveOnTo (kvF L h s) ⟨pc, .asyncArrive (obj L h (32 + 8 * s.val)) true⟩ = true := by
    simp [arriveOnTo]
  have hu : ((X.tr h).take k).countP (arriveOnTo (kvF L h s)) + 1 ≤
      (X.tr h).countP (arriveOnTo (kvF L h s)) := by
    rw [← countP_take_succ (p := arriveOnTo (kvF L h s)) he hsu]
    exact (List.take_sublist _ _).countP_le
  obtain ⟨c, hc, -, ⟨j, pcj, par, acq, sc, hje, hall⟩, -⟩ := kv_use_polled hp hX hFw hg hx s hy hu
  obtain ⟨i, pci, hie, hcnt, harr, hob⟩ := hall h hy
  obtain rfl := nthEv_unique (p := arriveOnTo (kvF L h s)) hie (by simp [arriveOnTo]) he hsu hcnt
  exact of_observed hX harr hc.1 hc.2.1 hje hob hx

/-- **The K/V row copies end before their CTA's exit.** -/
theorem rows_finished : RowsFinished L kernel Assumptions.all X := by
  rintro ⟨h, k⟩ sp ⟨pc, he⟩ hx
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, hC⟩ : (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) ∧
      LdCp L X h k sp := by
    rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨sp', hk, hw, h⟩ |
      ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
    exact ⟨hw, h⟩
  simp only at hx ⊢
  obtain ⟨pcx, hxh⟩ := exit_of_exited hx hg rfl
  obtain ⟨hkx, hl⟩ := before_exit he (by simp) hxh
  obtain ⟨A, -, hcnt, hcp, -⟩ := ld_exit hp hX hFw hw hxh
  -- the packet's arrive-on is made
  have hA : pkt X h k < A := by
    have h1 : ((X.tr h).take k).countP cpCopy + 1 ≤
        ((X.tr h).take ((X.tr h).length - 1)).countP cpCopy := by
      rw [← countP_take_succ (p := cpCopy) he rfl]
      exact countP_take_mono _ _ (by omega)
    unfold pkt
    omega
  set t := pkt X h k
  have hge := hcnt t hA
  let s : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  have hy : LdLane L h h := ⟨rfl, hw⟩
  have hu : t / 3 + 1 ≤ (X.tr h).countP (arriveOnTo (kvF L h s)) :=
    hge.trans (List.take_sublist _ _).countP_le
  obtain ⟨c, hc, -, ⟨j, pcj, par, acq, sc, hje, hall⟩, -⟩ := kv_use_polled hp hX hFw hg hx s hy hu
  obtain ⟨i, pci, hie, hcnt', harr, hob⟩ := hall h hy
  have hki : k < i := by
    rcases lt_trichotomy i k with h1 | h1 | h1
    · exfalso
      have h2 := countP_take_succ (p := arriveOnTo (kvF L h s)) hie (by simp [arriveOnTo])
      have h3 := countP_take_mono (arriveOnTo (kvF L h s)) (X.tr h) (show i + 1 ≤ k by omega)
      have h4 := hC.arrs
      change ((X.tr h).take k).countP (arriveOnTo (kvF L h s)) = t / 3 at h4
      omega
    · subst h1; rw [he] at hie; cases hie
    · exact h1
  have ht : TracksCpAsync X (h, k) (h, i) :=
    ⟨rfl, hki, ⟨sp, ⟨_, he⟩, hC.grp⟩, _, true, ⟨_, hie⟩⟩
  obtain ⟨-, -, -, harrOk⟩ := hX.tma
  have hwr : (X.async.copies (h, k)).writeBytes.isSome := (harrOk (h, i) harr).2 _ ht
  have hfin := of_observed hX (i := (h, i)) (q := .arriveOn) (c := h / L.block) harr hc.1 hc.2.1
    hje hob hx
  exact SharedFinished.of_stage (j := (h, i)) (q := .arriveOn) hwr
    (.inr ⟨rfl, rfl, ht, hwr, harr⟩) hfin

/-- **A K/V release's arrive-on ends before its CTA's exit.** -/
theorem kv_empty_finished {h k pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16} (s : Fin 3)
    (he : X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp rank = some (kvE L h s)) (hx : CtaExited L X (h / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async (h, k) (.tcNotify rank)) (h / L.block) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, -, hw, hmb, -⟩ := mma_commit_of hp hX hFw he ht
  have hcu := mma_kv_commit hp hX hFw s hw he hmb
  set u := ((X.tr h).take k).countP (commitsTo (obj L h (56 + 8 * s.val))) with hudef
  -- the lane polled the full slot for the use, so a loader lane arrived
  obtain ⟨j, pcj, par, acq, sc, -, hje, hjn⟩ := nth_poll (X := X) (g := h) (k := k)
    (l := kvF L h s) (n := u) hcu
  obtain ⟨c, hc, hcm, -, hfull, -⟩ := kvHandoff hp hX hFw h hg s
  obtain rfl : h = c := hcm he ht
  obtain ⟨i, pci, hie, hcnt, -⟩ := hfull hje hjn 0
  have hy : LdLane L h (ldProd L h 0) := by
    have hb := hp.block
    unfold LdLane ldProd Prologue.warpIndex
    rw [hb]
    simp only [Fin.isValue, Fin.val_zero]
    omega
  have hu : u + 1 ≤ (X.tr (ldProd L h 0)).countP (arriveOnTo (kvF L h s)) := by
    rw [← hcnt, ← countP_take_succ (p := arriveOnTo (kvF L h s)) hie (by simp [arriveOnTo])]
    exact (List.take_sublist _ _).countP_le
  obtain ⟨c, -, hcm', -, j', pc', par', acq', sc', hje', i', pci', sp', rank', hie', hmb', hcnt',
    hob⟩ := kv_use_polled hp hX hFw hg hx s hy hu
  obtain rfl : h = c := hcm' he ht
  obtain rfl := nthEv_unique (p := commitsTo (kvE L h s)) hie' (by simp [commitsTo, hmb']) he
    (by simp only [commitsTo, decide_eq_true_eq]; exact hmb) (hcnt'.trans hudef)
  obtain ⟨hr, pc2, s2, hg2, ht2⟩ := observed_notified hX hob
  rw [he] at hg2
  cases hg2
  obtain rfl : rank = rank' := target_rank ht ht2
  exact of_observed hX hr (thread_lt_of_cta hg hy.1) hy.1 hje' hob hx

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Life

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeMma
public import Lemmas.Order.GuardOrder
public import Lemmas.Order.DependencyWitness

@[expose] public section

/-!
# A tensor load finishes before its CTA exits

`Life.CopyFinished` (`IpLifeUse`): a tensor load's data writes complete before an exit of the
destination CTA, and its notification before an exit of the mbarrier's CTA. Both are of the
issuer's own CTA (`Own.tensor`, `Own.mbar`). The kernel's copies (the prologue's and the loader's)
complete on `kv_ready` of their CTA; the MMA warp polls `kv_ready` for every block it processes.

* `notify_finished`: a notification observed by a poll of a thread of CTA `c` that exits later is
  finished: the poll is a canonical spin, so the thread's exit resumes from it (`Resumes.of_spin`)
  and the poll is a witness of the notification;
* `copyFinished`: the notification by `notify_finished`, and each data write by the order of the
  stages of the load (the write precedes the notification, which a notified load has for every
  slot of its box, `EffectValidity`).

**Premise `CopyObserved`**: every tensor load is observed by a successful poll of its mbarrier by
a thread of the mbarrier's CTA. It is the counting fact of the `kv_ready` ring: the MMA warp polls
`kv_ready (t % 3)` for every block `t < num_iters` and every copy is for such a block (the
prologue's `num_pre = min(3, num_iters)` and the loader's loop to `num_iters`), and the poll for
use `n` observes the copies of use `n` (`PairTmaRing.copy_observed`, here `Kv.Hyp`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every tensor load whose mbarrier's CTA exited is observed by a poll of its mbarrier**, by a
launched thread of that CTA. It is stated for an exited CTA: before the exit the poll may not have
happened yet (an execution is a prefix of a run), and the only use of the premise is the finish of
the load before an exit. -/
def CopyObserved (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {s : TensorCopy.Spec}, X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ →
    CtaExited L X s.mbar.cta →
    ∃ h j acq ws, h < L.threads ∧ h / L.block = s.mbar.cta ∧
      X.AsyncPresent (g, k) (.notify .load) ∧
      WaitObserves X (.async (g, k) (.notify .load)) (h, j) s.mbar acq ws

/-- **An arrive-on or notification observed by a spinning poll of a thread of CTA `c`, before that
thread's exit, is finished.** -/
theorem notify_finished (hX : Consistent L kernel asms mem0 X) {i w : EvId} {p : Part}
    {m : Loc} {acq : Bool} {ws : MbarScope} {c kx pcx : Nat}
    (hp : X.AsyncPresent i p) (hwo : WaitObserves X (.async i p) w m acq ws)
    (hw1 : w.1 < L.threads) (hwc : w.1 / L.block = c)
    (hk : X.get (w.1, kx) = some ⟨pcx, .exit⟩) (hwk : w.2 < kx) :
    SharedFinished L kernel asms X (.async i p) c := by
  obtain ⟨pc, q, hget⟩ := hwo.1
  have hobs : Witness L X (.async i p) w :=
    Witness.of_mbarObserved (mbarObserved_of_waitObserves hX.tma.2.2.1 hp hwo)
  obtain ⟨ex, hsp⟩ := poll_spins hX hget
  exact SharedFinished.of_observer_exit (finish := (w.1, kx)) hp hobs
    (Resumes.of_spin hget hsp rfl hwk (len_of_get hk)) ⟨hw1, hwc, pcx, hk⟩

/-- A poll of a thread of an exited CTA is followed by the thread's exit. -/
theorem exit_after_poll {w : EvId} {ev : Event} {c : Nat}
    (hx : CtaExited L X c) (hw1 : w.1 < L.threads) (hwc : w.1 / L.block = c)
    (hev : X.get w = some ev) (hne : ∀ pc, ev ≠ ⟨pc, .exit⟩) :
    ∃ kx pcx, X.get (w.1, kx) = some ⟨pcx, .exit⟩ ∧ w.2 < kx := by
  obtain ⟨pc, hl⟩ := hx w.1 hw1 hwc
  rw [List.getLast?_eq_getElem?] at hl
  have hlen : w.2 < (X.tr w.1).length := len_of_get hev
  refine ⟨(X.tr w.1).length - 1, pc, hl, ?_⟩
  rcases Nat.lt_or_ge w.2 ((X.tr w.1).length - 1) with h | h
  · exact h
  · have heq : w.2 = (X.tr w.1).length - 1 := by omega
    have : X.get w = some ⟨pc, .exit⟩ := by
      show (X.tr w.1)[w.2]? = _
      rw [heq]
      exact hl
    rw [hev] at this
    exact absurd (Option.some.inj this) (hne pc)

/-- **`CopyFinished`** from the observation of every load. -/
theorem copyFinished (hX : Consistent L kernel asms mem0 X) (own : Own L X)
    (hobs : CopyObserved L X) : CopyFinished L X := by
  rintro ⟨g, k⟩ a s ⟨pc, he⟩
  have hmc : s.mbar.cta = g / L.block := own.mbar (Execution.UsesMbar.of_tensor ⟨pc, he⟩)
  have hbase : s.sharedBase.cta = g / L.block := own.tensor he
  have notify : ∀ c, CtaExited L X c → c = s.mbar.cta →
      SharedFinished L kernel asms X (.async (g, k) (.notify .load)) c := by
    intro c hex hc
    obtain ⟨h, j, acq, ws, hh, hhc, hp, hwo⟩ := hobs he (hc ▸ hex)
    obtain ⟨pcw, q, hget⟩ := hwo.1
    obtain ⟨kx, pcx, hk, hlt⟩ := exit_after_poll hex hh (hhc.trans hc.symm) hget
      (fun _ h => by cases h)
    exact notify_finished hX hp hwo hh (hhc.trans hc.symm) hk hlt
  refine ⟨fun x y kk hsl hex => ?_, fun hex => ?_⟩
  · have hfin := notify s.sharedBase.cta hex (by rw [hbase, hmc])
    obtain ⟨h, j, acq, ws, hh, hhc, hp, hwo⟩ := hobs he (by rw [hmc, ← hbase]; exact hex)
    obtain ⟨o, hto, hnot⟩ := hp
    obtain ⟨⟨al', pco, hti⟩, -⟩ := hX.tensor (g, k) o hto
    have hspec : o.spec = s := by
      rw [hti] at he
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he
      exact he.2.2
    subst hspec
    obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsl
    have hnot' : o.effects.notified = true := hnot
    obtain ⟨v, hv⟩ := (hX.effectValidity.tensor (g, k) o hto).2.1.complete hnot' slot
    have hwp : X.AsyncPresent (g, k) (.write (.load x y kk)) := ⟨o, slot, v, hto, hslot, hv⟩
    exact SharedFinished.of_stage (j := (g, k)) (q := .notify .load) hwp
      (.inr ⟨rfl, rfl, rfl, rfl, hwp, o, hto, hnot'⟩) hfin
  · exact notify _ hex rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Life

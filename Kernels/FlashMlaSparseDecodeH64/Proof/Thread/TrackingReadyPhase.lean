-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingObservedArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins
import Lemmas.MBarrier.MBarrierRound
import Lemmas.Tensor.TensorTransfer

@[expose] public section

/-! # Actual producer records of the TMA ready phase -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A successful arrival in the observed ready generation is a unit release of warp 7. -/
theorem ready_phase_arrive {g i q tag idx k phase n tx : Nat} {e : Event}
    {slot : Fin 4} {parity : Nat} {r w : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hRead : X.get (g, i) = some e) (hq : q < i)
    (hPrior : ∀ p, baseCausality L X p (g, i) → ¬ Dismisses P L X p)
    (hWait : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) slot) parity true true .cta⟩)
    (hwId : w.id = .thread (g, q)) (hwClean : w.fault = none)
    (hwReply : w.reply.waited = some true)
    (hk : k < idx)
    (hr : (X.objects (ready L (ctaOf L g) slot))[k]? = some r)
    (hw : (X.objects (ready L (ctaOf L g) slot))[idx]? = some w)
    (hphase : phaseAt (X.objects (ready L (ctaOf L g) slot)) k = some phase)
    (hobs : observedAt (X.objects (ready L (ctaOf L g) slot)) idx = some phase)
    (hClean : r.fault = none) (hAct : r.action = .arrive n tx) :
    ∃ h j, r.id = .thread (h, j) ∧
      AtIndex P L X (ctaOf L g) slot h j (fun s => ∃ extra, s = .ready extra) ∧ n = 1 ∧ tx = 0 := by
  let m := ready L (ctaOf L g) slot
  have hmem := List.mem_of_getElem? hr
  cases record_source hX.tma.2.2.1 hmem with
  | @arrive h j _ a b _ _ hid he hact =>
    have hObserve : WaitObserves X (.thread (h, j)) (g, q) m true .cta :=
      ⟨⟨tag, parity, hWait⟩, k, idx, r, w, phase, hr, hid, hClean, hw, hwId, hwClean,
        hwReply, hk, hphase, hobs, (objects_single_lifetime hX m).sameLifetime k idx⟩
    obtain ⟨hsite, htx, hn, _, _⟩ :=
      observed_ready_source hpre hX hs hRead hq he rfl hObserve hPrior
    obtain ⟨hCount, hTx⟩ := Action.arrive.inj (hAct.symm.trans hact)
    exact ⟨h, j, hid, hsite, hCount.trans hn, hTx.trans htx⟩
  | commit _ he hTarget _ => exact (no_ready_commit hpre hX hs he rfl hTarget).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | init _ _ ha | inval _ _ ha | wait _ _ ha | tensor _ _ _ ha | bulk _ _ _ _ ha
  | clc _ _ _ _ ha =>
    rw [hAct] at ha
    cases ha

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

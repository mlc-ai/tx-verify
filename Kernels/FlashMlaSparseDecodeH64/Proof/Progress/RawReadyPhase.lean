-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressRawPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Completion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingItems
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarRawReadyFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.MbarRingBlocker
import Lemmas.Protocol.UnitReachBlocker

public section

/-! # Once the raw gathers have issued, a dequantizer can acquire their slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing Protocol RawRing
open PTX.MBarrier hiding okPolls

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem raw_completed_ge {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    (X.tr issuer).countP (issuesTo (ready L cta slot)) ≤
      completedTxCount (X.objects (ready L cta slot)) := by
  let m := ready L cta slot
  let id (i : Nat) := Ref.async (issuer, i) (.notify .load)
  unfold completedTxCount
  apply countP_le_of_records id (fun i j _ _ he => by
    exact congrArg (fun ref : Ref => ref.issuer.2) he)
  intro i hi
  obtain ⟨⟨tag, kind⟩, hGet, hOp⟩ := (mem_indicesP_iff _ _ i).mp hi
  cases hk : kind <;> simp [issuesTo, hk] at hOp
  rename_i addr sp
  have he : X.get (issuer, i) = some ⟨tag, .tensorIssue addr sp⟩ := by
    rw [← hk]
    exact hGet
  obtain ⟨o, ho, hNote⟩ := tensor_loads_drained hpre hmax hs ht ⟨tag, he⟩
  have hAct : objectAction X X.async m (id i) = some (.completeTx
      (TensorTransfer.bytes sp.descriptor)) := by
    simp [id, objectAction, he, ho, hNote, hOp, m]
  obtain ⟨r, hr, hid⟩ := (hmax.1.tma.2.2.1 m).2.2 _ _ hAct
  have hAction := ((hmax.1.tma.2.2.1 m).2.1 r hr).1
  rw [hid, hAct] at hAction
  have hClean := Safety.raw_ready_fault_free hpre hmax.1 (fun k hk => (hs k hk).machine) ht r hr
  exact ⟨r, hr, hid, by simp [(Option.some.inj hAction).symm, hClean]⟩

private theorem raw_arrivals_ge {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    arrivals (ready L cta slot) (X.tr issuer) ≤ arrivalUnits (X.objects (ready L cta slot)) := by
  let m := ready L cta slot
  have hClean := Safety.raw_ready_fault_free (cta := cta) (slot := slot) hpre hX hs ht
  apply (Unit.arrivals_le_unitRec hX hClean issuer).trans
  rw [arrivalUnits_eq_length (fun r hr c tx _ ha =>
        (ready_arrival_record hpre hX hs ht hr ha).1),
    ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro r _ hr
  obtain ⟨⟨_, hOk⟩, hAct⟩ := by
    simpa only [Unit.unitRec, Bool.and_eq_true, Option.isNone_iff_eq_none] using hr
  apply countedArrive_iff.mpr
  refine ⟨hOk, ?_⟩
  cases h : r.action <;> simp [h] at hAct
  rename_i c tx
  exact ⟨c, tx, rfl⟩

private theorem raw_arrivals_le {cta issuer g : Nat} {slot : Fin 2} {n : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hIssuer : Issuer P L X cta issuer)
    {lane : Fin 128} (hLane : g = consumer L cta lane)
    (hCount : okPolls (ready L cta slot) (X.tr g) = n) :
    arrivalUnits (X.objects (ready L cta slot)) ≤ n + 1 := by
  classical
  let m := ready L cta slot
  let log := X.objects m
  let R := items (slot := slot) issuer hpre hX hs ht hIssuer
  let T : Finset (Unit × Nat) := Finset.univ ×ˢ Finset.range (n + 1)
  have hu := Round.units_le_of_uses (X.objects_checked hX m)
    (fun x : Unit × Nat => itemFull X m issuer 0 x.2) T (i := log.length)
    (fun k r c tx hk _ ha =>
      (ready_arrival_record hpre hX hs ht (List.mem_of_getElem? hk) ha).1)
    (fun k _ r c tx hk hOk ha => ?_)
  · change unitsBefore log log.length ≤ T.card at hu
    simpa [unitsBefore, List.take_length, T] using hu
  obtain ⟨x, hx, hid, hKind⟩ :=
    Safety.raw_ready_item_of_record hpre hX hs ht hIssuer (List.mem_of_getElem? hk) hOk
      (.inl ⟨c, tx, ha⟩)
  have hItem : x.1 = 0 := by
    unfold actionFull at hKind
    split at hKind
    · exact Fin.ext (by assumption)
    · rw [ha] at hKind
      cases hKind
  have hGen : x.2 < n + 1 := by
    by_contra! hgt
    have hPath := (R.reach hX.depAcyclic).1 0 x hx lane n (by omega)
    have hSeen := Poll.nth_present.mp (Unit.present_of_path hPath)
    change n < okPolls m (X.tr (consumer L cta lane)) at hSeen
    rw [← hLane, hCount] at hSeen
    omega
  rw [hItem] at hid
  exact ⟨((), x.2), by simpa [T] using (Nat.lt_succ_iff.mp hGen), hid⟩

/-- Once the current block's expectation and all gather issues are present, maximality has
drained those issues. A released dequantizer then takes the successful raw-ready poll. -/
theorem no_pending_raw_ready_of_published {g issuer : Nat} {d : Wg2.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.wg2 d))
    (hrel : PTX.Step.Released L X g) (hd : d.site = .rawReady)
    (hIssuer : RawRing.Issuer P L X (ctaOf L g) issuer)
    (hPub : d.block / 2 + 1 ≤ arrivals (ready L (ctaOf L g) (rawSlot d.block)) (X.tr issuer))
    (hGather : 16 * (d.block / 2 + 1) ≤ (X.tr issuer).countP
      (issuesTo (ready L (ctaOf L g) (rawSlot d.block)))) : False := by
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := ready L cta slot
  let log := X.objects m
  let hSound := fun k hk => (hs k hk).machine
  have hg := hp.1.1
  have hWg : wgOf L g = 2 := RingRoleGeometry.of_trace hmax.1 hg (hSound g hg) hp.2
  obtain ⟨lane, hLane⟩ := consumer_of_wg2 hpre (show ctaOf L g = cta from rfl) hWg
  have hCount := Wg2RawTrace.composed_raw_ready_count hpre
    ((hSound g hg).produces (hmax.1.thr g hg)) hp.2 hd
  rw [List.take_length] at hCount
  change okPolls m (X.tr g) = _ at hCount
  obtain ⟨_, hRun⟩ := Frame.run_some hmax.1 hub hp.1
  obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hg hRun hp.2
  change Wg2.Inv P L g d at hi
  obtain ⟨_, hInit⟩ := MachineTracking.table_init_of_followed_tail hpre hmax.1 hs hg hp.2
    (by intro s h; cases h) (RawRing.readyEntry slot)
  obtain ⟨hl, hn⟩ := RawRing.ready_entry L cta slot
  rw [hl, hn] at hInit
  obtain ⟨_, r, hr, _, _, _, _⟩ := init_record_of_consistent hmax.1 hInit
  have hNe : log ≠ [] := by
    intro h
    have hmem := List.mem_of_getElem? hr
    change r ∈ log at hmem
    rw [h] at hmem
    exact List.not_mem_nil hmem
  have hFirst := ready_init_first (slot := slot) (cta := cta) hpre hmax.1 hSound ht
  have hLife := objects_single_lifetime hmax.1 m
  obtain ⟨s, hsFinal⟩ := Unit.final_of_init hmax.1 hFirst hLife hNe
  have hA := raw_arrivals_le hpre hmax.1 hSound ht hIssuer hLane hCount
  have hA' := hPub.trans (raw_arrivals_ge hpre hmax.1 hSound ht)
  have hTx := hGather.trans (raw_completed_ge hpre hmax hs ht)
  have hMaxTx := Safety.raw_ready_completion_count_le hpre hmax.1 hSound ht hIssuer
    le_rfl hsFinal
  rw [List.take_length] at hMaxTx
  have hBytes := Safety.raw_ready_expected_bytes (cta := cta) (slot := slot) hpre hmax.1 hSound ht
    log (fun _ => id)
  have hUniform : UniformCompletedTx log 2304 :=
    fun r hr _ _ ha => (gather_record hpre hmax.1 hSound ht hr ha).1
  have hCase := Blocker.tx_short (X.objects_checked hmax.1 m) hLife hsFinal
    (PairTmaRing.expected_of_init hmax.1 hFirst hLife hsFinal)
    (show expectedTxBytes log = 16 * 2304 * arrivalUnits log by exact hBytes)
    hUniform hMaxTx (objects_no_pending_increment hmax.1 m)
  have hPhase : s.phase = d.block / 2 + 1 := by
    change arrivalUnits log ≤ _ at hA
    change _ ≤ arrivalUnits log at hA'
    change _ ≤ completedTxCount log at hTx
    change completedTxCount log ≤ 16 * (s.phase + 1) at hMaxTx
    change arrivalUnits log = s.phase ∨
      (arrivalUnits log = s.phase + 1 ∧ completedTxCount log < 16 * (s.phase + 1)) at hCase
    rcases hCase with h | ⟨h, hh⟩ <;> omega
  have hObject : DequantWait.object L g d .raw = m := by
    simp [DequantWait.object, m, cta, ctaOf, slot, rawSlot, ready, hi.bufBlock]
  have hParity : s.phase % 2 ≠ (DequantWait.parity d .raw) % 2 := by
    simp only [DequantWait.parity, hPhase, hi.parBlock, Nat.mod_mod]
    omega
  exact hmax.not_grows (dequant_poll_extension (w := .raw) hpre hs hmax.1 hub hp.1
    hrel hp.2 hd (hObject.symm ▸ hsFinal) hParity)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

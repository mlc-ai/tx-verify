-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarUnitFaults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressMmaPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarPublished
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # A blocked GEMM input wait finds a producer missing its publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow MBarrier Protocol GemmRing PTX.MbarRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

/-- The producers of the requested MMA input slot. -/
def MmaWait.producer (w : MmaWait) (L : Launch) (cta : Nat) : Fin 128 → Nat :=
  match w with
  | .dequant => GemmRing.producer L cta
  | .score => softmax L cta

private theorem input_wait_count (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {g : Nat} {d : Wg1Mma.D} {w : MmaWait} (hg : g < L.threads)
    (hd : d.site = w.site)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d))) :
    PTX.Flow.okPolls (w.object L g d) (X.tr g) = d.i / 2 := by
  have hcnt := Wg1MmaGemmTrace.composed_count_here hpre hg w.stream
    ((hs g hg).machine.produces (hX.thr g hg)) hσ (slot := rawSlot d.i) rfl
  rw [List.take_length] at hcnt
  cases w
  all_goals
    have hh := hcnt
    simp only [hd, MmaWait.site, MmaWait.stream, Wg1MmaGemmTrace.completed,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hh
    exact hh

/-- When an MMA input phase is incomplete at maximality, some producer has not published
the current block in that slot. A ready phase would extend the execution by a success poll. -/
private theorem pending_mma_wait_short_of_state (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg1Mma.D} {w : MmaWait} {before : State}
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = w.site)
    (hstate : stateBefore (X.objects (w.object L g d)) (X.objects (w.object L g d)).length =
      some before) :
    ∃ lane,
      PTX.Flow.arrivals (w.object L g d) (X.tr (w.producer L (ctaOf L g) lane)) ≤ d.i / 2 := by
  have hX := hmax.1
  let sound := fun g hg => (hs g hg).machine
  have hCount := input_wait_count hpre hX hs hp.1 hd hσ
  have hPhase : before.phase % 2 = Wg1Mma.parOf d.i % 2 := by
    by_contra hn
    exact hmax.not_grows (mma_poll_extension hpre hs hX (Safety.no_ub hpre hX hs ht)
      hp hrel hσ hd hstate hn)
  have hParity :
      before.phase % 2 = (PTX.Flow.okPolls (w.object L g d) (X.tr g) + 0) % 2 := by
    rw [hCount]
    simpa only [Wg1Mma.parOf, Nat.add_zero, Nat.mod_mod] using hPhase
  obtain ⟨issuer, hIssuer⟩ := exists_issuer (cta := ctaOf L g) hpre hX sound
  have hNe : d.site ≠ .elect := by cases w <;> simp [hd, MmaWait.site]
  have hg := hIssuer g _ d rfl hσ hNe
  subst issuer
  let slot := rawSlot d.i
  cases w with
  | dequant =>
    let R := dequantRing (slot := slot) hpre hX sound hIssuer
    let O := dequant_obj hpre hX sound (cta := ctaOf L g) (slot := slot)
    have hR : Unit.Reach L kernel Assumptions.all X (full L (ctaOf L g) slot) 128
        (GemmRing.producer L (ctaOf L g)) 0 g := by
      intro x hx j hj
      simp only [Nat.add_zero]
      exact (R.reach hX.depAcyclic).1 0 x hx 0 j hj
    have hClean := Safety.dequant_ready_fault_free hpre hX sound ht (cta := ctaOf L g)
      (slot := slot)
    obtain ⟨hExact, lane, hShort⟩ :=
      O.reach_short hX hR hClean hstate (Nat.zero_le _) hParity
    have hN : before.phase = d.i / 2 := hExact.trans hCount
    exact ⟨lane, hShort.trans hN.le⟩
  | score =>
    let R := scoreRing (slot := slot) hpre hX sound ht hIssuer
    let O := score_obj hpre hX sound ht (cta := ctaOf L g) (slot := slot)
    have hR : Unit.Reach L kernel Assumptions.all X (Object.soReady.loc L (ctaOf L g) slot)
        128 (softmax L (ctaOf L g)) 0 g := by
      intro x hx j hj
      have hj' : j + 1 ≤ x.2 := hj
      have hPath := (R.reach hX.depAcyclic).2 0 x hx (j + 1) (Nat.succ_pos j) hj'
      change Relation.TransGen (DepStep L kernel X)
        (.thread (g, Poll.nth X (Object.soReady.loc L (ctaOf L g) slot) g (j + 1 - 1)), true)
        (.thread (Unit.it X (Object.soReady.loc L (ctaOf L g) slot)
          (softmax L (ctaOf L g)) x.1 x.2), false) at hPath
      simpa only [Nat.add_zero, Nat.add_sub_cancel] using hPath
    have hClean := Safety.score_ready_fault_free hpre hX sound ht (cta := ctaOf L g)
      (slot := slot)
    obtain ⟨hExact, lane, hShort⟩ :=
      O.reach_short hX hR hClean hstate (Nat.zero_le _) hParity
    have hN : before.phase = d.i / 2 := hExact.trans hCount
    exact ⟨lane, hShort.trans hN.le⟩

private theorem mma_wait_init (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {g : Nat} {d : Wg1Mma.D} {w : MmaWait} (hg : g < L.threads)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d))) :
    ∃ i count, X.MbInit i (w.object L g d) count := by
  let slot := rawSlot d.i
  let entry (slot : Fin 2) : Fin 23 := match w with
    | .dequant => if slot.val = 0 then 3 else 9
    | .score => if slot.val = 0 then 7 else 13
  have hLoc (s : Fin 2) :
      IndexRing.initTable.loc L (ctaOf L g) (entry s) = w.stream.loc L g s := by
    cases w <;> fin_cases s <;> rfl
  obtain ⟨i, hi⟩ :=
    MachineTracking.table_init_of_followed_tail hpre hX hs hg hσ (by simp) (entry slot)
  rw [hLoc slot] at hi
  exact ⟨i, initCount (entry slot), hi⟩

/-- The reached MMA role has the actual barrier initialization. At maximality one missing
publication determines a specific producer lane. -/
theorem pending_mma_wait_short (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg1Mma.D} {w : MmaWait}
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = w.site) :
    ∃ lane,
      PTX.Flow.arrivals (w.object L g d) (X.tr (w.producer L (ctaOf L g) lane)) ≤ d.i / 2 := by
  obtain ⟨i, count, hi⟩ := mma_wait_init (w := w) hpre hmax.1 hs hp.1 hσ
  obtain ⟨r, hFirst, _, hAct, hClean⟩ := Safety.mbar_init_record_first hpre hmax.1 hs ht hi
  have hPos := (List.getElem?_eq_some_iff.mp hFirst).1
  obtain ⟨before, hState, _⟩ := ObjectInit.checked_expected_after_init
    (X.objects_checked hmax.1 (w.object L g d))
    (fun _ hr => Safety.mbar_record_not_inval hmax.1 hr) hFirst hAct hClean hPos le_rfl
  exact pending_mma_wait_short_of_state hpre hmax hs ht hp hrel hσ hd hState

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

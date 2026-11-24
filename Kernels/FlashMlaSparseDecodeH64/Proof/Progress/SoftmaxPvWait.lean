-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryMmaCandidate
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarPublished
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Lemmas.Protocol.NotifyBlocker

public section

/-! # The epilogue waits for the last PV commit, including when earlier phases were skipped -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow AsyncCopy MBarrier Protocol GemmRing PTX.MbarRing
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem pv_wait_state (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg0.D} (hg : g < L.threads)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d))) :
    let m := empty L (ctaOf L g) (rawSlot d.block)
    ∃ st, stateBefore (X.objects m) (X.objects m).length = some st := by
  let slot := rawSlot d.block
  let entry (s : Fin 2) : Fin 23 := if s.val = 0 then 8 else 14
  have hLoc (s : Fin 2) :
      IndexRing.initTable.loc L (ctaOf L g) (entry s) = empty L (ctaOf L g) s := by
    fin_cases s <;> rfl
  obtain ⟨i, hi⟩ := MachineTracking.table_init_of_followed_tail
    hpre hX hs hg hd (by simp) (entry slot)
  rw [hLoc slot] at hi
  obtain ⟨r, hFirst, _, hAct, hClean⟩ := Safety.mbar_init_record_first hpre hX hs ht hi
  have hPos := (List.getElem?_eq_some_iff.mp hFirst).1
  obtain ⟨st, hState, _⟩ := ObjectInit.checked_expected_after_init (X.objects_checked hX _)
    (fun _ hr => Safety.mbar_record_not_inval hX hr) hFirst hAct hClean hPos le_rfl
  exact ⟨st, hState⟩

/-- If a released epilogue lane remains at its PV wait, the final PV issue is missing. Every
issued Tensor Core operation and every eligible commit notification can already be completed. -/
theorem pending_softmax_pv_missing (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hsg : SyncGuarded L kernel X)
    {g : Nat} {d : Wg0.D} (hp : PendingState P L X g (.wg0 d)) (hRel : PTX.Step.Released L X g)
    (hd : d.site = .svDone) :
    let m := empty L (ctaOf L g) (rawSlot d.block)
    ∃ issuer, MmaIssuer P L X (ctaOf L g) issuer ∧
      (X.tr issuer).countP (commitsTo m) ≤ d.block / 2 := by
  have hX := hmax.1
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := empty L cta slot
  let n := d.block / 2
  let sound := fun h hh => (hs h hh).machine
  obtain ⟨st, hState⟩ := pv_wait_state hpre hX hs ht hp.1.1 hp.2
  have hHub := Safety.no_ub hpre hX hs ht
  have hParity : st.phase % 2 = n % 2 := by
    by_contra hn
    exact hmax.not_grows (softmax_gemm_poll_extension hpre hs hX hHub
      hp.1 hRel hp.2 .pv hd hState hn)
  obtain ⟨_, hRun⟩ := Frame.run_some hX hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  have hInv : Wg0.Inv P L g d := hInv
  have hLast := hInv.epilogueLast (by rw [hd]; rfl)
  obtain ⟨issuer, hIssuer⟩ := exists_issuer (cta := cta) hpre hX sound
  let O := reuse_obj (slot := slot) hpre hX sound hIssuer
  have hBound : (X.tr issuer).countP (commitsTo m) ≤ n + 1 := by
    by_contra! hLong
    obtain ⟨⟨tag, kind⟩, he, tick, hOrdinal⟩ := nthEv_spec hLong
    obtain ⟨sp, hk, hm⟩ := Notify.commit_of_commitsTo tick
    change kind = _ at hk
    subst kind
    have hTgt : TcCommit.target sp 0 = some m := by
      rw [commit_target hpre hX hs ht ⟨tag, he⟩, hm]
      rfl
    have hI := Frame.lt_of_get hX he
    obtain ⟨_, hCta, q, hSlot, hClass, hQ⟩ :=
      notification hpre hX (sound issuer hI) ht he rfl hTgt
    have hPv : q.site = .pvCommit := by
      rcases hClass with ⟨h, _⟩ | ⟨_, h⟩
      · cases h
      · exact h
    obtain ⟨_, _, _, _, hW, _, _⟩ := Frame.fired_site hs hX he hQ
    have hW : Wg1Mma.Inv P L issuer q := hW
    have hLt := hW.i_lt (by rw [hPv]; trivial)
    rw [StageAfterPv.block_count_eq (P := P) hCta] at hLt
    have hCount := Wg1MmaGemmTrace.pv_commits_before_block hpre hI slot
      ((sound issuer hI).produces (hX.thr issuer hI)) hQ
    change ((X.tr issuer).take _).countP (commitsTo (empty L (ctaOf L issuer) slot)) = _ at hCount
    rw [hCta, hOrdinal] at hCount
    change q.i % 2 = d.block % 2 at hSlot
    change n + 1 = (q.i + (1 - d.block % 2)) / 2 at hCount
    omega
  refine ⟨issuer, hIssuer, ?_⟩
  by_contra! hLong
  have hRecords (j : Nat) (hj : j < n + 1) :
      ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
        r.id = Notify.it X m issuer m j ∧ countedArrive r = true := by
    obtain ⟨⟨tag, kind⟩, he, tick, _⟩ := nthEv_spec (hj.trans_le hLong)
    obtain ⟨sp, hk, hm⟩ := Notify.commit_of_commitsTo tick
    change kind = _ at hk
    subst kind
    have hi : X.Commit (issuer, Notify.cm X issuer m j) sp := ⟨tag, he⟩
    have hTgt : TcCommit.target sp 0 = some m := by rw [commit_target hpre hX hs ht hi, hm]; rfl
    have hNotified := completed_commit_notified hpre hmax hs ht hi hTgt
      (fun _ hTrack => issued_tc_completed hpre hmax hs ht hsg hTrack.2.2.1)
    exact Notify.Obj.notified_rec_of_rank hX (Safety.sv_done_fault_free hpre hX sound ht)
      he hTgt hNotified
  have hLower := O.phase_ge_of_records hX hState hLong hRecords
  have hUpper := (O.phase_le_commit_count hX hState).trans hBound
  omega

private theorem mma_before_epilogue_pv {g h : Nat} {d : Wg0.D} {q : Wg1Mma.D}
    (hd : d.site = .svDone) (hLast : d.block + 1 = Result.blocks P (ctaidY L g))
    (hOut : q.site ≠ .outBar) (hExit : q.site ≠ .exit) (hBlock : q.i ≤ d.block) :
    priority P L h (.mma q) < priority P L g (.wg0 d) := by
  cases hSite : q.site
  all_goals try exact (hOut hSite).elim
  all_goals try exact (hExit hSite).elim
  all_goals
    simp only [priority, matmulTime, softmaxTime, hSite, hd, hLast.symm,
      wg0Ordinal, mmaOrdinal, blockTime]
    omega

/-- The MMA lane has not advanced beyond the block whose PV commit is missing. -/
inductive BeforePvCommit (block : Nat) : Machine.ThreadD → Prop where
  | launch (s : Machine.PSite) : BeforePvCommit block (.prologue s)
  | dispatch : BeforePvCommit block .head
  | mma (q : Wg1Mma.D) : q.site ≠ .outBar → q.site ≠ .exit → q.i ≤ block →
      BeforePvCommit block (.mma q)

/-- A missing PV issue bounds the actual elected lane's pending block. -/
theorem pending_mma_before_unissued_pv (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g issuer block : Nat} (hg : g < L.threads) (hBlock : block < Wg0.blocksOf P L g)
    (hIssuer : MmaIssuer P L X (ctaOf L g) issuer)
    (hShort : (X.tr issuer).countP (commitsTo (empty L (ctaOf L g) (rawSlot block))) ≤ block / 2) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧ BeforePvCommit block q := by
  let cta := ctaOf L g
  let slot := rawSlot block
  let m := empty L cta slot
  let sound := fun h hh => (hs h hh).machine
  have hc := NamedBar.cta_lt hg
  obtain ⟨lane, _, _, hTail⟩ := QueryMmaCandidate.select_mma (cta := cta) hpre hX hs ht
    (fun _ h => pending_followed hpre hX hs ht h) hc
  let h := cta * L.block + 128 + lane.val
  obtain ⟨hh, hCta, _, _⟩ := QueryMmaCandidate.lane_geometry hpre hc lane
  change ctaOf L h = cta at hCta
  have hSameCta : SameCta L g h := ⟨hg, hh, hCta.symm⟩
  have hHub := Safety.no_ub hpre hX hs ht
  have hTotal : Wg1Mma.blocks P L h = Wg0.blocksOf P L g :=
    StageAfterPv.block_count_eq (P := P) (g := g) (h := h) hCta
  let hTrace := (sound h hh).produces (hX.thr h hh)
  have hShortAt {q : Wg1Mma.D} {i : Nat} (hi : i ≤ (X.tr h).length)
      (hQ : Frame.stateAt (Machine.code P L) X h i = some (some (.mma q)))
      (hSite : q.site ≠ .elect) : q.i ≤ block := by
    have hId := hIssuer h i q hCta hQ hSite
    have hCount := Wg1MmaGemmTrace.pv_commits_before_block hpre hh slot hTrace hQ
    change ((X.tr h).take i).countP (commitsTo (empty L (ctaOf L h) slot)) = _ at hCount
    rw [hCta] at hCount
    have hMono := countP_take_mono (commitsTo m) (X.tr h) hi
    rw [List.take_length, hCount, hId] at hMono
    have hn := hMono.trans hShort
    change (q.i + (1 - block % 2)) / 2 ≤ block / 2 at hn
    omega
  have hNoExit {j : Nat} {p : Wg1Mma.D} (hj : j ≤ (X.tr h).length)
      (hP : Frame.stateAt (Machine.code P L) X h j = some (some (.mma p)))
      (hExit : p.site = .exit) : False := by
    obtain ⟨i, _, e, q, he, hQ, hOut⟩ :=
      ClosingOrder.mma_out_bar_before_exit_state hpre ht hh hj hP hExit
    obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.fired_site hs hX he hQ
    have hI : Wg1Mma.Inv P L h q := hI
    have hN := hShortAt (PTX.len_of_get he).le hQ (by simp [hOut])
    rw [hI.end_i hOut, hTotal] at hN
    omega
  rcases hTail with ⟨i, tag, q, he, hState, hSite⟩ | ⟨q, hPending, hQ, hActive⟩
  · exact (hNoExit (PTX.len_of_get he).le hState hSite).elim
  refine ⟨h, q, hSameCta, ⟨hPending, hQ⟩, ?_⟩
  cases hActive with
  | launch s => exact .launch s
  | dispatch => exact .dispatch
  | mma p =>
    obtain ⟨v, hRun⟩ := Frame.run_some hX hHub hPending
    obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.end_at hs hh hRun hQ
    have hI : Wg1Mma.Inv P L h p := hI
    by_cases hElect : p.site = .elect
    · have hZero := hI.prefix_i (by rw [hElect]; trivial)
      exact .mma p (by simp [hElect]) (by simp [hElect]) (hZero ▸ Nat.zero_le block)
    have hN := hShortAt le_rfl hQ hElect
    have hOut : p.site ≠ .outBar := by
      intro hOut
      rw [hI.end_i hOut, hTotal] at hN
      omega
    exact .mma p hOut (hNoExit le_rfl hQ) hN

/-- A softmax epilogue waiting for PV has an earlier pending lane in the CTA's MMA warp. -/
theorem pending_softmax_pv_earlier (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hsg : SyncGuarded L kernel X)
    {g : Nat} {d : Wg0.D} (hp : PendingState P L X g (.wg0 d)) (hRel : PTX.Step.Released L X g)
    (hd : d.site = .svDone) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.wg0 d) := by
  have hX := hmax.1
  obtain ⟨issuer, hIssuer, hShort⟩ := pending_softmax_pv_missing hpre hmax hs ht hsg hp hRel hd
  have hHub := Safety.no_ub hpre hX hs ht
  obtain ⟨_, hRun⟩ := Frame.run_some hX hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  have hInv : Wg0.Inv P L g d := hInv
  have hLast : d.block + 1 = Result.blocks P (ctaidY L g) :=
    hInv.epilogueLast (by rw [hd]; rfl)
  obtain ⟨h, q, hCta, hPending, hBefore⟩ :=
    pending_mma_before_unissued_pv hpre hX hs ht hp.1.1 hInv.blockLt hIssuer hShort
  refine ⟨h, q, hCta, hPending, ?_⟩
  cases hBefore with
  | launch s =>
    simp only [priority, softmaxTime, hd, wg0Ordinal, blockTime]
    omega
  | dispatch =>
    simp only [priority, softmaxTime, hd, wg0Ordinal, blockTime]
    omega
  | mma p hOut hExit hN => exact mma_before_epilogue_pv hd hLast hOut hExit hN

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

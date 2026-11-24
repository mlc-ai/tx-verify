-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemRelease
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputTmemReadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvCompletedValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory

@[expose] public section

/-! # Epilogue tensor-memory loads have sources at issue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Protocol Result OutputTmemReadSource AsyncCopy

/-- The final PV acquire selects the write and value for a just-issued output load. -/
theorem final_load_source {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i : Nat} {words : List Value} {tile : Fin 4} {d : Wg0.D} (reg : Fin 64)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oLoad tile)
    (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b) (hWords : words.length = 64) :
    ∃ src value, TcMma.ReadSource L X .ld src (g, i) (outputCell L g tile reg) ∧
      TcMma.Wrote L Assumptions.all X src (outputCell L g tile reg) value := by
  have he := hload.choose_spec
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hInv : Wg0.Inv P L g d := hInv
  have hLast := hInv.epilogueLast (by rw [hsite]; rfl)
  obtain ⟨w, hwi, wt, scope, hw, q, hState, hWsite, hBlock⟩ :=
    Wg0OutputVisits.pvWaitBeforeLoad_state hpre hX hg (hs g hg).machine hInv hd hsite
  have hw' : X.get (g, w) = some
      ⟨wt, .wait (GemmRing.empty L (ctaOf L g) (rawSlot q.block))
        (q.block / 2 % 2) true true scope⟩ := by
    rw [hBlock]
    exact hw
  obtain ⟨issuer, hu⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun a ha => (hs a ha).machine)
  obtain ⟨c, ct, sp, rank, pv, src, hc, hPv, hPvSite, hPvBlock, hNotify, hIdx, hIssue,
    hCell, hRead⟩ :=
    final_pv_source_of_wait hpre hX hs ht hu hState hWsite hBlock hw'
      hwi hInv hLast hload hWords reg
  have hRead := hRead (tmem_load_source_live hpre hX hs ht hCell)
  obtain ⟨j, hj, hSrc⟩ := PvIssueHistory.pv_state_of_commit hc hPv hPvSite (lastIssue tile)
  have hSame : j = src := by omega
  subst j
  rw [hPvBlock] at hSrc
  have hSrcLt : src < c := by have := (lastIssue tile).isLt; omega
  have hTracked : TracksMma X (issuer, src) (issuer, c) :=
    ⟨rfl, hSrcLt, .inl ⟨_, _, _, _, hIssue⟩, sp, ct, hc⟩
  have hDone := (hX.tcCommit (issuer, c) rank hNotify).2 (issuer, src) hTracked
  have hWrite : X.MmaCell (issuer, src) (outputCell L g tile reg) := by
    rcases hRead.2.1 with h | ⟨_, _, _, _, ⟨_, hs'⟩, _, _⟩ |
      ⟨_, _, _, _, ⟨_, hs'⟩, _, _, _, _⟩ | ⟨_, ⟨_, hs'⟩, _⟩
    · exact h
    all_goals cases congrArg Event.kind (Option.some.inj (hIssue.choose_spec.symm.trans hs'))
  obtain ⟨value, hValue⟩ := pv_completed_values hpre hX hs ht hIssue hSrc hDone _ hWrite
  exact ⟨(issuer, src), value, hRead, .inl hValue⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

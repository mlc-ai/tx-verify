-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasRound
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
import all Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
import all Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.ReturningPrefix
import Lemmas.Order.ElectSiteOrdinal
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

set_option maxRecDepth 100000 in
/-- Inside a warm round, after the stage-zero wait loop or after the stage-one wait loop,
a lane stays in that part of the round until its next shuffle. -/
theorem warmRoundNoReturn {l : Launch} {t : Nat} {s u : TState} {es : List Event}
    (lo : Nat) (hlo : lo = 1149 ∨ lo = 1178)
    (hReach : TraceReach kernel Assumptions.all l t s es u)
    (hs : lo ≤ s.pc ∧ s.pc ≤ 1239) (hCount : es.countP Execution.isShfl = 0) :
    lo ≤ u.pc ∧ u.pc ≤ 1239 := by
  have hLo : 174 ≤ lo := by omega
  have hStart : 1149 ≤ lo ∧ lo ≤ 1240 := by omega
  have hRank : (((kernel.code.drop lo).take (1240-lo)).zipIdx lo).all
      (fun (i,k) => LoaderRankedInstr 1240 k i) = true := by
    rcases hlo with rfl | rfl <;> kernel_rfl
  have hTail : ∀ pos ∈ List.range 91, loaderShuffleTail 1240 (1149+pos) = 1 := by
    decide +kernel
  have hAudit : ∀ edge ∈ loaderBackEdges, lo ≤ edge.1 → edge.1 ≤ 1239 → lo ≤ edge.2 := by
    rcases hlo with rfl | rfl <;> decide
  have step {a b : TState} {e : Option Event} (h : WStep kernel Assumptions.all l t a e b)
      (hA : lo ≤ a.pc ∧ a.pc ≤ 1239)
      (hz : e.toList.countP Execution.isShfl = 0) :
      lo ≤ b.pc ∧ b.pc ≤ 1239 := by
    have hPc : lo ≤ a.pc ∧ a.pc < 1240 := ⟨hA.1,by omega⟩
    have hFloor : lo ≤ b.pc := by
      by_contra! hn
      rcases h with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
      · have hedge := loaderTauBackEdge (hLo.trans hPc.1) (by omega) (by omega) ht
        exact (Nat.not_le_of_lt hn) (hAudit _ hedge hPc.1 hA.2)
      · have he' : EStep kernel [] l t a ev (some b) := by
          obtain ⟨tmpl,hO,hF⟩ := he
          exact ⟨tmpl,by rwa [← loaderOutCore (hLo.trans hPc.1) (by omega)],hF⟩
        rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 <;> omega
    have hCeiling : b.pc ≤ 1239 := by
      have hEq := rankedLoaderStep (start := lo) (stop := 1240)
        ⟨hLo,hStart.2,by decide⟩ hRank hPc.1 hPc.2 h
      have hT := hTail (a.pc-1149) (List.mem_range.mpr (by omega))
      rw [Nat.add_sub_of_le (hStart.1.trans hPc.1)] at hT
      rw [hT,hz,Nat.zero_add] at hEq
      by_contra! hn
      have hDrop : ((kernel.code.take 1240).drop b.pc) = [] :=
        List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
      simp [loaderShuffleTail,hDrop] at hEq
    exact ⟨hFloor,hCeiling⟩
  induction hReach with
  | refl => exact hs
  | tau ht _ ih => exact ih (step (.inl ⟨rfl,ht⟩) hs rfl) hCount
  | @event a b c rest e he _ ih =>
    by_cases hMark : Execution.isShfl e = true
    · simp [hMark] at hCount
    · have hMark' := Bool.eq_false_iff.mpr hMark
      simp only [List.countP_cons,hMark',Bool.false_eq_true,ite_false] at hCount
      exact ih (step (.inr ⟨_,rfl,he⟩) hs (by simp [hMark'])) hCount

/-- A lane that recorded an event after one of the warm Bias wait loops cannot reach a
point before that loop again without a shuffle. -/
theorem noReturnAfterEvent {l : Launch} {X : Execution} {t j stop : Nat} {e : Event}
    (lo : Nat) (hlo : lo = 1149 ∨ lo = 1178) (he : X.get (t,j) = some e)
    (hPc : lo ≤ e.pc ∧ e.pc ≤ 1239) (hj : j < stop) {target : TState}
    (hTarget : TraceReach kernel Assumptions.all l t {} ((X.tr t).take stop) target)
    (hBelow : target.pc < lo)
    (hZero : ((X.tr t).take stop).countP Execution.isShfl =
      ((X.tr t).take j).countP Execution.isShfl) : False := by
  obtain ⟨q,hQ,hLocal⟩ := hTarget.returnedPrefix
  have hIn : ((X.tr t).take stop)[j]? = some e := by rwa [List.getElem?_take_of_lt hj]
  obtain ⟨t1,o,hPath,hStep⟩ := hQ.before_event hIn
  rw [List.take_take,Nat.min_eq_left hj.le] at hPath
  obtain ⟨b,hB,hBLocal⟩ := hPath.returnedPrefix
  let rest := ((X.tr t).drop j).take (stop-j)
  have hTrunc : (X.tr t).take stop = (X.tr t).take j ++ rest := by
    conv_lhs => rw [← Nat.add_sub_of_le hj.le]
    rw [List.take_add]
  have hRest : Run kernel Assumptions.all l t b rest (some q) := by
    apply hB.after_returned_prefix
    rw [← hTrunc]
    exact hQ
  have hNe : rest ≠ [] := by
    have hFirst : rest[0]? = some e := by
      simp only [rest]
      rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_zero]
      exact he
    exact List.ne_nil_of_mem (List.mem_of_getElem? hFirst)
  have hRun := hRest.after_local_nonempty hBLocal hNe
  have hCore := hRun.returning_reach.append (.of_local hLocal)
  rw [List.append_nil] at hCore
  have hZeroRest : rest.countP Execution.isShfl = 0 := by
    have h := hZero
    rw [hTrunc,List.countP_append] at h
    omega
  have hSrc : t1.pc = e.pc := (estep_source_pc hStep).symm
  have h := (warmRoundNoReturn lo hlo hCore ⟨hSrc ▸ hPc.1,hSrc ▸ hPc.2⟩ hZeroRest).1
  omega

/-- A loader event after the warm loop has at least the shuffle rank of the warm exit. -/
theorem lateLoaderEventRank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch lane j : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hl : lane < 32)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {e : Event} (he : X.get (warpLane l g lane,j) = some e) (hLate : 1353 ≤ e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    primingSearchShuffleCount batch+64+64*warmRounds p l g batch ≤
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl := by
  have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨b,hB,hL,hH,hProj⟩ := actualWarmCacheProjectionOrAfter hp hX hg hw hl
    (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA he (by omega)
    (.inr ⟨batch,hb,hLo,hHi,hTrips⟩) hSafe
  obtain ⟨_,_,uniq⟩ := tileBatch_existsUnique p hCTA
  have hb' : b = batch := (uniq b ⟨hB,hL,hH⟩).trans (uniq batch ⟨hb,hLo,hHi⟩).symm
  subst b
  rcases hProj with ⟨hPc,_⟩ | ⟨_,pos,hBefore,_,hRank⟩
  · omega
  · have hMono := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hBefore
    unfold warmRounds
    omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

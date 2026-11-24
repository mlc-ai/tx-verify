-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Step.Issue

public section

/-! # Counted ordinary writes after the common prologue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : Machine.ThreadD}

private theorem no_alloc_at_write_tail (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : ∀ s, d ≠ .prologue s) :
    ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → False := by
  intro pc grp dst n he
  obtain ⟨q, hq⟩ := Frame.state_of_noUb hs hX ht hub he
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g (Frame.lt_of_get hX he)).machine he hq
  have hAlloc := ResourceEvents.emits hpre hf rfl
  have hIndex : (X.tr g).length - 1 + 1 = (X.tr g).length := by
    have hLen : (X.tr g).length - 1 < (X.tr g).length := PTX.len_of_get he
    omega
  have hNext := hσ
  rw [← hIndex, Frame.stateAt_succ he, hq, Option.bind_some] at hNext
  cases hAlloc with
  | alloc _ _ _ =>
    change Machine.next P L g (.prologue .alloc) ⟨pc, .tc (.resource grp dst (.alloc n))⟩ =
      some (some d) at hNext
    simp only [Machine.next,
      PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hNext
    exact hd _ (Option.some.inj (Option.some.inj hNext)).symm
  | relinquish _ _ h => cases h
  | dealloc _ _ _ _ _ h => cases h

/-- A released lane past the prologue can append its defined weak write. -/
theorem role_write_extension {t u v : TState} {a : Acc} {bs : List Byte} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hrel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : ∀ s, d ≠ .prologue s) (hRun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) (hWeak : a.release = false)
    (hout : out kernel Assumptions.all L g u = .ev (.write a bs v)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hSigma
    exact hd _ (Option.some.inj (Option.some.inj hSigma)).symm
  exact PTX.Step.plain_counted_extension hX hg (.inl hne) hrel hRun hTau
    (e := ⟨u.pc, .wr a bs⟩) (o := some v) ⟨_, hout, rfl, rfl⟩
    (by simp [Kind.Plain, hWeak]) (by simp [Kind.isTma, hWeak])
    (by simp) (by simp) (by simp) rfl
    (hX.tmemPairResult.snoc_last
      (fun pc grp dst n he =>
        (no_alloc_at_write_tail hpre hs hX ht hub hSigma hd pc grp dst n he).elim))
    (Interface.all_wf_snoc_of_not_nc hX (by simp) (by simp))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

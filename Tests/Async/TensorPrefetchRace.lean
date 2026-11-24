-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Safety
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Async.AsyncCopy
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# A tensor prefetch is a weak async-proxy read (§9.7.10.28.5.5, §8.6, §8.7.1–2)

A 1D u8 map of 16 elements at global 4096, prefetched whole: the prefetch reads global bytes
4096..4111 through the async proxy and never completes. An overlapping one-byte write in another
thread, or later in the same thread, is a uniform-size `Race`; an overlapping four-byte write is
`Mixed`. A tensor store whose output writes completed (bulk wait `.full`) before the prefetch is
ordered before it. With no write there is nothing to report.
-/

namespace PTX.Tests.TensorPrefetchRace
noncomputable section

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }

private def line : TensorDescriptor.Descriptor 0 :=
  ⟨.u8, 4096, ![16], ![], ⟨![16], ![1]⟩, .none, .zero, .small⟩
private def pre : TensorPrefetch.Spec := ⟨0, line, ![0], none⟩

private def l0 : Loc := ⟨.global, 0, 4096⟩
private def b : Byte := (.bits 8 0, 0)
private def byte : Acc := { loc := l0, size := 1 }
private def word : Acc := { loc := l0, size := 4 }

/-- Byte 0 of the prefetched box is global byte 4096. -/
private theorem source0 : TensorTransfer.sourceLoc line ![0] none 0 0 0 = some l0 := rfl

/-- Thread 0 prefetches; thread 1 performs `tail`. -/
private def X (tail : List Event) : Execution where
  tr
    | 0 => [⟨0, .tensorPrefetch 1024 pre⟩]
    | 1 => tail
    | _ => []
  rf _ _ := none

private def pf : AsyncCopy.Ref := .async (0, 0) (.read (.prefetch 0 0 0))

private theorem pf_intent (tail : List Event) : (X tail).Intent pf byte false :=
  ⟨rfl, pre, 1024, ⟨0, rfl⟩, source0, rfl⟩

/-- The prefetch read is never observed complete. -/
private theorem pf_unfinished (Y : Execution) (i w : EvId) (x y k : Nat) :
    ¬ AsyncFinished L Y i (.read (.prefetch x y k)) w := by
  rintro (⟨g, hv, -⟩ | ⟨ws, ⟨n, m, hn, -⟩, -⟩)
  · cases g with
    | bulk mode => cases mode <;> simp [GroupWaitVisible] at hv
    | cpAsync => simp [GroupWaitVisible] at hv
  · simp [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn

/-- With no async proxy fence, no thread access is ordered before an asynchronous access. -/
private theorem no_proxy (Y : Execution) (h : ∀ e sp sc, ¬ Y.IsProxyFence e (.async sp) sc)
    (e i : EvId) : ¬ ProxyBefore L Y e i l0 := by
  rintro ⟨fence, sp, sc, hf, -⟩
  exact h fence sp sc hf

/-- Neither direction of `modelCausality` holds at `l0` between the prefetch's read and a thread
access, in an execution with no async proxy fence and no linear operation at `(0, 0)`. -/
private theorem unordered (Y : Execution) (f : EvId)
    (hfence : ∀ e sp sc, ¬ Y.IsProxyFence e (.async sp) sc) (hcopy : ¬ GenericCopy Y (0, 0)) :
    ¬ modelCausality L Y l0 pf (.thread f) ∧ ¬ modelCausality L Y l0 (.thread f) pf := by
  constructor
  · rintro ⟨-, w, hw, -⟩
    exact pf_unfinished Y _ w 0 0 0 hw
  · rintro ⟨-, hp | ⟨hg, -⟩⟩
    · exact no_proxy Y hfence f _ hp
    · exact hcopy hg

private theorem covers (a : Acc) (h : a.loc = l0) (hs : 0 < a.size) : a.Covers l0 := by
  simp [Acc.Covers, Loc.InRange, h, hs]

/-- `X tail` with a one-event tail records no async proxy fence: thread 0 holds the prefetch,
thread 1 the write and every other thread an empty trace. -/
private theorem x_no_fence (a : Acc) (bs : List Byte) :
    ∀ e sp sc, ¬ (X [⟨0, .wr a bs⟩]).IsProxyFence e (.async sp) sc := by
  rintro ⟨g, i⟩ sp sc ⟨pc, h⟩
  rcases g with _ | _ | g
  · simp [Execution.get, X] at h
    cases i <;> simp at h
  · simp [Execution.get, X] at h
    cases i <;> simp at h
  · simp [Execution.get, X] at h

/-- `X tail` issues no linear operation at its first event, which is the prefetch. -/
private theorem x_no_copy (tail : List Event) : ¬ GenericCopy (X tail) (0, 0) := by
  rintro ⟨s, ⟨pc, h⟩, -⟩
  simp [Execution.get, X] at h

/-- An overlapping one-byte write in another thread is a uniform-size race. -/
example : Race L (X [⟨0, .wr byte [b]⟩]) := by
  have hun : ¬ modelCausality L (X [⟨0, .wr byte [b]⟩]) l0 pf (.thread (1, 0)) ∧
      ¬ modelCausality L (X [⟨0, .wr byte [b]⟩]) l0 (.thread (1, 0)) pf :=
    unordered _ _ (x_no_fence byte [b]) (x_no_copy _)
  refine ⟨pf, .thread (1, 0), byte, byte, l0,
    ⟨by simp [pf], false, true, pf_intent _, .inr (.inl ⟨[b], ⟨0, rfl⟩, rfl⟩), .inr rfl,
      l0, covers byte rfl (by decide), covers byte rfl (by decide)⟩,
    ⟨rfl, rfl⟩, covers byte rfl (by decide), ?_,
    fun h => hun.1 ((ByteCausality.direct_iff_of_global rfl).1 h),
    fun h => hun.2 ((ByteCausality.direct_iff_of_global rfl).1 h), ?_⟩
  · rintro ⟨-, hg, -⟩
    exact x_no_copy _ (hg.mpr trivial)
  · rintro ⟨⟨h, -⟩, -⟩
    cases h

/-- An overlapping four-byte write is a mixed-size race. -/
example : Mixed L (X [⟨0, .wr word [b, b, b, b]⟩]) :=
  have hun : ¬ modelCausality L (X [⟨0, .wr word [b, b, b, b]⟩]) l0 pf (.thread (1, 0)) ∧
      ¬ modelCausality L (X [⟨0, .wr word [b, b, b, b]⟩]) l0 (.thread (1, 0)) pf :=
    unordered _ _ (x_no_fence word [b, b, b, b]) (x_no_copy _)
  ⟨pf, .thread (1, 0), byte, word, l0,
    ⟨by simp [pf], false, true, pf_intent _, .inr (.inl ⟨[b, b, b, b], ⟨0, rfl⟩, rfl⟩),
      .inr rfl, l0, covers byte rfl (by decide), covers word rfl (by decide)⟩,
    fun h => absurd h.2 (by decide), covers byte rfl (by decide),
    covers word rfl (by decide), fun h => hun.1 ((ByteCausality.direct_iff_of_global rfl).1 h),
    fun h => hun.2 ((ByteCausality.direct_iff_of_global rfl).1 h)⟩

/-- A later write of the prefetching thread itself is not ordered after the prefetch: program
order relates the two, but they use different proxies and the prefetch never completes. -/
private def Y : Execution where
  tr
    | 0 => [⟨0, .tensorPrefetch 1024 pre⟩, ⟨1, .wr byte [b]⟩]
    | _ => []
  rf _ _ := none

/-- `Y` records no async proxy fence. -/
private theorem y_no_fence : ∀ e sp sc, ¬ Y.IsProxyFence e (.async sp) sc := by
  rintro ⟨g, i⟩ sp sc ⟨pc, h⟩
  rcases g with _ | g
  · simp [Execution.get, Y] at h
    cases i with
    | zero => simp at h
    | succ i =>
      cases i with
      | zero => simp at h
      | succ i => simp at h
  · simp [Execution.get, Y] at h

/-- `Y` issues no linear operation at its first event, which is the prefetch. -/
private theorem y_no_copy : ¬ GenericCopy Y (0, 0) := by
  rintro ⟨s, ⟨pc, h⟩, -⟩
  simp [Execution.get, Y] at h

example : Race L Y := by
  have hun : ¬ modelCausality L Y l0 pf (.thread (0, 1)) ∧
      ¬ modelCausality L Y l0 (.thread (0, 1)) pf := unordered _ _ y_no_fence y_no_copy
  refine ⟨pf, .thread (0, 1), byte, byte, l0,
    ⟨by simp [pf], false, true, ⟨rfl, pre, 1024, ⟨0, rfl⟩, source0, rfl⟩,
      .inr (.inl ⟨[b], ⟨1, rfl⟩, rfl⟩), .inr rfl, l0, covers byte rfl (by decide),
      covers byte rfl (by decide)⟩,
    ⟨rfl, rfl⟩, covers byte rfl (by decide), ?_,
    fun h => hun.1 ((ByteCausality.direct_iff_of_global rfl).1 h),
    fun h => hun.2 ((ByteCausality.direct_iff_of_global rfl).1 h), ?_⟩
  · rintro ⟨-, hg, -⟩
    exact y_no_copy (hg.mpr trivial)
  · rintro ⟨⟨h, -⟩, -⟩
    cases h

/-- With no write, a prefetch conflicts with nothing. -/
example : ¬ Race L (X []) ∧ ¬ Mixed L (X []) := by
  have hw : ∀ r a, ¬ (X []).Intent r a true := by
    intro r a h
    cases r with
    | thread i =>
      obtain ⟨g, k⟩ := i
      rcases h with ⟨bs, ⟨pc, h⟩, -⟩ | ⟨bs, ⟨pc, h⟩, -⟩ | ⟨old, new, ⟨pc, h⟩⟩ <;>
        rcases g with _ | _ | g <;> rcases k with _ | k <;> simp [Execution.get, X] at h
    | async i p =>
      obtain ⟨g, k⟩ := i
      rcases g with _ | _ | g <;> rcases k with _ | k <;> cases p <;>
        simp [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
          Execution.TensorStoreIssue, Execution.TensorIssue, Execution.ClcIssue, Execution.Copy,
          Execution.get, X] at h
  have hc : ∀ e f a a', ¬ Conflict (X []) e f a a' := by
    rintro e f a a' ⟨-, we, wf, he, hf, hw', -⟩
    rcases hw' with rfl | rfl
    · exact hw _ _ he
    · exact hw _ _ hf
  exact ⟨fun ⟨e, f, a, a', _, h, _⟩ => hc e f a a' h, fun ⟨e, f, a, a', _, h, _⟩ => hc e f a a' h⟩

/-! ### A write ordered before the prefetch -/

private def storeLine : TensorDescriptor.Descriptor 0 :=
  ⟨.u8, 4096, ![16], ![], ⟨![16], ![1]⟩, .none, .zero, .small⟩
private def store : TensorStore.Spec := ⟨⟨0, storeLine, ![0], ⟨.shared, 0, 128⟩, none⟩, none⟩

/-- Thread 0 stores the line, waits for the store's output writes, then prefetches it. -/
private def Z : Execution where
  tr
    | 0 => [⟨0, .tensorStore 2048 store⟩, ⟨1, .bulkCommit⟩, ⟨2, .bulkWait .full 0⟩,
        ⟨3, .tensorPrefetch 1024 pre⟩]
    | _ => []
  rf _ _ := none
  tensorStores i := if i = (0, 0) then some ⟨store, { readsDone := true, fullDone := true }⟩
    else none

private theorem waits : BulkWaitsFor Z .full (0, 0) (0, 2) := by
  refine ⟨2, 0, rfl, ?_⟩
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions,
    bulkAction, Z, BulkGroup.run, BulkGroup.step]

/-- Both stages a `.full` wait covers are present: the store completed its reads and its writes. -/
private theorem stages_present :
    ∀ q ∈ GroupWaitStages Z (0, 0) (.bulk .full), Z.AsyncPresent (0, 0) q := by
  intro q hq
  have hq' : q = .readsDone ∨ q = .fullDone := by
    simpa [GroupWaitStages, Execution.get, Z, Event.kind] using hq
  rcases hq' with rfl | rfl <;>
    exact ⟨⟨store, { readsDone := true, fullDone := true }⟩, by simp [Z], rfl⟩

/-- The `.full` wait of thread 0 at `(0, 2)` observes the store's write completion. -/
private theorem finished : AsyncFinished L Z (0, 0) (.write (.store 0 0 0)) (0, 2) :=
  .inl ⟨.bulk .full, by decide, waits, stages_present⟩

/-- The store's completed write of byte 4096 is ordered before the prefetch's read of it, so
this pair is no race. -/
example : modelCausality L Z l0 (.async (0, 0) (.write (.store 0 0 0)))
    (.async (0, 3) (.read (.prefetch 0 0 0))) := by
  refine ⟨.inl ⟨by decide, by decide, rfl⟩, .direct ⟨⟨byte, true, ⟨rfl, store, 2048, ⟨0, rfl⟩,
    rfl, rfl⟩, covers byte rfl (by decide)⟩, ⟨byte, false, ⟨rfl, pre, 1024, ⟨3, rfl⟩, source0,
    rfl⟩, covers byte rfl (by decide)⟩, .inl ⟨(0, 2), finished, ?_⟩⟩⟩
  exact .single (.inl ⟨rfl, by decide, by decide, fun h => by
    simp [SameAccess, Execution.get, Z, Event.acc] at h⟩)

end
end PTX.Tests.TensorPrefetchRace

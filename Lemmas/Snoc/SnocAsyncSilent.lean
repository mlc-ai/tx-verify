-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Snoc.SnocMemory

@[expose] public section

/-! Appending an event that issues and awaits no asynchronous operation preserves all older
asynchronous effects and byte visibility into older events. Such an event can only add
incoming order at its own newly appended thread event. -/
namespace PTX
noncomputable section
open AsyncCopy

/-- A kind that issues no asynchronous operation (linear copy or prefetch, arrive-on, MMA,
`tcgen05.cp` or `tcgen05.shift`, commit, tensor copy, store or prefetch, CLC request), is no group
wait, and completes no acquiring mbarrier wait. -/
def Kind.AsyncSilent : Kind → Prop
  | .copy _ | .bulkPrefetch _ | .asyncArrive .. | .tensorIssue .. | .tensorStore ..
  | .tensorPrefetch .. | .clcIssue .. | .bulkWait .. | .asyncWait _ => False
  | .tc (.mma ..) | .tc (.commit _) | .tc (.cp _) | .tc (.shift _) => False
  | .wait _ _ ok acquire _ => ok = false ∨ acquire = false
  | _ => True

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

namespace Kind.AsyncSilent

theorem ne {k : Kind} (hs : e.kind.AsyncSilent) (hk : ¬k.AsyncSilent) : e.kind≠k :=
  fun h => hk (h ▸ hs)

theorem snoc_copy (hs : e.kind.AsyncSilent) {i : EvId} {s : Spec} :
    (X.snoc g e r).Copy i s ↔ X.Copy i s :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_bulkPrefetch (hs : e.kind.AsyncSilent) {i : EvId} {a : Acc} :
    (X.snoc g e r).BulkPrefetch i a ↔ X.BulkPrefetch i a :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_asyncArrive (hs : e.kind.AsyncSilent) {i : EvId} {m : Loc} {noinc : Bool} :
    (X.snoc g e r).AsyncArrive i m noinc ↔ X.AsyncArrive i m noinc :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_tracksCpAsync (hs : e.kind.AsyncSilent) {i j : EvId} :
    TracksCpAsync (X.snoc g e r) i j ↔ TracksCpAsync X i j := by
  simp only [TracksCpAsync, snoc_copy hs, snoc_asyncArrive hs]

theorem snoc_genericCopy (hs : e.kind.AsyncSilent) {i : EvId} :
    GenericCopy (X.snoc g e r) i ↔ GenericCopy X i := by
  simp only [GenericCopy, snoc_copy hs]

theorem snoc_commit (hs : e.kind.AsyncSilent) {i : EvId} {s : TcCommit.Spec} :
    (X.snoc g e r).Commit i s ↔ X.Commit i s := snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_issuedBy (hs : e.kind.AsyncSilent) :
    issuedBy (X.snoc g e r) = issuedBy X := by
  funext i
  unfold issuedBy
  rw [snoc_get]
  split_ifs with hi
  · subst i
    obtain ⟨pc,kind⟩ := e
    cases kind <;> simp_all [Kind.AsyncSilent,Execution.get]
  · rfl

theorem snoc_mmaIssue (hs : e.kind.AsyncSilent) {i : EvId} {d : Nat}
    {spec : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} :
    (X.snoc g e r).MmaIssue i d spec accum mask ↔ X.MmaIssue i d spec accum mask :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_cpIssue (hs : e.kind.AsyncSilent) {i : EvId} {c : TcCopy.Spec} :
    (X.snoc g e r).CpIssue i c ↔ X.CpIssue i c :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_shiftIssue (hs : e.kind.AsyncSilent) {i : EvId} {c : TcShift.Spec} :
    (X.snoc g e r).ShiftIssue i c ↔ X.ShiftIssue i c :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_mmaRead (hs : e.kind.AsyncSilent) {i : EvId} {isB : Bool}
    {k : Nat} {l : Loc} {b : Option Byte} :
    (X.snoc g e r).MmaRead i isB k l b ↔ X.MmaRead i isB k l b := by
  simp only [Execution.MmaRead,Execution.MmaFootprint,snoc_mmaIssue hs,snoc_cpIssue hs,snoc_async]

theorem snoc_tensorIssue (hs : e.kind.AsyncSilent) {i : EvId} {addr : Nat} {spec : TensorCopy.Spec}
    :
    (X.snoc g e r).TensorIssue i addr spec ↔ X.TensorIssue i addr spec :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_storeIssue (hs : e.kind.AsyncSilent) {i : EvId} {addr : Nat} {spec : TensorStore.Spec}
    :
    (X.snoc g e r).TensorStoreIssue i addr spec ↔ X.TensorStoreIssue i addr spec :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_prefetchIssue (hs : e.kind.AsyncSilent) {i : EvId} {addr : Nat}
    {spec : TensorPrefetch.Spec} :
    (X.snoc g e r).TensorPrefetchIssue i addr spec ↔ X.TensorPrefetchIssue i addr spec :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_clcIssue (hs : e.kind.AsyncSilent) {i : EvId} {spec : Clc.Spec} {targets : List Nat} :
    (X.snoc g e r).ClcIssue i spec targets ↔ X.ClcIssue i spec targets :=
  snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))

theorem snoc_acquireWait (hs : e.kind.AsyncSilent) {i : EvId} {m : Loc} :
    (X.snoc g e r).AcquireWait i m ↔ X.AcquireWait i m := by
  have hs (parity : Nat) (scope : MbarScope) :
      (∃ pc, (X.snoc g e r).get i = some ⟨pc,.wait m parity true true scope⟩) ↔
      ∃ pc, X.get i = some ⟨pc,.wait m parity true true scope⟩ :=
        snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))
  unfold Execution.AcquireWait
  rw [exists_comm,exists_comm (p := fun pc parity => ∃ scope, X.get i =
    some ⟨pc,.wait m parity true true scope⟩)]
  apply exists_congr
  intro parity
  rw [exists_comm,exists_comm (p := fun pc scope => X.get i =
    some ⟨pc,.wait m parity true true scope⟩)]
  exact exists_congr (hs parity)

theorem snoc_asyncPresent (hs : e.kind.AsyncSilent) {i : EvId} {p : Part} :
    (X.snoc g e r).AsyncPresent i p ↔ X.AsyncPresent i p := by
  cases p <;> simp only [Execution.AsyncPresent, snoc_mmaRead hs, snoc_async]
  all_goals rfl

theorem snoc_tracksMma (hs : e.kind.AsyncSilent) {i j : EvId} :
    TracksMma (X.snoc g e r) i j ↔ TracksMma X i j := by
  simp only [TracksMma, Execution.TcAsync, snoc_mmaIssue hs, snoc_cpIssue hs, snoc_shiftIssue hs,
    snoc_commit hs]

theorem snoc_waitObserves (hs : e.kind.AsyncSilent) {x : Ref} {w : EvId} {m : Loc} {ws : MbarScope}
    :
    WaitObserves (X.snoc g e r) x w m true ws ↔ WaitObserves X x w m true ws := by
  have hw (parity : Nat) :
      (∃ pc, (X.snoc g e r).get w = some ⟨pc,.wait m parity true true ws⟩) ↔
      ∃ pc, X.get w = some ⟨pc,.wait m parity true true ws⟩ :=
        snoc_kind_iff (hs.ne (by simp [Kind.AsyncSilent]))
  unfold WaitObserves
  rw [exists_comm, exists_comm (p := fun pc parity => X.get w =
    some ⟨pc,.wait m parity true true ws⟩)]
  simp only [hw]
  rfl

theorem snoc_groupWaitsFor (hs : e.kind.AsyncSilent) {k : GroupWait} {i w : EvId} :
    GroupWaitsFor (X.snoc g e r) k i w ↔ GroupWaitsFor X k i w := by
  cases k with
  | bulk mode => exact snoc_bulkWaits (fun mode n => hs.ne (by simp [Kind.AsyncSilent]))
  | cpAsync =>
    constructor
    · rintro ⟨pc, n, hp, hst⟩
      obtain ⟨pc, hp'⟩ := (snoc_kind_iff (X := X) (g := g) (r := r) (v := w)
        (hs.ne (k := .asyncWait n) (by simp [Kind.AsyncSilent]))).mp ⟨pc, hp⟩
      refine ⟨pc, n, hp', ?_⟩
      simpa only [asyncStateBefore, snoc_take (len_of_get hp').le] using hst
    · rintro ⟨pc, n, hp, hst⟩
      refine ⟨pc, n, Execution.le_get le_snoc hp, ?_⟩
      simpa only [asyncStateBefore, snoc_take (len_of_get hp).le] using hst

theorem snoc_groupWaitStages (hs : e.kind.AsyncSilent) {i : EvId} {k : GroupWait} :
    GroupWaitStages (X.snoc g e r) i k = GroupWaitStages X i k := by
  unfold GroupWaitStages
  rw [snoc_get]
  split_ifs with hi
  · have hn : X.get i = none := by rw [hi]; exact List.getElem?_eq_none (le_refl _)
    rw [hn]
    obtain ⟨pc, kind⟩ := e
    cases kind <;> cases k <;> simp_all [Kind.AsyncSilent] <;> (rename_i mode; cases mode <;> rfl)
  · rfl

theorem snoc_intent_async (hs : e.kind.AsyncSilent) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {w : Bool} : (X.snoc g e r).Intent (.async i p) a w ↔ X.Intent (.async i p) a w := by
  cases p <;> simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
    and_false, snoc_copy hs, snoc_bulkPrefetch hs, Execution.MmaFootprint, snoc_mmaIssue hs,
    snoc_cpIssue hs, snoc_tensorIssue hs, snoc_storeIssue hs, snoc_prefetchIssue hs,
    snoc_clcIssue hs]

theorem snoc_asyncCovers (hs : e.kind.AsyncSilent) {i : EvId} {p : AsyncCopy.Part} {l : Loc} :
    AsyncCovers (X.snoc g e r) i p l ↔ AsyncCovers X i p l := by
  simp only [AsyncCovers, snoc_intent_async hs]

theorem snoc_memReads_async (hs : e.kind.AsyncSilent) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads (.async i p) a bs ↔ X.MemReads (.async i p) a bs := by
  cases p <;> simp only [Execution.MemReads, snoc_copy hs, snoc_mmaRead hs,
    snoc_tensorIssue hs,snoc_storeIssue hs,snoc_async]
  all_goals rfl

theorem snoc_memWrites_async (hs : e.kind.AsyncSilent) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {bs : List Byte} :
    (X.snoc g e r).MemWrites (.async i p) a bs ↔ X.MemWrites (.async i p) a bs := by
  cases p <;> simp only [Execution.MemWrites, snoc_copy hs,
    snoc_tensorIssue hs,snoc_storeIssue hs,snoc_clcIssue hs,snoc_async]
  all_goals rfl

theorem snoc_memReads (hs : e.kind.AsyncSilent) (hr : ∀ a bs, e.kind ≠ .rd a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    {i : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads i a bs ↔ X.MemReads i a bs := by
  cases i with
  | thread i =>
    exact or_congr (snoc_kind_iff (hr a bs)) (exists_congr fun n => snoc_kind_iff (hrmw a bs n))
  | async i p => exact snoc_memReads_async hs

theorem snoc_memWrites (hs : e.kind.AsyncSilent) (hw : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    {i : AsyncCopy.Ref} {a : Acc} {bs : List Byte} :
    (X.snoc g e r).MemWrites i a bs ↔ X.MemWrites i a bs := by
  cases i with
  | thread i =>
    exact or_congr (snoc_kind_iff (hw a bs))
      (exists_congr fun o => snoc_kind_iff (hrmw a o (some bs)))
  | async i p => exact snoc_memWrites_async hs

theorem snoc_asyncObserved (hs : e.kind.AsyncSilent) {i w : EvId} {p : AsyncCopy.Part}
    {ws : MbarScope} :
    AsyncObserved (X.snoc g e r) i p w true ws ↔ AsyncObserved X i p w true ws := by
  cases p <;> simp only [AsyncObserved, Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
    Notification, snoc_waitObserves hs, snoc_issuedBy hs, snoc_tensorIssue hs, snoc_clcIssue hs,
    snoc_tracksMma hs, snoc_commit hs, snoc_tracksCpAsync hs, snoc_asyncArrive hs, snoc_async]
  all_goals rfl

theorem snoc_asyncFinished (hs : e.kind.AsyncSilent) {i w : EvId} {p : AsyncCopy.Part} :
    AsyncFinished L (X.snoc g e r) i p w ↔ AsyncFinished L X i p w := by
  simp only [AsyncFinished, snoc_asyncObserved hs, snoc_asyncPresent hs, snoc_groupWaitsFor hs,
    snoc_groupWaitStages hs]

/-- A proxy fence appended to thread `g` precedes no old event, so the proxy order into old
events is that of `X`. -/
theorem proxyBefore_snoc_old
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f)) {x i : EvId} {l : Loc}
    (hi : i.2 < (X.tr i.1).length) :
    ProxyBefore L (X.snoc g e r) x i l ↔ ProxyBefore L X x i l := by
  unfold ProxyBefore
  refine exists_congr fun fence => exists_congr fun sp => exists_congr fun scope => ?_
  constructor
  · rintro ⟨⟨pc, hp⟩, h1, h2, h3, h4, h5⟩
    have h5' := (hbo hi).mp h5
    have hfo := (baseCausality_events h5').1
    exact ⟨⟨pc, by rwa [snoc_get_old hfo] at hp⟩, h1, h2, h3, (hbo hfo).mp h4, h5'⟩
  · rintro ⟨⟨pc, hp⟩, h1, h2, h3, h4, h5⟩
    exact ⟨⟨pc, Execution.le_get le_snoc hp⟩, h1, h2, h3, (hbo (len_of_get hp)).mpr h4,
      (hbo hi).mpr h5⟩

theorem modelCausality_snoc_old (hs : e.kind.AsyncSilent)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
    (halloc : ∀ {x f : EvId} {l : Loc}, f.2 < (X.tr f.1).length →
      (Tmem.Pair.AllocResultBefore L (X.snoc g e r) l x f ↔
        Tmem.Pair.AllocResultBefore L X l x f))
    {x f : AsyncCopy.Ref} {l : Loc} (hf : f.issuer.2 < (X.tr f.issuer.1).length) :
    modelCausality L (X.snoc g e r) l x f ↔ modelCausality L X l x f := by
  have hpo {w f : EvId} (hf : f.2 < (X.tr f.1).length) :
      po (X.snoc g e r) w f ↔ po X w f := by
    exact po_snoc_old hf
  have honly : ∀ i p w, AsyncOnlyFinished (X.snoc g e r) i p w ↔
      AsyncOnlyFinished X i p w := by
    intro i p w
    simp only [AsyncOnlyFinished, snoc_asyncPresent hs, snoc_groupWaitsFor hs,
      snoc_groupWaitStages hs]
  have hd : ∀ a b, AsyncBefore L (X.snoc g e r) l a b ↔ AsyncBefore L X l a b := by
    intro a b
    exact AsyncBefore.congr (fun _ _ => snoc_asyncCovers hs)
      (fun _ _ _ => snoc_asyncFinished hs) honly
      (fun _ _ _ hc => hbo hc.issuer_lt) (fun _ _ _ hc => hpo hc.issuer_lt)
  cases x <;> cases f <;> simp only [AsyncCopy.Ref.issuer] at hf <;>
    simp only [modelCausality, snoc_asyncCovers hs, snoc_asyncFinished hs,
      proxyBefore_snoc_old hbo hf, hbo hf, halloc hf, snoc_genericCopy hs,
      observedCompletionBefore_snoc_old (fun _ => snoc_cpIssue hs)
        (fun _ _ _ _ => snoc_mmaIssue hs)
        hf (hbo hf) (proxyBefore_snoc_old hbo hf)]
  have hpt : ∀ k, PairTc (X.snoc g e r) k ↔ PairTc X k := fun _ => by
    simp only [PairTc, snoc_mmaIssue hs, snoc_cpIssue hs]
  simp only [hpt]
  exact and_congr_right fun _ => AsyncChain.congr hd (fun _ _ => snoc_asyncPresent hs)

end Kind.AsyncSilent
end
end
end PTX

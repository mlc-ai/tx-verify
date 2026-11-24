-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocAsync
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Order.Order
public import Lemmas.Tmem.AllocResultDependency

@[expose] public section

/-! Preservation of ordinary/async byte observations when appending a thread event.
All operations are queried by their actual origins; no writer or phase bound is used. -/
namespace PTX
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event}
  {r : Nat → Option AsyncCopy.Ref}

theorem snoc_kind_iff {v : EvId} {k : Kind} (hk : e.kind ≠ k) :
    (∃ pc, (X.snoc g e r).get v = some ⟨pc, k⟩) ↔ ∃ pc, X.get v = some ⟨pc, k⟩ := by
  constructor
  · rintro ⟨pc, hp⟩
    rw [snoc_get] at hp
    split_ifs at hp
    · exact False.elim (hk (congrArg Event.kind (Option.some.inj hp)))
    · exact ⟨pc, hp⟩
  · rintro ⟨pc, hp⟩
    exact ⟨pc, by rw [snoc_get_old (len_of_get hp)]; exact hp⟩

theorem snoc_copy (hk : e.kind.isTma = false) {i : EvId} {s : AsyncCopy.Spec} :
    (X.snoc g e r).Copy i s ↔ X.Copy i s := by
  apply snoc_kind_iff
  intro h; rw [h] at hk; cases hk

theorem snoc_bulkPrefetch (hk : e.kind.isTma = false) {i : EvId} {a : Acc} :
    (X.snoc g e r).BulkPrefetch i a ↔ X.BulkPrefetch i a := by
  apply snoc_kind_iff
  intro h; rw [h] at hk; cases hk

theorem snoc_proxyFence (hk : e.kind.isTma = false) {i : EvId} {k : ProxyFence}
    {scope : Option MbarScope} :
    (X.snoc g e r).IsProxyFence i k scope ↔ X.IsProxyFence i k scope := by
  apply snoc_kind_iff
  intro h; rw [h] at hk; cases hk

theorem snoc_asyncArrive (hk : e.kind.isTma = false) {i : EvId} {m : Loc} {noinc : Bool} :
    (X.snoc g e r).AsyncArrive i m noinc ↔ X.AsyncArrive i m noinc := by
  apply snoc_kind_iff
  intro h; rw [h] at hk; cases hk

theorem snoc_tracksCpAsync (hk : e.kind.isTma = false) {i j : EvId} :
    AsyncCopy.TracksCpAsync (X.snoc g e r) i j ↔ AsyncCopy.TracksCpAsync X i j := by
  simp only [AsyncCopy.TracksCpAsync, snoc_copy hk, snoc_asyncArrive hk]

theorem snoc_genericCopy (hk : e.kind.isTma = false) {i : EvId} :
    GenericCopy (X.snoc g e r) i ↔ GenericCopy X i := by
  simp only [GenericCopy, snoc_copy hk]

theorem snoc_tensorIssue (hk : e.kind.isTma =
    false) {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} :
    (X.snoc g e r).TensorIssue i addr spec ↔ X.TensorIssue i addr spec := by
  apply snoc_kind_iff
  intro he; rw [he] at hk; cases hk

theorem snoc_tensorStoreIssue (hk : e.kind.isTma =
    false) {i : EvId} {addr : Nat} {spec : TensorStore.Spec} :
    (X.snoc g e r).TensorStoreIssue i addr spec ↔ X.TensorStoreIssue i addr spec := by
  apply snoc_kind_iff
  intro he; rw [he] at hk; cases hk

theorem snoc_tensorPrefetchIssue (hk : e.kind.isTma = false) {i : EvId} {addr : Nat}
    {spec : TensorPrefetch.Spec} :
    (X.snoc g e r).TensorPrefetchIssue i addr spec ↔ X.TensorPrefetchIssue i addr spec := by
  apply snoc_kind_iff
  intro he; rw [he] at hk; cases hk

theorem snoc_clcIssue (hk : e.kind.isTma =
    false) {i : EvId} {spec : Clc.Spec} {targets : List Nat} :
    (X.snoc g e r).ClcIssue i spec targets ↔ X.ClcIssue i spec targets := by
  apply snoc_kind_iff
  intro he; rw [he] at hk; cases hk

theorem snoc_intent_async (hk : e.kind.isTma = false) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {w : Bool} : (X.snoc g e r).Intent (.async i p) a w ↔ X.Intent (.async i p) a w := by
  cases p <;> simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
    and_false, snoc_copy hk, snoc_bulkPrefetch hk, Execution.MmaFootprint,
    snoc_mmaIssue (plain_not_tc hk), snoc_cpIssue (plain_not_tc hk),
    snoc_tensorIssue hk,snoc_tensorStoreIssue hk,snoc_tensorPrefetchIssue hk,snoc_clcIssue hk]

theorem snoc_asyncCovers (hk : e.kind.isTma = false) {i : EvId} {p : AsyncCopy.Part} {l : Loc} :
    AsyncCovers (X.snoc g e r) i p l ↔ AsyncCovers X i p l := by
  simp only [AsyncCovers, snoc_intent_async hk]

theorem snoc_memReads_async (hk : e.kind.isTma = false) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads (.async i p) a bs ↔ X.MemReads (.async i p) a bs := by
  cases p <;> simp only [Execution.MemReads, snoc_copy hk, snoc_mmaRead (plain_not_tc hk),
    snoc_tensorIssue hk,snoc_tensorStoreIssue hk,snoc_async]
  all_goals rfl

theorem snoc_memWrites_async (hk : e.kind.isTma = false) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {bs : List Byte} :
    (X.snoc g e r).MemWrites (.async i p) a bs ↔ X.MemWrites (.async i p) a bs := by
  cases p <;> simp only [Execution.MemWrites, snoc_copy hk, snoc_tensorIssue hk,
    snoc_tensorStoreIssue hk, snoc_clcIssue hk, snoc_async]
  all_goals rfl

theorem snoc_memReads (hk : e.kind.isTma = false) (hr : ∀ a bs, e.kind ≠ .rd a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    {i : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads i a bs ↔ X.MemReads i a bs := by
  cases i with
  | thread i =>
    exact or_congr (snoc_kind_iff (hr a bs)) (exists_congr fun n => snoc_kind_iff (hrmw a bs n))
  | async i p => exact snoc_memReads_async hk

theorem snoc_memWrites (hk : e.kind.isTma = false) (hw : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    {i : AsyncCopy.Ref} {a : Acc} {bs : List Byte} :
    (X.snoc g e r).MemWrites i a bs ↔ X.MemWrites i a bs := by
  cases i with
  | thread i =>
    exact or_congr (snoc_kind_iff (hw a bs))
      (exists_congr fun o => snoc_kind_iff (hrmw a o (some bs)))
  | async i p => exact snoc_memWrites_async hk

theorem snoc_asyncObserved (hk : e.kind.isTma = false) {i w : EvId} {p : AsyncCopy.Part}
    {acq : Bool} {ws : MbarScope} :
    AsyncCopy.AsyncObserved (X.snoc g e r) i p w acq ws ↔ AsyncCopy.AsyncObserved X i p w acq ws :=
      by
  cases p <;> simp only [AsyncCopy.AsyncObserved, AsyncCopy.Notifies, AsyncCopy.Part.target,
    AsyncCopy.NotifyOn, AsyncCopy.Notification,
    snoc_waitObserves hk, snoc_issuedBy hk, snoc_tensorIssue hk, snoc_clcIssue hk,
    snoc_tracksMma hk, snoc_commit (plain_not_tc hk), snoc_tracksCpAsync hk, snoc_asyncArrive hk,
    snoc_async]
  all_goals rfl

theorem snoc_asyncGroupWaits (hk : e.kind.isTma = false) {i w : EvId} :
    AsyncGroupWaitsFor (X.snoc g e r) i w ↔ AsyncGroupWaitsFor X i w := by
  have old {pc n : Nat} (hp : (X.snoc g e r).get w = some ⟨pc, .asyncWait n⟩) :
      X.get w = some ⟨pc, .asyncWait n⟩ := by
    rw [snoc_get] at hp
    split_ifs at hp
    · have he := congrArg Event.kind (Option.some.inj hp)
      rw [he] at hk
      cases hk
    · exact hp
  constructor
  · rintro ⟨pc, n, hp, hs⟩
    have hp' := old hp
    refine ⟨pc, n, hp', ?_⟩
    simpa only [asyncStateBefore, snoc_take (len_of_get hp').le] using hs
  · rintro ⟨pc, n, hp, hs⟩
    refine ⟨pc, n, Execution.le_get le_snoc hp, ?_⟩
    simpa only [asyncStateBefore, snoc_take (len_of_get hp).le] using hs

theorem snoc_groupWaitsFor (hk : e.kind.isTma = false) {k : GroupWait} {i w : EvId} :
    GroupWaitsFor (X.snoc g e r) k i w ↔ GroupWaitsFor X k i w := by
  cases k with
  | bulk mode => exact snoc_bulkWaits (fun mode n he => by rw [he] at hk; cases hk)
  | cpAsync => exact snoc_asyncGroupWaits hk

theorem snoc_groupWaitStages (hk : e.kind.isTma = false) {i : EvId} {k : GroupWait} :
    GroupWaitStages (X.snoc g e r) i k = GroupWaitStages X i k := by
  unfold GroupWaitStages
  rw [snoc_get]
  split_ifs with hi
  · have hn : X.get i = none := by rw [hi]; exact List.getElem?_eq_none (le_refl _)
    rw [hn]
    obtain ⟨pc, kind⟩ := e
    cases kind <;> cases k <;> simp_all [Kind.isTma] <;> (rename_i mode; cases mode <;> rfl)
  · rfl

theorem snoc_asyncFinished (hk : e.kind.isTma = false) {i w : EvId} {p : AsyncCopy.Part} :
    AsyncFinished L (X.snoc g e r) i p w ↔ AsyncFinished L X i p w := by
  simp only [AsyncFinished, snoc_asyncObserved hk, snoc_asyncPresent hk, snoc_groupWaitsFor hk,
    snoc_groupWaitStages hk]

theorem proxyBefore_snoc_old (hk : e.kind.isTma = false)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f)) {x i : EvId} {l : Loc}
    (hi : i.2 < (X.tr i.1).length) :
    ProxyBefore L (X.snoc g e r) x i l ↔ ProxyBefore L X x i l := by
  unfold ProxyBefore
  refine exists_congr fun fence => exists_congr fun sp => exists_congr fun scope => ?_
  constructor
  · rintro ⟨⟨pc, hp⟩, h1, h2, h3, h4, h5⟩
    obtain ⟨pc', hp'⟩ := (snoc_proxyFence hk).mp ⟨pc, hp⟩
    exact ⟨⟨pc', hp'⟩, h1, h2, h3, (hbo (len_of_get hp')).mp h4, (hbo hi).mp h5⟩
  · rintro ⟨⟨pc, hp⟩, h1, h2, h3, h4, h5⟩
    exact ⟨(snoc_proxyFence hk).mpr ⟨pc, hp⟩, h1, h2, h3, (hbo (len_of_get hp)).mpr h4,
      (hbo hi).mpr h5⟩

/-- Appending an event outside the memory model keeps the `cta_group::2` `tcgen05` operations. -/
theorem snoc_pairTc (hk : e.kind.isTma = false) {i : EvId} :
    PairTc (X.snoc g e r) i ↔ PairTc X i := by
  have hm : ∀ d s acc mask, (X.snoc g e r).MmaIssue i d s acc mask ↔
      X.MmaIssue i d s acc mask := fun _ _ _ _ => by
    apply snoc_kind_iff
    intro h; rw [h] at hk; cases hk
  have hc : ∀ c, (X.snoc g e r).CpIssue i c ↔ X.CpIssue i c := fun _ => by
    apply snoc_kind_iff
    intro h; rw [h] at hk; cases hk
  simp only [PairTc, hm, hc]

/-- Executions without tensor-core instructions have only ordinary thread order. -/
theorem Execution.NoTma.modelCausality_thread (hn : X.NoTma) {l : Loc} {i j : EvId} :
    modelCausality L X l (.thread i) (.thread j) ↔ baseCausality L X i j := by
  refine ⟨?_, .inl⟩
  rintro (hb | ⟨_, _, _, _, hr, _, _, _, _⟩)
  · exact hb
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hget, _⟩ := hr
    cases hn _ _ _ hget

/-- An old load's allocation result was already present when its allocation returned. -/
theorem snoc_allocResultBefore_old (hready : ∀ i, Returned X i → Ready L X i)
    {x f : EvId} {l : Loc} (hf : f.2 < (X.tr f.1).length) :
    Tmem.Pair.AllocResultBefore L (X.snoc g e r) l x f ↔
      Tmem.Pair.AllocResultBefore L X l x f := by
  refine ⟨fun h => h.of_prefix le_snoc ?_ hf, fun h => h.mono le_snoc⟩
  exact h.store_present_of_load_prefix le_snoc hf hready
    (fun i _ _ _ _ he hl => allocResult_witnessed L X i he hl)

/-- An appended non-write cannot supply a new allocation result store. -/
theorem snoc_allocResultBefore_old_of_not_write (hnw : ∀ a bs, e.kind ≠ .wr a bs)
    {x f : EvId} {l : Loc} (hf : f.2 < (X.tr f.1).length) :
    Tmem.Pair.AllocResultBefore L (X.snoc g e r) l x f ↔
      Tmem.Pair.AllocResultBefore L X l x f := by
  refine ⟨fun h => h.of_prefix le_snoc ?_ hf, fun h => h.mono le_snoc⟩
  obtain ⟨_, _, _, _, hr, _, _, _, _⟩ := h
  obtain ⟨_, _, hstore⟩ := hr.writes
  rw [snoc_get] at hstore
  split_ifs at hstore
  · exact (hnw _ _ (congrArg Event.kind (Option.some.inj hstore))).elim
  · exact len_of_get hstore

/-- An old destination retains its completion paths when the append preserves Tensor Core issues. -/
theorem observedCompletionBefore_snoc_old {l : Loc} {i w f : EvId} {p : AsyncCopy.Part}
    (hcopy : ∀ s, (X.snoc g e r).CpIssue i s ↔ X.CpIssue i s)
    (hmma : ∀ d s acc mask, (X.snoc g e r).MmaIssue i d s acc mask ↔ X.MmaIssue i d s acc mask)
    (hf : f.2 < (X.tr f.1).length)
    (hb : baseCausality L (X.snoc g e r) w f ↔ baseCausality L X w f)
    (hp : ProxyBefore L (X.snoc g e r) w f l ↔ ProxyBefore L X w f l) :
    ObservedCompletionBefore L (X.snoc g e r) l i p w f ↔
      ObservedCompletionBefore L X l i p w f := by
  refine or_congr (by cases p <;> first | exact hb | exact hp) ?_
  cases p <;> try rfl
  simp only [TcReadReuseBefore, hcopy, hmma, hb, Execution.Writes, snoc_get_old hf]

theorem modelCausality_snoc_old (hk : e.kind.isTma = false)
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
    simp only [AsyncOnlyFinished, snoc_asyncPresent hk, snoc_groupWaitsFor hk,
      snoc_groupWaitStages hk]
  have hd : ∀ a b, AsyncBefore L (X.snoc g e r) l a b ↔ AsyncBefore L X l a b := by
    intro a b
    exact AsyncBefore.congr (fun _ _ => snoc_asyncCovers hk)
      (fun _ _ _ => snoc_asyncFinished hk) honly
      (fun _ _ _ hc => hbo hc.issuer_lt) (fun _ _ _ hc => hpo hc.issuer_lt)
  cases x <;> cases f <;> simp only [AsyncCopy.Ref.issuer] at hf <;>
    simp only [modelCausality, snoc_asyncCovers hk, snoc_asyncFinished hk,
      proxyBefore_snoc_old hk hbo hf, hbo hf, halloc hf, snoc_genericCopy hk, snoc_pairTc hk,
      observedCompletionBefore_snoc_old (fun _ => snoc_cpIssue (plain_not_tc hk))
        (fun _ _ _ _ => snoc_mmaIssue (plain_not_tc hk))
        hf (hbo hf) (proxyBefore_snoc_old hk hbo hf)]
  exact and_congr_right fun _ => AsyncChain.congr hd (fun _ _ => snoc_asyncPresent hk)

theorem refPresent_issuer_lt (ht : EffectValidity L X) {f : AsyncCopy.Ref} (hf : X.RefPresent f) :
    f.issuer.2 < (X.tr f.issuer.1).length := by
  cases f with
  | thread i => obtain ⟨ev, he⟩ := hf; exact len_of_get he
  | async i p => obtain ⟨ev, he⟩ := asyncPresent_issuer ht hf; exact len_of_get he

/-- A prior read is unchanged by a plain instruction, regardless of its proxy. -/
theorem snoc_memReads_old (hk : e.kind.isTma = false) {v : AsyncCopy.Ref}
    (hn : v ≠ .thread (g, (X.tr g).length)) {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads v a bs ↔ X.MemReads v a bs := by
  cases v with
  | thread i =>
    simp only [Execution.MemReads, Execution.Reads, Execution.Rmw, snoc_get,
      ite_eq_right (fun h => hn (congrArg AsyncCopy.Ref.thread h))]
  | async i p => exact snoc_memReads_async hk

theorem snoc_memWrites_old (hk : e.kind.isTma = false) {v : AsyncCopy.Ref}
    (hn : v ≠ .thread (g, (X.tr g).length)) {a : Acc} {bs : List Byte} :
    (X.snoc g e r).MemWrites v a bs ↔ X.MemWrites v a bs := by
  cases v with
  | thread i =>
    simp only [Execution.MemWrites, Execution.Writes, Execution.Rmw, snoc_get,
      ite_eq_right (fun h => hn (congrArg AsyncCopy.Ref.thread h))]
  | async i p => exact snoc_memWrites_async hk

theorem snoc_memWrites_lift (hk : e.kind.isTma = false) {v : AsyncCopy.Ref}
    {a : Acc} {bs : List Byte} (hw : X.MemWrites v a bs) :
    (X.snoc g e r).MemWrites v a bs := by
  cases v with
  | thread i =>
    rcases hw with hw | ⟨old, pc, hp⟩
    · exact .inl (snoc_writes_old hw)
    · exact .inr ⟨old, pc, by rw [snoc_get_old (len_of_get hp)]; exact hp⟩
  | async i p => exact (snoc_memWrites_async hk).mpr hw

private theorem no_allocResultBefore_from_new
    (hready : ∀ i, Returned X i → Ready L X i) {f : EvId} {l : Loc} :
    ¬ Tmem.Pair.AllocResultBefore L (X.snoc g e r) l (g, (X.tr g).length) f := by
  intro h
  have hresult := h
  obtain ⟨_, _, _, _, hr, _, _, ⟨_, hread⟩, _⟩ := hresult
  by_cases hf : f = (g, (X.tr g).length)
  · obtain ⟨_, _, hstore⟩ := hr.writes
    rw [hf] at hread
    rw [hread] at hstore
    cases hstore
  · rw [snoc_get, ite_eq_right hf] at hread
    have hp := (snoc_allocResultBefore_old hready (len_of_get hread)).mp h
    obtain ⟨_, _, _, _, hresult, _, _, _, _⟩ := hp
    obtain ⟨_, _, hstore⟩ := hresult.writes
    exact Nat.lt_irrefl _ (len_of_get hstore)

/-- A new ordinary instruction cannot already precede another observation, when no old read reads
from it, it does not read from itself, and every old returned allocation has its result. -/
theorem snoc_no_modelCausality_from_new (hk : e.kind.isTma = false)
    (hold : SnocReadsOld X g e r) (hself : SnocReadsSelf X g e r)
    (hready : ∀ i, Returned X i → Ready L X i) {f : AsyncCopy.Ref} {l : Loc} :
    ¬ modelCausality L (X.snoc g e r) l (.thread (g, (X.tr g).length)) f := by
  intro hv
  cases f with
  | thread i =>
    rcases hv with hb | ha
    · exact snoc_no_baseCausality_from_new hk hold hself hb
    · exact no_allocResultBefore_from_new hready ha
  | async i p =>
    rcases hv.2 with ⟨fence, sp, -, -, -, -, -, hb, -⟩ | ⟨-, hb⟩
    · exact snoc_no_baseCausality_from_new hk hold hself hb
    · exact snoc_no_baseCausality_from_new hk hold hself hb

end
end
end PTX

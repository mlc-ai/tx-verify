-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.PlainExtend
public import Lemmas.Snoc.SnocAsync
public import Lemmas.Tcgen05.TcMmaReadMono

@[expose] public section

/-! Extension lemmas for Tensor Memory instructions. Independent completion flags and
mbarrier histories are retained. Existing observations are preserved because they name
actual older commits, not because an mbarrier is fresh or limited to one phase. -/

namespace PTX
open TcMma (byteInt s32)

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}

theorem snoc_get_cases {v : EvId} {ev : Event} (h : (X.snoc g e r).get v = some ev) :
    (v = (g, (X.tr g).length) ∧ ev = e) ∨ (v.2 < (X.tr v.1).length ∧ X.get v = some ev) := by
  rw [snoc_get] at h
  split_ifs at h with hv
  · exact .inl ⟨hv, (Option.some.inj h).symm⟩
  · exact .inr ⟨len_of_get h, h⟩

theorem snoc_get_of_old {v : EvId} {ev : Event} (h : X.get v = some ev) :
    (X.snoc g e r).get v = some ev := by
  rw [snoc_get_old (len_of_get h)]; exact h

theorem sameWarp_symm {a b : Nat} (h : SameWarp L a b) : SameWarp L b a :=
  ⟨⟨h.1.2.1, h.1.1, h.1.2.2.symm⟩, h.2.symm⟩

/-- Tracking an old commit cannot acquire an MMA appended later in that thread. -/
theorem tracksMma_snoc_old {x c : EvId} (hc : c.2 < (X.tr c.1).length) :
    AsyncCopy.TracksMma (X.snoc g e r) x c ↔ AsyncCopy.TracksMma X x c := by
  constructor
  · rintro ⟨ht, hb, hm, s, hq⟩
    have hx : x.2 < (X.tr x.1).length := by rw [ht]; omega
    refine ⟨ht, hb, ?_, s, ?_⟩
    · simpa only [Execution.TcAsync, Execution.MmaIssue, Execution.CpIssue, Execution.ShiftIssue,
        snoc_get_old hx] using hm
    · simpa only [Execution.Commit, snoc_get_old hc] using hq
  · rintro ⟨ht, hb, hm, s, hq⟩
    have hx : x.2 < (X.tr x.1).length := by rw [ht]; omega
    refine ⟨ht, hb, ?_, s, ?_⟩
    · simpa only [Execution.TcAsync, Execution.MmaIssue, Execution.CpIssue, Execution.ShiftIssue,
        snoc_get_old hx] using hm
    · simpa only [Execution.Commit, snoc_get_old hc] using hq

/-- A preserved notification must already have had a real issuing commit. Appending an
instruction cannot create a notification of that instruction. -/
theorem observesMma_snoc (ht : AsyncCopy.CommitOk X) {x w : EvId} {acq : Bool} {ws : MbarScope}
    (hwold : w.2 < (X.tr w.1).length) :
    AsyncCopy.AsyncObserved (X.snoc g e r) x .mmaDone w acq ws ↔
      AsyncCopy.AsyncObserved X x .mmaDone w acq ws := by
  constructor
  · rintro ⟨n, m, ⟨c, s, rank, rfl, htrack, ⟨pc, hc⟩, htg, hn⟩, ⟨pcw, q, hw⟩, hu⟩
    obtain ⟨⟨_, _, ⟨pc', hc'⟩, _⟩, _⟩ := ht c rank hn
    have hco := len_of_get hc'
    exact ⟨_, m, ⟨c, s, rank, rfl, (tracksMma_snoc_old hco).mp htrack,
      ⟨pc, (snoc_get_old hco).symm.trans hc⟩, htg, hn⟩,
      ⟨pcw, q, (snoc_get_old hwold).symm.trans hw⟩, hu⟩
  · rintro ⟨n, m, ⟨c, s, rank, rfl, htrack, ⟨pc, hc⟩, htg, hn⟩, ⟨pcw, q, hw⟩, hu⟩
    exact ⟨_, m, ⟨c, s, rank, rfl, (tracksMma_snoc_old (len_of_get hc)).mpr htrack,
      ⟨pc, snoc_get_of_old hc⟩, htg, hn⟩, ⟨pcw, q, snoc_get_of_old hw⟩, hu⟩

/-- An update an old wait observed is recorded, so it names an old instruction. -/
theorem update_thread_old (ho : AsyncCopy.ObjectsOk X) {m : Loc} {x : EvId} {w : AsyncCopy.Ref}
    (hu : MBarrier.UpdateBeforeWait (X.objects m) (.thread x) w) : x.2 < (X.tr x.1).length := by
  obtain ⟨i, j, rec, -, -, hi, hid, -⟩ := hu
  have hp := objectAction_present ((ho m).2.1 rec (List.mem_of_getElem? hi)).1
  rw [hid] at hp
  obtain ⟨ev, hx⟩ := hp
  exact len_of_get hx

/-- Appending an instruction adds no mbarrier observation by an old wait. -/
theorem mbarExec_snoc (ho : AsyncCopy.ObjectsOk X) {x w : EvId}
    (hwold : w.2 < (X.tr w.1).length) :
    MbarExec L (X.snoc g e r) x w ↔ MbarExec L X x w := by
  constructor
  · rintro ⟨m, tx, count, rel, rs, acq, ws, ⟨pcx, hx⟩, ⟨⟨pc, q, hw⟩, hu⟩, hsc⟩
    have hxo := update_thread_old ho hu
    exact ⟨m, tx, count, rel, rs, acq, ws, ⟨pcx, (snoc_get_old hxo).symm.trans hx⟩,
      ⟨⟨pc, q, (snoc_get_old hwold).symm.trans hw⟩, hu⟩, hsc⟩
  · rintro ⟨m, tx, count, rel, rs, acq, ws, ⟨pcx, hx⟩, ⟨⟨pc, q, hw⟩, hu⟩, hsc⟩
    exact ⟨m, tx, count, rel, rs, acq, ws, ⟨pcx, snoc_get_of_old hx⟩,
      ⟨⟨pc, q, snoc_get_of_old hw⟩, hu⟩, hsc⟩

/-- Appending one instruction adds no evidence about old events. -/
theorem readPreserved_snoc (ht : AsyncCopy.CommitOk X) (ho : AsyncCopy.ObjectsOk X)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f)) :
    TcMma.ReadPreserved L X (X.snoc g e r) :=
  ⟨le_snoc, hbo, fun hw => observesMma_snoc ht hw, fun _ _ h => h, fun _ _ hr => .inl hr,
    fun hw => mbarExec_snoc ho hw, fun _ hq => .inl hq⟩

/-- Only the TMEM read values of a newly appended load are new obligations. -/
theorem readOk_snoc {A : List Assumption} (h : TcMma.ReadOk L A X) (ht : AsyncCopy.CommitOk X)
    (ho : AsyncCopy.ObjectsOk X)
    (hte : AsyncCopy.TcEffectsOk X)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
    (hld : ∀ pc ta vals sh, e = ⟨pc, .tc (.ld ta vals sh)⟩ → ∀ (j : Nat) source cell value,
      TcMma.LoadCell L (X.snoc g e r) (g, (X.tr g).length) j cell →
      TcMma.ReadSource L (X.snoc g e r) .ld source (g, (X.tr g).length) cell →
      TcMma.Wrote L A (X.snoc g e r) source cell value →
      ∃ word, vals[j]? = some word ∧ TcMma.WordContains value word) :
    TcMma.ReadOk L A (X.snoc g e r) := by
  apply (readPreserved_snoc ht ho hbo).readOk h hte
  intro load address vals sh j source cell value ⟨pc, hp⟩ hc hnew hs hw
  rcases snoc_get_cases hp with ⟨rfl, he⟩ | ⟨hold, _⟩
  · exact hld pc address vals sh he.symm j source cell value hc hs hw
  · omega

/-- Appending an instruction with no new effects preserves the existing TC completions. -/
theorem tcEffectsOk_snoc (ht : AsyncCopy.TcEffectsOk X) :
    AsyncCopy.TcEffectsOk (X.snoc g e r) := by
  refine ⟨?_, ht.2⟩
  intro i hi
  rcases ht.1 i hi with ⟨d,s,accum,mask,operands,⟨pc,hm⟩,hop,hv,ha,hb⟩ |
    ⟨c,operands,⟨pc,hm⟩,hop,ha,hb⟩ | ⟨s,operands,⟨pc,hm⟩,hop,ha,hb⟩
  · exact .inl ⟨d,s,accum,mask,operands,⟨pc,snoc_get_of_old hm⟩,hop,hv,ha,hb⟩
  · exact .inr (.inl ⟨c,operands,⟨pc,snoc_get_of_old hm⟩,hop,ha,hb⟩)
  · exact .inr (.inr ⟨s,operands,⟨pc,snoc_get_of_old hm⟩,hop,ha,hb⟩)

theorem issuedBy_snoc_tc {pc : Nat} {k : TcKind} (he : e = ⟨pc, .tc k⟩) :
    AsyncCopy.issuedBy (X.snoc g e r) = AsyncCopy.issuedBy X := by
  subst he
  funext i
  unfold AsyncCopy.issuedBy
  rw [snoc_get]
  split_ifs with hi
  · subst hi
    rw [show X.get (g, (X.tr g).length) = none from List.getElem?_eq_none (le_refl _)]
  · rfl

/-- TC issue itself is not an mbarrier arrival. Only its separately recorded notification
can perform that arrival; a new issue has no pre-existing notification. -/
theorem objectAction_snoc_tc (hmulti : AsyncCopy.CommitOk X) {pc : Nat} {k : TcKind}
    (he : e = ⟨pc, .tc k⟩) (m : Loc) (id : AsyncCopy.Ref) :
    AsyncCopy.objectAction (X.snoc g e r) X.async m id =
      AsyncCopy.objectAction X X.async m id := by
  have hm : X.tcNotified (g,(X.tr g).length) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rank hr
    obtain ⟨⟨spec,m,⟨pc,hp⟩,_⟩,_⟩ := hmulti _ rank hr
    have hl := len_of_get hp
    simp at hl
  cases id with
  | thread i =>
    subst he
    simp only [AsyncCopy.objectAction]
    rw [snoc_get]
    split_ifs with hi
    · subst hi
      rw [show X.get (g, (X.tr g).length) = none from List.getElem?_eq_none (le_refl _)]
    · rfl
  | async i part =>
    cases part <;> first
      | rfl
      | (simp only [AsyncCopy.objectAction]
         rw [issuedBy_snoc_tc he])
      | (simp only [AsyncCopy.objectAction]
         rw [snoc_get]
         split_ifs with hi
         · subst hi
           rw [show X.get (g, (X.tr g).length) = none from List.getElem?_eq_none (le_refl _)]
           subst he
           cases k <;> simp [hm,Execution.snoc]
         · rfl)

/-- All copy stages and object histories survive a TC issue. -/
theorem tmaOk_snoc_tc (h : TmaOk X) (hmulti : AsyncCopy.CommitOk X) {pc : Nat} {k : TcKind}
    (he : e = ⟨pc, .tc k⟩) :
    TmaOk (X.snoc g e r) := by
  refine ⟨?_, tcEffectsOk_snoc h.2.1, ?_, snoc_arriveOk h.2.2.2⟩
  · simpa only [issuedBy_snoc_tc he, snoc_async] using h.1
  · intro m
    obtain ⟨hv, hm, hc⟩ := h.2.2.1 m
    refine ⟨hv, ?_, ?_⟩
    · intro rec hr
      simpa only [snoc_async, objectAction_snoc_tc hmulti he] using hm rec hr
    · intro id action hid
      apply hc id action
      simpa only [snoc_async, objectAction_snoc_tc hmulti he] using hid

end

end PTX

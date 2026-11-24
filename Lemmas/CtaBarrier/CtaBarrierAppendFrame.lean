-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierHistoryOrder
public import Lemmas.Execution.LegacyExtension
public import Lemmas.CtaBarrier.CtaBarrierReplaceOrder
public import Lemmas.CtaBarrier.CtaBarrierGeneration
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.MBarrier.BarrierWaitingSources
public import Lemmas.Order.DependencyWitness
public import Lemmas.Order.WaitingClosure

@[expose] public section

section
namespace PTX
noncomputable section
variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {c : Nat} {records : List (CtaBarrier.Record EvId)}

/-- Checked extensions of actual CTA arrivals preserve the legacy fragment's
independent effects. -/
theorem effectValidity_withCtaHistory_legacy (hX : Consistent L K A mem0 X) :
    EffectValidity L (X.withCtaHistory c records) :=
  ⟨⟨hX.tma.1,hX.tma.2.1,hX.tma.2.2⟩, hX.tensor,hX.store,hX.clc,hX.tmemPair,hX.tcCommit⟩

/-- A CTA-barrier history adds causality only through its own arrivals, which the caller
shows preserve `hb`; it records no Tensor Memory evidence. -/
theorem readOk_withCtaHistory (hX : Consistent L K A mem0 X) (hp : X.barriers c <+: records)
    (hbo : ∀ e f, baseCausality L (X.withCtaHistory c records) e f ↔ baseCausality L X e f) :
    TcMma.ReadOk L A (X.withCtaHistory c records) := by
  refine (TcMma.ReadPreserved.readOk ⟨X.le_withCtaHistory c hp, fun _ => hbo _ _,
    fun _ => Iff.rfl, fun _ _ h => h, fun _ _ hr => .inl hr, fun _ => Iff.rfl, fun _ hq => .inl hq⟩
    hX.tcRead hX.tma.2.1) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
  have := len_of_get (X := X) hl
  omega

end
end PTX
end

section
/-! # Frame of an appended CTA barrier history

Appending records to one CTA's barrier history (`X.withCtaHistory c (X.barriers c ++ suffix)`)
changes only the CTA barrier relations: the order of logical barrier `(c, id)` gains the issue
nodes of the suffix references, and a rendezvous gains returns of arrivals whose generation the
old history had not completed, which are terminal (`ctaWaits_changed`). So for a node set `S`
holding the suffix issue nodes and the terminal returns of the CTA, every relation of
MEM-OBJECT-ORDER-CAUSALITY between nodes outside `S` is one of `X` (`ctaHistory_append_prim`).
The closedness of `S` under the waiting edges and the frame of the dependency steps stay with the
caller: the needs of a `bar.sync` read its CTA's history, so no other field frames them. -/

namespace PTX
open AsyncCopy
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A barrier arrival that is the last event of its thread. -/
def TerminalBar (X : Execution) (e : EvId) : Prop :=
  (∃ id count pc, X.IsBarrier e id count pc) ∧ e.2 + 1 = (X.tr e.1).length

theorem withCtaHistory_barriers_self (X : Execution) (c : Nat)
    (r : List (CtaBarrier.Record EvId)) :
    (X.withCtaHistory c r).barriers c = r := by
  simp [Execution.withCtaHistory]

theorem withCtaHistory_barriers_ne (X : Execution) {c d : Nat}
    (r : List (CtaBarrier.Record EvId)) (h : d ≠ c) :
    (X.withCtaHistory c r).barriers d = X.barriers d := by
  simp [Execution.withCtaHistory, h]

/-- A completion inside a prefix is a completion of that prefix. -/
theorem completesAt_of_append_left {α : Type} {block i id phase : Nat}
    {xs ys : List (CtaBarrier.Record α)} (hi : i < xs.length)
    (hc : CtaBarrier.CompletesAt block (xs ++ ys) i id phase) :
    CtaBarrier.CompletesAt block xs i id phase := by
  obtain ⟨r, s, t, hi', hs, hr, hphase, hnext⟩ := hc
  refine ⟨r, s, t, ?_, ?_, hr, hphase, hnext⟩
  · rwa [List.getElem?_append_left hi] at hi'
  · unfold CtaBarrier.At at hs ⊢
    rwa [List.take_append_of_le_length hi.le] at hs

/-- A released generation is not a generation that a later state still has to complete. -/
theorem not_released_of_ge {block id g : Nat} {h : List (CtaBarrier.Record EvId)}
    {s : CtaBarrier.State} (hs : CtaBarrier.run block {} h = .ok s)
    (hge : (s.slots id).generation ≤ g) : ¬ CtaBarrier.Released block h id g := by
  intro hd
  have hlt := CtaBarrier.released_generation_lt hs hd
  omega

/-- A key of the extended history is an old key, or belongs to a generation that the old
history has not yet completed. -/
theorem ctaBarK_append_cases {c : Nat} {suffix : List (CtaBarrier.Record EvId)}
    {s : CtaBarrier.State} (hs : CtaBarrier.run L.block {} (X.barriers c) = .ok s)
    {e : EvId} {key : Nat} (hec : e.1 / L.block = c)
    (hk : CtaBarK L (X.withCtaHistory c (X.barriers c ++ suffix)) e key) :
    CtaBarK L X e key ∨ (s.slots (key % 16)).generation ≤ key / 16 := by
  obtain ⟨hlt, ⟨count, pc, hbar⟩, hgen⟩ := hk
  rw [hec, withCtaHistory_barriers_self] at hgen
  rcases CtaBarrier.GenerationOf.append_cases hs hgen with h | h
  · refine .inl ⟨hlt, ⟨count, pc, hbar⟩, ?_⟩
    rw [hec]
    exact h
  · exact .inr h

/-- The same for arrivals of either form. -/
theorem ctaBarArrivalK_append_cases {c : Nat} {suffix : List (CtaBarrier.Record EvId)}
    {s : CtaBarrier.State} (hs : CtaBarrier.run L.block {} (X.barriers c) = .ok s)
    {e : EvId} {key : Nat} (hec : e.1 / L.block = c)
    (hk : CtaBarArrivalK L (X.withCtaHistory c (X.barriers c ++ suffix)) e key) :
    CtaBarArrivalK L X e key ∨ (s.slots (key % 16)).generation ≤ key / 16 := by
  obtain ⟨hlt, ⟨count, pc, hbar⟩, hgen⟩ := hk
  rw [hec, withCtaHistory_barriers_self] at hgen
  rcases CtaBarrier.GenerationOf.append_cases hs hgen with h | h
  · refine .inl ⟨hlt, ⟨count, pc, hbar⟩, ?_⟩
    rw [hec]
    exact h
  · exact .inr h

/-- An arrival whose key generation is still open in `X` is terminal: a later event would
have to be released, and its release would be the open generation itself. -/
theorem terminal_of_not_done (hX : Consistent L K A mem0 X) {c : Nat}
    {records : List (CtaBarrier.Record EvId)} (hp : X.barriers c <+: records)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c records))
    {e : EvId} {key : Nat} (hk : CtaBarK L (X.withCtaHistory c records) e key)
    (hec : e.1 / L.block = c) (hd : ¬ CtaBarDone L X c key) : TerminalBar X e := by
  obtain ⟨count, pc, hbar⟩ := hk.2.1
  refine ⟨⟨_, count, pc, hbar⟩, ?_⟩
  by_contra hne
  have hlt : e.2 + 1 < (X.tr e.1).length := by
    have h1 : e.2 < (X.tr e.1).length := hk.lt
    omega
  obtain ⟨key', hk', hd'⟩ := ctaBarDone_of_returned hX hbar hlt
  have hk'Y : CtaBarK L (X.withCtaHistory c records) e key' :=
    hk'.mono (X.le_withCtaHistory c hp)
  have heq : key = key' := CtaBarK.key_unique hh hk hk'Y
  subst heq
  rw [hec] at hd'
  exact hd hd'

/-- A completion by an appended record is a generation that `X` has not completed. -/
theorem suffix_completes_not_done {c : Nat} {suffix : List (CtaBarrier.Record EvId)}
    {s : CtaBarrier.State} (hs : CtaBarrier.run L.block {} (X.barriers c) = .ok s)
    {i id g : Nat} (hcomp : CtaBarrier.CompletesAt L.block (X.barriers c ++ suffix) i id g)
    (hi : (X.barriers c).length ≤ i) : ¬ CtaBarrier.Released L.block (X.barriers c) id g := by
  rcases CtaBarrier.CompletesAt.append_cases hs hcomp with h | h
  · obtain ⟨_r, _s, _t, hi', -, -, -, -⟩ := h
    have hlt := (List.getElem?_eq_some_iff.mp hi').1
    omega
  · exact not_released_of_ge hs h

/-- Edges of the appended history, classified against the original history. A new edge from a
node of the original history into the suffix lands on an issue node of the suffix, or on the
return node of a terminal arrival of the CTA. Every other edge is an edge of `X`. -/
theorem ctaWaits_changed (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {i j : EvId} {b b' : Bool}
    (hw : CtaBarWaits L (X.withCtaHistory c (X.barriers c ++ suffix)) i j b b') :
    (b' = false ∧ j ∈ suffix.flatMap CtaBarrier.Record.refs) ∨
      (b' = true ∧ TerminalBar X j ∧ j.1 / L.block = c) ∨ CtaBarWaits L X i j b b' := by
  obtain ⟨hpi, hpj, hcase⟩ := hw
  obtain ⟨-, -, s, hs⟩ := hX.ctaBar.2 c hc
  have hpre : X.barriers c <+: X.barriers c ++ suffix := ⟨suffix, rfl⟩
  rcases hcase with ⟨hb, hb', d, i', j', r, q, hr, hq, hij, her, hfq⟩ |
    ⟨hb, hb', hscope, key, hke, hkf⟩ | ⟨hb, hb', key, i', r, hkf, hr, her, hcomp⟩
  · by_cases hdc : d = c
    · rw [hdc, withCtaHistory_barriers_self] at hr hq
      by_cases hj : j' < (X.barriers c).length
      · have hr' : (X.barriers c)[i']? = some r := by
          rwa [List.getElem?_append_left (by omega)] at hr
        have hq' : (X.barriers c)[j']? = some q := by
          rwa [List.getElem?_append_left hj] at hq
        exact .inr (.inr ⟨hpi, hpj, .inl ⟨hb, hb', c, i', j', r, q, hr', hq', hij, her, hfq⟩⟩)
      · have hge : (X.barriers c).length ≤ j' := by omega
        have hqs : q ∈ suffix :=
          List.mem_of_getElem? (by rwa [List.getElem?_append_right hge] at hq)
        exact .inl ⟨hb', List.mem_flatMap.mpr ⟨q, hqs, hfq⟩⟩
    · have hr' : (X.barriers d)[i']? = some r := by
        rwa [withCtaHistory_barriers_ne X _ hdc] at hr
      have hq' : (X.barriers d)[j']? = some q := by
        rwa [withCtaHistory_barriers_ne X _ hdc] at hq
      exact .inr (.inr ⟨hpi, hpj, .inl ⟨hb, hb', d, i', j', r, q, hr', hq', hij, her, hfq⟩⟩)
  · by_cases hcc : i.1 / L.block = c
    · have hjc : j.1 / L.block = c := by rw [← hscope.2.2, hcc]
      by_cases hd : CtaBarDone L X c key
      · have hi' : CtaBarArrivalK L X i key := by
          rcases ctaBarArrivalK_append_cases hs hcc hke with h | h
          · exact h
          · exact absurd hd (not_released_of_ge hs h)
        have hj' : CtaBarK L X j key := by
          rcases ctaBarK_append_cases hs hjc hkf with h | h
          · exact h
          · exact absurd hd (not_released_of_ge hs h)
        exact .inr (.inr ⟨hpi, hpj, .inr (.inl ⟨hb, hb', hscope, key, hi', hj'⟩)⟩)
      · exact .inr (.inl ⟨hb', terminal_of_not_done hX hpre hh hkf hjc hd, hjc⟩)
    · have hi' : CtaBarArrivalK L X i key := (ctaBarArrivalK_withCtaHistory_other hcc).mp hke
      have hjc : ¬ j.1 / L.block = c := by rw [← hscope.2.2]; exact hcc
      have hj' : CtaBarK L X j key := (ctaBarK_withCtaHistory_other hjc).mp hkf
      exact .inr (.inr ⟨hpi, hpj, .inr (.inl ⟨hb, hb', hscope, key, hi', hj'⟩)⟩)
  · by_cases hcc : j.1 / L.block = c
    · rw [hcc, withCtaHistory_barriers_self] at hr hcomp
      by_cases hi' : i' < (X.barriers c).length
      · have hcomp' : CtaBarrier.CompletesAt L.block (X.barriers c) i' (key % 16) (key / 16) :=
          completesAt_of_append_left hi' hcomp
        have hdone : CtaBarrier.Released L.block (X.barriers c) (key % 16) (key / 16) :=
          ⟨i', hcomp'⟩
        have hk' : CtaBarK L X j key := by
          rcases ctaBarK_append_cases hs hcc hkf with h | h
          · exact h
          · exact absurd hdone (not_released_of_ge hs h)
        have hr' : (X.barriers c)[i']? = some r := by
          rwa [List.getElem?_append_left hi'] at hr
        exact .inr (.inr ⟨hpi, hpj, .inr (.inr ⟨hb, hb', key, i', r, hk',
          by rw [hcc]; exact hr', her, by rw [hcc]; exact hcomp'⟩)⟩)
      · have hnd : ¬ CtaBarDone L X c key :=
          suffix_completes_not_done hs hcomp (by omega)
        exact .inr (.inl ⟨hb', terminal_of_not_done hX hpre hh hkf hcc hnd, hcc⟩)
    · have hk' : CtaBarK L X j key := (ctaBarK_withCtaHistory_other hcc).mp hkf
      rw [withCtaHistory_barriers_ne X _ hcc] at hr hcomp
      exact .inr (.inr ⟨hpi, hpj, .inr (.inr ⟨hb, hb', key, i', r, hk', hr, her, hcomp⟩)⟩)

section Frame
variable {c : Nat} {suffix : List (CtaBarrier.Record EvId)}

/-- A warp-instance wait of the appended history — a shuffle instance or a warp-collective
`tcgen05` instance, the two warp-collective disjuncts of `Waits` — is one of `X`: both read the
thread traces, which a CTA barrier history leaves unchanged. -/
theorem rendezvous_withCtaHistory_append {i j : EvId}
    (h : (SameWarp L i.1 j.1 ∧
        ∃ n, (X.withCtaHistory c (X.barriers c ++ suffix)).ShflK i n ∧
          (X.withCtaHistory c (X.barriers c ++ suffix)).ShflK j n) ∨
      (SameWarp L i.1 j.1 ∧
        ∃ k, (X.withCtaHistory c (X.barriers c ++ suffix)).TcK i k ∧
          (X.withCtaHistory c (X.barriers c ++ suffix)).TcK j k)) :
    (SameWarp L i.1 j.1 ∧ ∃ n, X.ShflK i n ∧ X.ShflK j n) ∨
      (SameWarp L i.1 j.1 ∧ ∃ k, X.TcK i k ∧ X.TcK j k) := h

/-- A stage-causality step of the appended history is one of `X`: its stage order and its copy
release read no CTA barrier history, and its base causality is that of `X`
(`baseCausality_withCtaHistory_iff`). -/
theorem stageCausality_withCtaHistory {records : List (CtaBarrier.Record EvId)}
    (hX : Consistent L K A mem0 X) (hp : X.barriers c <+: records)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c records)) {u v : Ref × Bool}
    (h : stageCausality L (X.withCtaHistory c records) u v) : stageCausality L X u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  rcases h with h | ⟨hb, hb', i, j, he, hf, hbc⟩ | ⟨hb, hb', j, hf, hcr⟩
  · exact .inl h
  · exact .inr (.inl ⟨hb, hb', i, j, he, hf,
      (baseCausality_withCtaHistory_iff hX hp hh i j).mp hbc⟩)
  · exact .inr (.inr ⟨hb, hb', j, hf, hcr⟩)

/-- The order of a logical barrier between references outside the suffix is the old one. -/
theorem objectOrder_withCtaHistory_append {o : OrderObject} {u v : Ref × Bool}
    (hv : ∀ j, v = (.thread j, false) → j ∉ suffix.flatMap CtaBarrier.Record.refs)
    (h : ObjectOrder L (X.withCtaHistory c (X.barriers c ++ suffix)) o u v) :
    ObjectOrder L X o u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  cases o with
  | ctaBar d id =>
    obtain ⟨hb, hb', i, j, he, hf, hpi, hpj, k, l, r, q, hr, hq, hkl, hri, hqi, hi, hj⟩ := h
    refine ⟨hb, hb', i, j, he, hf, hpi, hpj, k, l, r, q, ?_, ?_, hkl, hri, hqi, hi, hj⟩
    · by_cases hdc : d = c
      · subst hdc
        rw [withCtaHistory_barriers_self] at hr hq
        have hl : l < (X.barriers d).length := by
          by_contra hn
          rw [List.getElem?_append_right (by omega)] at hq
          exact hv j (by rw [hf, hb']) (List.mem_flatMap.mpr ⟨q, List.mem_of_getElem? hq, hj⟩)
        rwa [List.getElem?_append_left (by omega)] at hr
      · rwa [withCtaHistory_barriers_ne X _ hdc] at hr
    · by_cases hdc : d = c
      · subst hdc
        rw [withCtaHistory_barriers_self] at hq
        have hl : l < (X.barriers d).length := by
          by_contra hn
          rw [List.getElem?_append_right (by omega)] at hq
          exact hv j (by rw [hf, hb']) (List.mem_flatMap.mpr ⟨q, List.mem_of_getElem? hq, hj⟩)
        rwa [List.getElem?_append_left hl] at hq
      · rwa [withCtaHistory_barriers_ne X _ hdc] at hq
  | mbar m => exact h
  | cluster d => exact h
  | tmem d => exact h

/-- **The appended history is a sink frame** for the node set `S`, when `S` holds the issue nodes
of the suffix (`hsuf`), no waiting dependency leaves it (`closed`), and every asynchronous update
whose issue it holds is new and follows that issue (`issue`). Between nodes outside `S` every
relation of MEM-OBJECT-ORDER-CAUSALITY is one of `X`. The dependency steps are the caller's
`dep`: the needs of a `bar.sync` read its CTA's history, so the other fields do not frame them. -/
theorem ctaHistory_append_prim (hX : Consistent L K A mem0 X)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (S : Ref × Bool → Prop)
    (hsuf : ∀ j ∈ suffix.flatMap CtaBarrier.Record.refs, S (.thread j, false))
    (closed : ∃ rank : Ref × Bool → Nat,
      ∀ u v, Waits L (X.withCtaHistory c (X.barriers c ++ suffix)) u v → S u →
        S v ∧ rank u < rank v)
    (issue : ∀ m i p y, MBarrier.Before ((X.withCtaHistory c (X.barriers c ++ suffix)).objects m)
        (.async i p) y → S (.thread i, false) → S (.async i p, true) ∧
        Relation.TransGen (Waits L (X.withCtaHistory c (X.barriers c ++ suffix)))
          (.thread i, false) (.async i p, true))
    (dep : ∀ u v, ¬ S u → ¬ S v →
      DepStep L K (X.withCtaHistory c (X.barriers c ++ suffix)) u v →
        Relation.TransGen (DepStep L K X) u v) :
    SinkFrame L K A X (X.withCtaHistory c (X.barriers c ++ suffix)) S where
  closed := closed
  cause := fun _ _ _ _ h => .single (stageCausality_withCtaHistory hX ⟨suffix, rfl⟩ hh h)
  observed := fun _ _ _ _ h => h
  object := fun _ _ v _ hv h => objectOrder_withCtaHistory_append
    (fun j hj hm => hv (hj ▸ hsuf j hm)) h
  objectSync := by
    have hobj : ∀ (o : OrderObject) (u v : Ref × Bool), ¬ S u → ¬ S v →
        ObjectOrder L (X.withCtaHistory c (X.barriers c ++ suffix)) o u v → ObjectOrder L X o u v :=
      fun o u v hu hv h => objectOrder_withCtaHistory_append
        (fun j hj hm => hv (hj ▸ hsuf j hm)) h
    intro o u v hu hv h
    obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    cases o with
    | mbar m => exact ⟨hobj (.mbar m) (e, b) (f, b') hu hv h.1, h.2⟩
    | ctaBar d id => exact hobj (.ctaBar d id) (e, b) (f, b') hu hv h
    | cluster d => exact hobj (.cluster d) (e, b) (f, b') hu hv h
    | tmem d => exact hobj (.tmem d) (e, b) (f, b') hu hv h
  dep := dep
  issue := issue
  asyncSelf := fun m i p y hb => (hX.asyncObject m i p y hb).1
  asyncObserved := fun _ _ _ _ _ _ h => h
  initFence := by
    intro m init w y hsync hpath hbefore
    exact hX.initFence m init w y hsync
      (Relation.TransGen.mono (fun _ _ h => stageCausality_withCtaHistory hX ⟨suffix, rfl⟩ hh h)
        _ _ hpath) hbefore
  get := fun _ _ => rfl

end Frame

end
end PTX
end

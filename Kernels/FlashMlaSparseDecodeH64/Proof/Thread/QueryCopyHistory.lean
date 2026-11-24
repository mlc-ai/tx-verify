-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmReuseEndpoints
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.Final

@[expose] public section

/-! # The MMA prologue copies all query chunks before committing -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryCopyHistory

open PTX PTX.Flow

private def needsCopy (k : Fin 16) : Wg1Mma.Site → Prop
  | .qCopy j => k.val < j.val
  | .qCopyCommit => True
  | _ => False

set_option maxHeartbeats 1200000 in
private theorem copy_step {P : Params} {L : Launch} {g : Nat} {e : Event}
    {d d' : Wg1Mma.D} {k : Fin 16}
    (h : Wg1Mma.next P L g d e = some (some d')) (hn : needsCopy k d'.site) :
    needsCopy k d.site ∨ d.site = .qCopy k := by
  cases hd : d.site <;> simp only [Wg1Mma.next, hd, Wg1Mma.nextSite] at h
  case qCopy old =>
    split at h
    · cases h
      change k.val < old.val + 1 at hn
      by_cases hEq : old.val = k.val
      · exact .inr (congrArg Wg1Mma.Site.qCopy (Fin.ext hEq))
      · exact .inl (by change k.val < old.val; omega)
    · rename_i hlast
      cases h
      have ho := old.isLt
      have hk := k.isLt
      by_cases hEq : old.val = k.val
      · exact .inr (congrArg Wg1Mma.Site.qCopy (Fin.ext hEq))
      · exact .inl (by change k.val < old.val; omega)
  all_goals repeat' split at h
  all_goals cases h
  all_goals
    try simp only [Wg1Mma.startSite, Wg1Mma.afterTopk] at hn
    repeat' split_ifs at hn
    all_goals simp_all [needsCopy]

private def copyWitness (P : Params) (L : Launch) (g : Nat) (k : Fin 16)
    (es : List Event) : Prop :=
  ∃ j e q o, es[j]? = some e ∧
    (Machine.machine P L g).after (some (.prologue .shfl0)) (es.take j) = some (some (.mma q)) ∧
    q.site = .qCopy k ∧ (Machine.machine P L g).Fired (some (.mma q)) e o

private def copyHistory (P : Params) (L : Launch) (g : Nat) (k : Fin 16)
    (d : Option Machine.ThreadD) (es : List Event) : Prop :=
  (Machine.machine P L g).after (some (.prologue .shfl0)) es = some d ∧
    match d with
    | some (.mma q) => needsCopy k q.site → copyWitness P L g k es
    | _ => True

private theorem copy_witness_append {P : Params} {L : Launch} {g : Nat} {k : Fin 16}
    {es : List Event} {e : Event} (h : copyWitness P L g k es) :
    copyWitness P L g k (es ++ [e]) := by
  obtain ⟨j, f, q, o, hj, hp, hs, hf⟩ := h
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨j, f, q, o, ?_, ?_, hs, hf⟩
  · rwa [List.getElem?_append_left hlt]
  · rwa [List.take_append_of_le_length hlt.le]

private theorem copy_history_step {P : Params} {L : Launch} {g : Nat}
    {d d' : Option Machine.ThreadD} {e : Event} {o : Option TState} {es : List Event}
    {k : Fin 16} (h : copyHistory P L g k d es)
    (hf : (Machine.machine P L g).Fired d e o)
    (hn : (Machine.machine P L g).next d e = some d') :
    copyHistory P L g k d' (es ++ [e]) := by
  refine ⟨?_, ?_⟩
  · rw [Machine.after_snoc (M := Machine.machine P L g) (some (.prologue .shfl0)) es e, h.1]
    exact hn
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue st =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> try trivial
      intro h
      exact h.elim
    case mma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hd
        cases hn
        intro hn
        rcases copy_step hd hn with hp | hsite
        · exact copy_witness_append (h.2 hp)
        · exact ⟨es.length, e, d, o, by simp, by
            rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
            exact h.1, hsite, hf⟩
      · split_ifs at hn <;> cases hn <;> trivial
      · split_ifs at hn
        all_goals cases hn
        all_goals trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- The actual copy site and firing for a given chunk occur before the query commit. -/
theorem query_copy_site_before_commit {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg1Mma.D} {e : Event} (k : Fin 16)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd : d.site = .qCopyCommit) :
    ∃ j f q u, j < i ∧ X.get (g, j) = some f ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ q.site = .qCopy k ∧
      (Machine.machine P L g).Fired (some (.mma q)) f (some u) ∧
      X.CpIssue (g, j) (MmaDataTrace.queryCopySpec L g k) := by
  have hg := Frame.lt_of_get hX he
  have hw := (hs.produces (hX.thr g hg)).prefix_induction (copyHistory P L g k)
    ⟨rfl, trivial⟩ (fun _ _ _ _ _ => copy_history_step) i (some (.mma d)) hst
  obtain ⟨j, f, q, o, hget, hs', hq, hf⟩ := hw.2 (by simp [needsCopy, hd])
  have hj : j < i := ((List.getElem?_eq_some_iff.mp hget).1).trans_le (List.length_take_le _ _)
  have hget' : X.get (g, j) = some f := by
    change (X.tr g)[j]? = some f
    rwa [List.getElem?_take_of_lt hj] at hget
  rw [List.take_take, Nat.min_eq_left hj.le] at hs'
  cases o with
  | none =>
    obtain ⟨_, _, hF⟩ := hf
    obtain ⟨_, hrun⟩ := hX.thr g hg
    have hLen := PTX.Flow.Run.end_last hrun hget' (fires_none_ends hF)
    have hi := PTX.len_of_get he
    change i < (X.tr g).length at hi
    omega
  | some u =>
    have hk := GemmReuseEndpoints.query_copy hpre hg hq hf
    obtain ⟨tag, kind⟩ := f
    exact ⟨j, _, q, u, hj, hget', hs', hq, hf, tag, by rw [hget', ← hk]⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryCopyHistory

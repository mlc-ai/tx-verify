-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CopyFinishVisibility
public import Lemmas.Order.CommitOperandFrame

@[expose] public section

namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {X : Execution} {i : EvId} {bytes : List Byte} {src : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref} {spec : Spec}

theorem finishCopyRecord_reads (hi : issuedBy X i = some spec)
    {e : Ref} {a : Acc} {bs : List (Option Byte)}
    (hr : (X.finishCopyRecord i bytes src mb rec).MemReads e a bs) :
    (e = .async i (.read .copy) ∧ a = spec.src ∧ bs = bytes.map some) ∨ X.MemReads e a bs := by
  cases e with
  | thread j => exact .inr hr
  | async j p =>
    cases p <;> simp only [Execution.MemReads] at hr ⊢
    all_goals try exact Or.inr hr
    · obtain ⟨s, raw, hb, hsa, hraw, rfl⟩ := hr
      by_cases hj : j = i
      · subst j
        have hspec : s = spec := Execution.Copy.unique (X := X) hb (issuedBy_some.mp hi)
        subst s
        have he : raw = bytes := by
          simpa [Execution.finishCopyRecord, Execution.appendObject,
            Execution.finishCopy] using hraw.symm
        exact .inl ⟨rfl, hsa.symm, by rw [he]⟩
      · refine .inr ⟨s, raw, hb, hsa, ?_, rfl⟩
        simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy,
          hj] using hraw
    · obtain ⟨s, r, raw, hb, hw, he, ho, rfl⟩ := hr
      refine .inr ⟨s, r, raw, hb, hw, he, ?_, rfl⟩
      by_cases hj : j = i
      · subst j
        simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy] using ho
      · simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy,
          hj] using ho

theorem finishCopyRecord_writes (hi : issuedBy X i = some spec)
    {e : Ref} {a : Acc} {bs : List Byte}
    (hw : (X.finishCopyRecord i bytes src mb rec).MemWrites e a bs) :
    (e = .async i (.write .copy) ∧ a = spec.dst ∧ bs = bytes) ∨ X.MemWrites e a bs := by
  cases e with
  | thread j => exact .inr hw
  | async j p =>
    cases p <;> simp only [Execution.MemWrites] at hw ⊢
    all_goals try exact Or.inr hw
    · obtain ⟨s, hb, hwh, hd, hraw⟩ := hw
      by_cases hj : j = i
      · subst j
        have hspec : s = spec := Execution.Copy.unique (X := X) hb (issuedBy_some.mp hi)
        subst s
        exact .inl ⟨rfl, hd.symm, by
          simpa [Execution.finishCopyRecord, Execution.appendObject,
            Execution.finishCopy] using hraw.symm⟩
      · refine .inr ⟨s, hb, hwh, hd, ?_⟩
        simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy,
          hj] using hraw
    · obtain ⟨s, hb, he, hraw⟩ := hw
      refine .inr ⟨s, hb, he, ?_⟩
      by_cases hj : j = i
      · subst j
        simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy] using hraw
      · simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy,
          hj] using hraw

/-- W0 supplies the newly completed source read. Existing reads retain both their
values and their original sources, including writes performed by other copies. -/
theorem finishCopyRecord_initial_rf {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    (hle : X.le (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec)) :
    RfWf mem0 (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec) := by
  intro e a bs hr
  rcases finishCopyRecord_reads hi hr with ⟨rfl, rfl, rfl⟩ | hold
  · refine ⟨by simp [initialBytes], ?_⟩
    intro k hk
    simp only [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy]
    rw [ite_eq_left ⟨True.intro, by simpa [initialBytes] using hk⟩]
    intro c hc
    simp [initialBytes, List.getElem?_range hk, hc, Execution.initialByte]
  · obtain ⟨hn, hs⟩ := hX.rf e a bs hold
    refine ⟨hn, ?_⟩
    intro k hk
    rw [hle.2.1 e k ⟨a, bs, hold⟩]
    cases hf : X.rf e k with
    | none =>
      have hh := hs k hk
      simp only [hf] at hh ⊢
      exact hh
    | some w =>
      have hh := hs k hk
      rw [hf] at hh
      obtain ⟨dst, raw, hw, hc, hv⟩ := hh
      exact ⟨dst, raw, Execution.le_memWrites hle hw, hc, hv⟩

theorem finishCopyRecord_initial_noFuture {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    {m : Loc} (hm : spec.completion = .mbarrier m)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    (hle : X.le (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec)) :
    NoFuture L (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec) := by
  have hcopy := issuedBy_some.mp hi
  intro e a bs k w hr hk hf hv
  rcases finishCopyRecord_reads hi hr with ⟨rfl, rfl, rfl⟩ | hold
  · simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy,
      initialBytes, hk] at hf
  · rw [hle.2.1 e k ⟨a, bs, hold⟩] at hf
    exact hX.noFuture e a bs k w hold hk hf
      (ByteCausality.of_same_context (X := X)
        (Y := X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec) rfl rfl
        (fun h => (finishCopyRecord_modelCausality_iff hX.tma.2.2.1 hn hid hcopy hm).mp h)
        (fun h => (finishCopyRecord_asyncObserved_iff hX.tma.2.2.1 hn hid).mp h) hv)

theorem finishCopyRecord_initial_hidden {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    {m : Loc} (hm : spec.completion = .mbarrier m)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k))
    (hle : X.le (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec)) :
    Hidden L (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec) := by
  have hcopy := issuedBy_some.mp hi
  intro e a bs k w target raw hr hk hw hc hv
  have reflect {l e f} :
      ByteCausality L (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec)
        l e f → ByteCausality L X l e f :=
    ByteCausality.of_same_context (X := X)
      (Y := X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec) rfl rfl
      (fun h => (finishCopyRecord_modelCausality_iff hX.tma.2.2.1 hn hid hcopy hm).mp h)
      (fun h => (finishCopyRecord_asyncObserved_iff hX.tma.2.2.1 hn hid).mp h)
  have hv' := reflect hv
  rcases finishCopyRecord_writes hi hw with ⟨rfl, _, _⟩ | hwrite
  · obtain ⟨_, edge⟩ := hv'.starts
    exact (unnotified_copy_write_not_vis hcopy hm hn edge).elim
  rcases finishCopyRecord_reads hi hr with ⟨rfl, rfl, rfl⟩ | hread
  · exact (hsource k hk w target raw hwrite hc).elim
  · rw [hle.2.1 e k ⟨a, bs, hread⟩]
    have hh := hX.hidden e a bs k w target raw hread hk hwrite hc hv'
    cases hf : X.rf e k with
    | none => simp only [hf] at hh
    | some w' =>
      rw [hf] at hh
      intro hvis
      exact hh (reflect hvis)

end
end PTX

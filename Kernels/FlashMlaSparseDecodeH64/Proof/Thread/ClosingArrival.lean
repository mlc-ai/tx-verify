-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate

public section

/-! # The next closing arrival of any participating role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingArrival

open PTX PTX.Flow

private theorem closing_code {P : Params} {L : Launch} {g : Nat} {d : Machine.ThreadD}
    (hs : ScoreClosingGate.ClosingSite d) :
    ∃ a c, kernel.code[(Machine.code P L g).pc d]? =
      some ⟨none, .barSyncN a c false⟩ := by
  cases d
  case wg0 d =>
    change d.site = .everyone at hs
    change ∃ a c, kernel.code[d.site.pc]? = _
    rw [hs]
    exact ⟨_, _, Flow.code_bar_10⟩
  case mma d =>
    change d.site = .outBar at hs
    change ∃ a c, kernel.code[d.site.pc]? = _
    rw [hs]
    exact ⟨_, _, Flow.code_bar_11⟩
  case tma d =>
    change d.site = .barrier at hs
    change ∃ a c, kernel.code[d.site.pc]? = _
    rw [hs]
    exact ⟨_, _, Flow.code_bar_12⟩
  case index d =>
    change d.site = .barrier at hs
    change ∃ a c, kernel.code[d.site.pc]? = _
    rw [hs]
    exact ⟨_, _, Flow.code_bar_13⟩
  case idle s =>
    change s = .sync at hs
    subst s
    exact ⟨_, _, Flow.code_bar_14⟩
  case wg2 d =>
    change d.site = .barrier at hs
    change ∃ a c, kernel.code[d.site.pc]? = _
    rw [hs]
    exact ⟨_, _, Flow.code_bar_15⟩
  all_goals exact hs.elim

private theorem bar_template_cases {L : Launch} {g : Nat} {t : TState} (a c : Opnd) :
    (∃ f, barTmpl L g t a (some c) .sync = .ub f) ∨
      (∃ id count, barTmpl L g t a (some c) .sync = .bar id (PTX.next t) count .sync) := by
  unfold barTmpl
  repeat' split
  all_goals first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, _, rfl⟩

/-- A released lane can take its actual barrier-12 step at any role's closing site. -/
theorem event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hsite : ScoreClosingGate.ClosingSite d) :
    ∃ t t1, Run kernel Assumptions.all L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1 ∧
      EStep kernel Assumptions.all L g t1 ⟨t1.pc, .bar 12 none .sync⟩ (some (PTX.next t1)) := by
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, ins, hLocal, hat, hinv, hc, hout⟩ := Frame.end_at hs hp.1 hRun hd
  obtain ⟨a, c, hcode⟩ := closing_code (P := P) (L := L) (g := g) hsite
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  change out kernel Assumptions.all L g t1 = .ev (barTmpl L g t1 a (some c) .sync) at hout
  have hFired {e : Event} {o : Option TState}
      (h : Fires t1.pc (barTmpl L g t1 a (some c) .sync) e o) :
      (Machine.machine P L g).Fired (some d) e o := by
    refine ⟨t1, ⟨hat, hinv⟩, ?_⟩
    change Fires t1.pc (match kernel.code[(Machine.code P L g).pc d]? with
      | some ins => eventTmpl Assumptions.all L g t1 ins.op
      | none => .ub .pcOutOfRange) e o
    rw [hcode]
    exact h
  rcases bar_template_cases (L := L) (g := g) (t := t1) a c with ⟨f, h⟩ | ⟨id, count, h⟩
  · have hf : Fires t1.pc (barTmpl L g t1 a (some c) .sync) ⟨t1.pc, .ub f⟩ none := by
      rw [h]
      exact ⟨rfl, rfl⟩
    have hNot := ScoreClosingGate.closing_kind hpre (hFired hf) hsite
    cases hNot
  · have hf : Fires t1.pc (barTmpl L g t1 a (some c) .sync) ⟨t1.pc, .bar id count .sync⟩
        (some (PTX.next t1)) := by rw [h]; exact ⟨rfl, rfl⟩
    have hk := ScoreClosingGate.closing_kind hpre (hFired hf) hsite
    obtain ⟨rfl, rfl, _⟩ := Kind.bar.inj hk
    exact ⟨t, t1, hRun, hLocal, _, hout, hf⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingArrival

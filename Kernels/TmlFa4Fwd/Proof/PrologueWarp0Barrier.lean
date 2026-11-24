-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Rounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem recordInitFence {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X)
    {g n : Nat} (hg : g < l.threads) (hn : 0 < n) {t : TState}
    (hCur : InitCursor l X g n t) (hPc : t.pc = 172) (hf : t.fault = none)
    (hReady : n = (X.tr g).length → Step.Released l X g) :
    X.get (g, n) = some ⟨172, .fenceMbarInit⟩ ∧ InitCursor l X g (n + 1) (next t) := by
  obtain ⟨hLen, u, hRun, hTau, o, hRest⟩ := hCur
  have hCode : out kernel [] l g t = .ev (.fenceMbarInit (next t)) := by
    unfold out
    rw [hPc, hf, Flow.code_172]
    rfl
  have hOut := startupOut (A := Assumptions.all) (.inl (by rw [hPc]; decide)) hCode
  let e : Event := ⟨172, .fenceMbarInit⟩
  have hStep : EStep kernel Assumptions.all l g t e (some (next t)) :=
    ⟨_, hOut, by rw [hPc], rfl⟩
  have hLt : n < (X.tr g).length := by
    by_contra hLow
    have hEq : n = (X.tr g).length := by omega
    have hNotEmpty : X.tr g ≠ [] := by intro hNil; rw [hNil, List.length_nil] at hEq; omega
    rw [List.take_of_length_le hEq.ge] at hRun
    apply hMax.not_grows
    exact fenceInitCanIssue hMax.1 hg hNotEmpty (hReady hEq) hRun hTau hStep
  rw [List.drop_eq_getElem_cons hLt] at hRest
  have hNext : Next kernel Assumptions.all l g u t (.fenceMbarInit (next t)) := ⟨hTau, hOut⟩
  obtain ⟨v, ⟨he, hv⟩, hTail⟩ := hNext.continuing_event (by
    rintro ⟨_, h⟩
    cases h) hRest
  obtain rfl := Option.some.inj hv
  have he' : (X.tr g)[n] = e := by rw [he, hPc]
  refine ⟨?_, Nat.succ_le_of_lt hLt, next t, ?_, .refl, o, hTail⟩
  · change (X.tr g)[n]? = _
    rw [List.getElem?_eq_getElem hLt, he']
  · rw [List.take_succ_eq_append_getElem hLt, he']
    exact hRun.snoc hTau hStep

/-- Warp zero records the publication fence and reaches the same CTA barrier as the other
warps. The initializer and fence appends retain visibility at every recorded byte. -/
theorem warp0BarrierArrivesWithHistory {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0) :
    ∃ n, X.get (g, n) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, n + 1) = some ⟨173, .bar 0 none .sync⟩ ∧
      EarlierEvents X g n 172 ∧ InitHistory l X g n 16 := by
  obtain ⟨n, t, hn, hCur, hAt, hPrevious, hReady, hHistory⟩ :=
    warp0InitHistoryAtFence hp hMax hg hw
  have hf := hAt.2.2.2.1
  obtain ⟨he, hAfter⟩ := recordInitFence hMax hg hn hCur hAt.1 hf hReady
  have hPc : (next t).pc = 173 := by change t.pc + 1 = 173; rw [hAt.1]
  have hCode : out kernel [] l g (next t) = .ev (.bar 0 (next (next t)) none .sync) := by
    have hSafe : (next t).fault = none := hf
    unfold out
    rw [hPc, hSafe, Flow.code_173]
    rfl
  have hOut := startupOut (A := Assumptions.all) (.inl (by rw [hPc]; decide)) hCode
  obtain ⟨hLen, u, hRun, hTau, o, hRest⟩ := hAfter
  have hLt : n + 1 < (X.tr g).length := by
    by_contra hLow
    have hEq : n + 1 = (X.tr g).length := by omega
    have hNotEmpty : X.tr g ≠ [] := by intro hNil; rw [hNil, List.length_nil] at hEq; omega
    have hReleased := releasedIfLast (l := l) he (by intro h; cases h) hEq
    rw [List.take_of_length_le hEq.ge] at hRun
    have hStep : EStep kernel Assumptions.all l g (next t)
        ⟨(next t).pc, .bar 0 none .sync⟩ (some (next (next t))) := ⟨_, hOut, rfl, rfl⟩
    exact hMax.not_grows (Step.bar_counted_extension hMax.1 hg (.inl hNotEmpty) hReleased
      (fun a ha => Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl) a ha) hRun hTau hStep)
  rw [List.drop_eq_getElem_cons hLt] at hRest
  have hNext : Next kernel Assumptions.all l g u (next t)
      (.bar 0 (next (next t)) none .sync) := ⟨hTau, hOut⟩
  obtain ⟨_, ⟨he', _⟩, _⟩ := hNext.continuing_event (by rintro ⟨_, h⟩; cases h) hRest
  refine ⟨n, he, ?_, hPrevious, hHistory⟩
  change (X.tr g)[n + 1]? = _
  rw [List.getElem?_eq_getElem hLt, he', hPc]

theorem warp0BarrierArrives {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0) :
    ∃ n, X.get (g, n) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, n + 1) = some ⟨173, .bar 0 none .sync⟩ ∧ EarlierEvents X g n 172 := by
  obtain ⟨n, hf, he, hPrev, _⟩ := warp0BarrierArrivesWithHistory hp hMax hg hw
  exact ⟨n, hf, he, hPrev⟩

private theorem initGroupsCover (i : Fin 34) : ∃ j : Fin 16, i ∈ initGroup j := by
  fin_cases i <;> decide

/-- One lane of warp zero initializes every decoded object and then posts the publication
fence and the first common CTA barrier arrival. -/
theorem warp0InitializerRecords {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0) :
    ∃ a n, SameWarp l g a ∧ X.get (a, n) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (a, n + 1) = some ⟨173, .bar 0 none .sync⟩ ∧
      ∀ i : Fin 34, ∃ b < n, X.get (a, b) = some (initEvent l a i) := by
  obtain ⟨leader, hMember, hLeader⟩ :=
    Step.exists_leader hMax.1 (g := g) (electMember_full l g)
  obtain ⟨a, ha, hLane⟩ := warp0LaneWitness hp hg hw hMember.1
  have hWp : warpIndex l a = 0 := ha.2.symm.trans hw
  obtain ⟨n, hf, hb, _, hHistory⟩ :=
    warp0BarrierArrivesWithHistory hp hMax ha.1.2.1 hWp
  refine ⟨a, n, ha, hf, hb, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := initGroupsCover i
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hj
  obtain ⟨ix, inst, tag, _, hElect, hInit⟩ := hHistory j j.isLt
  have hTag : tag = leader := hLeader _ _ _ _ ha hElect
  exact ⟨ix + 1 + b, hInit (hLane.trans hTag.symm) b i hb⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue

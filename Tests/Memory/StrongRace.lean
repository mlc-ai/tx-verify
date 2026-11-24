-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Mathlib.Tactic

/-!
# Morally strong pairs are not data races (§8.7, §8.7.1)

T0 `st.release.cta.shared.u32 [f], 1;` and T1 `ld.acquire.cta.shared.u32 r, [f];` in one CTA, in the
execution where T1's load reads the initial value: the two accesses conflict and are unordered, but
they are morally strong, so the execution has no `Race`. The same execution with a weak store is a
`Race`. -/

namespace PTX.Tests.StrongRace
noncomputable section

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }

private def f : Loc := ⟨.shared, 0, 0⟩
private def b : Byte := (.bits 8 0, 0)
private def ra : Acc := { loc := f, size := 4, acquire := true }

/-- T0 stores to `f` with `wa`; T1's acquire load reads W0 at every byte. -/
private def X (wa : Acc) : Execution where
  tr
    | 0 => [⟨0, .wr wa [b, b, b, b]⟩]
    | 1 => [⟨0, .rd ra [some b, some b, some b, some b]⟩]
    | _ => []
  rf _ _ := none

private def release : Acc := { loc := f, size := 4, release := true }
private def weak : Acc := { loc := f, size := 4 }

private theorem get_cases {wa : Acc} {e : EvId} {ev : Event} (h : (X wa).get e = some ev) :
    (e = (0, 0) ∧ ev = ⟨0, .wr wa [b, b, b, b]⟩) ∨
      (e = (1, 0) ∧ ev = ⟨0, .rd ra [some b, some b, some b, some b]⟩) := by
  obtain ⟨g, k⟩ := e
  rcases g with _ | _ | g <;> rcases k with _ | k <;> simp [Execution.get, X] at h ⊢ <;> simp [h]

private theorem len_le {wa : Acc} (g : Nat) : ((X wa).tr g).length ≤ 1 := by
  rcases g with _ | _ | g <;> simp [X]

private theorem no_fence {wa : Acc} (e : EvId) (sem : FenceSem) (scope : MbarScope) :
    ¬ (X wa).ThreadFence e sem scope := by
  rintro ⟨pc, hp⟩
  obtain ⟨g, k⟩ := e
  rcases g with _ | _ | g <;> rcases k with _ | k <;> simp [Execution.get, X] at hp

private theorem no_base {wa : Acc} (e g : EvId) :
    ¬ (po (X wa) e g ∨ CtaBarSync L (X wa) e g ∨ MSync L (X wa) e g ∨ ClusterSync L (X wa) e g ∨
      WarpBarSync L (X wa) e g ∨ synchronizesWith L (X wa) e g ∨ FenceSync L (X wa) e g) := by
  have hl := len_le (wa := wa) g.1
  rintro (⟨_, h1, h2⟩ | ⟨_, _, _, _, _, _, _, h1, h2⟩ | ⟨_, _, _, _, _, _, _, _, _, _, h1, h2, _⟩ |
    ⟨_, _, _, _, _, _, h1, h2⟩ | ⟨_, _, _, _, h1, h2⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hn, _, _,
      hr⟩ | hfs)
  all_goals first
    | omega
    | (have := hr 0 hn; simp [X] at this)
    | exact not_fenceSync_of_noFence no_fence e g hfs

/-- No causality order relates the two accesses. -/
private theorem no_baseCausality {wa : Acc} (e g : EvId) : ¬ baseCausality L (X wa) e g := by
  intro h
  induction h with
  | single h => exact no_base _ _ h
  | tail _ h _ => exact no_base _ _ h

/-- Hence no visibility order between them. -/
private theorem no_modelOrder {wa : Acc} (e g : EvId) :
    ¬ modelCausality L (X wa) f (.thread e) (.thread g) := by
  rintro (hb | ⟨_, _, _, _, hr, _, _, _, _⟩)
  · exact no_baseCausality _ _ hb
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, halloc, _⟩ := hr
    rcases get_cases halloc with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

private theorem no_order {wa : Acc} (e g : EvId) :
    ¬ ByteCausality L (X wa) f (.thread e) (.thread g) := by
  rw [ByteCausality.direct_iff_of_no_operand]
  · exact no_modelOrder e g
  · rintro i d s accum mask ⟨pc, h⟩
    rcases get_cases h with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  · rintro i c ⟨pc, h⟩
    rcases get_cases h with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h

private theorem conflict (wa : Acc) (hf : wa.loc = f) (hs : wa.size = 4) :
    Conflict (X wa) (.thread (0, 0)) (.thread (1, 0)) wa ra := by
  refine ⟨by simp, true, false, .inr (.inl ⟨[b, b, b, b], ⟨0, rfl⟩, rfl⟩),
    .inl ⟨[some b, some b, some b, some b], ⟨0, rfl⟩, rfl⟩, by simp, f, ?_, ?_⟩ <;>
    simp [Acc.Covers, Loc.InRange, ra, f, hf, hs]

/-- The release store and the acquire load are morally strong. -/
theorem morallyStrong :
    MorallyStrong L (X release) (.thread (0, 0)) (.thread (1, 0)) release ra := by
  refine ⟨.inr ⟨⟨⟨true, .inr (.inl ⟨[b, b, b, b], ⟨0, rfl⟩, rfl⟩)⟩, .inr (.inr rfl), ?_⟩,
    ⟨⟨false, .inl ⟨[some b, some b, some b, some b], ⟨0, rfl⟩, rfl⟩⟩, .inr (.inl rfl), ?_⟩⟩,
    Iff.rfl, release, ra, rfl, rfl, ⟨rfl, rfl⟩⟩
  · simp [MbarScopeIncludes, SameCta, Launch.threads, L, release]
    decide
  · simp [MbarScopeIncludes, SameCta, Launch.threads, L, ra]
    decide

/-- **No race**: the only conflicting pair is morally strong. -/
theorem no_race : ¬ Race L (X release) := by
  rintro ⟨e, g, a, a', l, ⟨hne, we, wg, he, hg, -, -⟩, -, -, hms, -, -⟩
  have hthread : ∀ {r : AsyncCopy.Ref} {c : Acc} {w : Bool}, (X release).Intent r c w →
      ∃ i, r = .thread i ∧ (X release).Access i c w := by
    intro r c w h
    cases r with
    | thread i => exact ⟨i, rfl, h⟩
    | async i p =>
      exfalso
      obtain ⟨g, k⟩ := i
      rcases g with _ | _ | g <;> rcases k with _ | k <;> cases p <;>
        simp [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint, and_false,
          Execution.Copy, Execution.TensorStoreIssue, Execution.TensorIssue,
          Execution.TensorPrefetchIssue,
          Execution.ClcIssue, Execution.BulkPrefetch, Execution.MmaFootprint, Execution.MmaIssue,
          Execution.CpIssue, Execution.get, X] at h
  obtain ⟨i, rfl, hi⟩ := hthread he
  obtain ⟨j, rfl, hj⟩ := hthread hg
  have hacc : ∀ {k : EvId} {c : Acc} {w : Bool}, (X release).Access k c w →
      (k = (0, 0) ∧ c = release ∧ w = true) ∨ (k = (1, 0) ∧ c = ra ∧ w = false) := by
    intro k c w h
    rcases h with ⟨bs, ⟨pc, hp⟩, rfl⟩ | ⟨bs, ⟨pc, hp⟩, rfl⟩ | ⟨old, new, pc, hp⟩ <;>
      rcases get_cases hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h <;> simp
  apply hms
  rcases hacc hi with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hacc hj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact (hne rfl).elim
  · exact morallyStrong
  · refine ⟨.inr ⟨⟨⟨false, .inl ⟨[some b, some b, some b, some b], ⟨0, rfl⟩, rfl⟩⟩,
      .inr (.inl rfl), ?_⟩, ⟨⟨true, .inr (.inl ⟨[b, b, b, b], ⟨0, rfl⟩, rfl⟩)⟩, .inr (.inr rfl),
      ?_⟩⟩, Iff.rfl, ra, release, rfl, rfl, ⟨rfl, rfl⟩⟩
    · simp [MbarScopeIncludes, SameCta, Launch.threads, L, ra]
      decide
    · simp [MbarScopeIncludes, SameCta, Launch.threads, L, release]
      decide
  · exact (hne rfl).elim

/-- With a weak store the same execution is a data race. -/
theorem weak_race : Race L (X weak) := by
  refine ⟨.thread (0, 0), .thread (1, 0), weak, ra, f, conflict weak rfl rfl, ⟨rfl, rfl⟩,
    by simp [Acc.Covers, Loc.InRange, weak, f], ?_, no_order _ _, no_order _ _, ?_⟩
  · rintro ⟨⟨i, j, hi, hj, hij⟩ | ⟨⟨-, hst, -⟩, -⟩, -⟩
    · cases hi; cases hj; simp at hij
    · simp [Acc.Strong, weak] at hst
  · rintro ⟨-, hio, -, -⟩
    rcases hio with ⟨bs, -, hb⟩ | ⟨bs, ⟨pc, hp⟩, -⟩ | ⟨old, new, pc, hp⟩
    · simp at hb
    · rcases get_cases hp with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    · rcases get_cases hp with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h

/-! Tensor reductions (§9.7.10.28.5.4: "Each reduction operation performed by
cp.reduce.async.bulk.tensor has individually .relaxed.gpu memory ordering semantics and are
element-wise atomic."). Two reductions of the same element, from any threads of the launch, are
morally strong, so `Race` cannot report them; a plain tensor store of that element, or a thread
access, is not morally strong with a reduction. -/
section Reductions
variable {L : Launch} {X : Execution} {i j : EvId} {ai aj : Nat} {s t : TensorStore.Spec}
  {x y k x' y' k' : Nat} {loc : Loc} {a b : Acc}

/-- A tensor store is not a generic-proxy linear operation: it performs no copy. -/
private theorem not_genericCopy_of_tensorStore {i : EvId} {addr : Nat} {s : TensorStore.Spec}
    (h : X.TensorStoreIssue i addr s) : ¬ GenericCopy X i := by
  obtain ⟨pc, hp⟩ := h
  rintro ⟨s', ⟨pc', hp'⟩, -⟩
  rw [hp] at hp'
  cases hp'

theorem reductions_morallyStrong (hi : X.TensorStoreIssue i ai s) (hj : X.TensorStoreIssue j aj t)
    {op op' : AtomOp} (hs : s.reduce = some op) (ht : t.reduce = some op')
    (hgi : i.1 < L.threads) (hgj : j.1 < L.threads)
    (hl : TensorStore.writeLoc s x y 0 = some loc) (hl' : TensorStore.writeLoc t x' y' 0 = some loc)
    (hb : s.descriptor.format.bytes = t.descriptor.format.bytes) :
    MorallyStrong L X (.async i (.write (.store x y k)))
      (.async j (.write (.store x' y' k'))) a b :=
  ⟨.inr ⟨⟨⟨ai, s, op, hi, hs⟩, hgi, hgj⟩, ⟨⟨aj, t, op', hj, ht⟩, hgj, hgi⟩⟩,
    ⟨fun h => absurd h (not_genericCopy_of_tensorStore hi),
      fun h => absurd h (not_genericCopy_of_tensorStore hj)⟩, _, _,
    ⟨ai, s, op, loc, hi, hs, hl, rfl⟩, ⟨aj, t, op', loc, hj, ht, hl', rfl⟩, ⟨rfl, hb⟩⟩

theorem store_reduction_not_morallyStrong (hi : X.TensorStoreIssue i ai s) (hs : s.reduce = none) :
    ¬ MorallyStrong L X (.async i (.write (.store x y k)))
      (.async j (.write (.store x' y' k'))) a b := by
  rintro ⟨⟨_, _, h, -⟩ | ⟨⟨⟨ai', s', op, hi', hs'⟩, -⟩, -⟩, -⟩
  · cases h
  · obtain ⟨pc, hp⟩ := hi
    obtain ⟨pc', hp'⟩ := hi'
    rw [hp] at hp'
    cases hp'
    rw [hs] at hs'
    cases hs'

theorem thread_reduction_not_morallyStrong {e : EvId} :
    ¬ MorallyStrong L X (.thread e) (.async j (.write (.store x' y' k'))) a b := by
  rintro ⟨-, hg, -, -, -, ⟨addr, s, red, loc, hj, -, -, -⟩, -⟩
  exact not_genericCopy_of_tensorStore hj (hg.mp trivial)

end Reductions

end
end PTX.Tests.StrongRace

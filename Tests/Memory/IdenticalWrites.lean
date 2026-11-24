-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Mathlib.Tactic

/-!
# Identical-value writes are not a race (ERR-DATA-RACE)

T0 `st.shared.u8 [f], b;` and T1 `st.shared.u8 [f], v;` in one CTA, with no synchronization: the
two writes conflict and are unordered. A uniform-size race that §8.7.2 describes ("But these
axioms are sufficient to describe the behavior of a PTX program with only uniform-size
data-races ."): (a) when `v = b` the pair writes the same bytes with the same value
(`SameValueWrites`) and the execution has no `Race`; (b) when `v ≠ b` it is a `Race`; (c) with
`v = b`, an unordered `ld.shared.u8` of `f` by T2 is still a `Race` with T0's write; (d) a
two-byte store by T1 that overlaps T0's byte partially, with the same byte values, is `Mixed`.
-/

namespace PTX.Tests.IdenticalWrites
noncomputable section

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }

private def f : Loc := ⟨.shared, 0, 0⟩
private def b : Byte := (.bits 8 0, 0)
private def c : Byte := (.bits 8 1, 0)
private def byte : Acc := { loc := f, size := 1 }
private def half : Acc := { loc := f, size := 2 }

/-- T0 writes `b` to `f`; T1 writes `bs` with footprint `a1`; T2 performs `tail`. -/
private def X (a1 : Acc) (bs : List Byte) (tail : List Event) : Execution where
  tr
    | 0 => [⟨0, .wr byte [b]⟩]
    | 1 => [⟨0, .wr a1 bs⟩]
    | 2 => tail
    | _ => []
  rf _ _ := none

private def rd : List Event := [⟨0, .rd byte [some b]⟩]

private theorem len_le {a1 : Acc} {bs : List Byte} {tail : List Event} (ht : tail.length ≤ 1)
    (g : Nat) : ((X a1 bs tail).tr g).length ≤ 1 := by
  rcases g with _ | _ | _ | g <;> simp [X, ht]

private theorem no_base {a1 : Acc} {bs : List Byte} {tail : List Event}
    (ht : tail = [] ∨ tail = rd) (e g : EvId) :
    ¬ (po (X a1 bs tail) e g ∨ CtaBarSync L (X a1 bs tail) e g ∨ MSync L (X a1 bs tail) e g ∨
      ClusterSync L (X a1 bs tail) e g ∨ WarpBarSync L (X a1 bs tail) e g ∨
      synchronizesWith L (X a1 bs tail) e g ∨ FenceSync L (X a1 bs tail) e g) := by
  have htl : tail.length ≤ 1 := by rcases ht with rfl | rfl <;> simp [rd]
  have hl := len_le (a1 := a1) (bs := bs) htl g.1
  have hnf : ∀ e sem s, ¬ (X a1 bs tail).ThreadFence e sem s := by
    rintro ⟨g0, k0⟩ sem s ⟨pc, hp⟩
    have hk := len_of_get hp
    have h1 := len_le (a1 := a1) (bs := bs) htl g0
    have hk0 : k0 = 0 := by simp only at hk; omega
    subst hk0
    rcases ht with rfl | rfl <;> rcases g0 with _ | _ | _ | g0 <;> simp_all [X, Execution.get, rd]
  rintro (⟨_, h1, h2⟩ | ⟨_, _, _, _, _, _, _, h1, h2⟩ | ⟨_, _, _, _, _, _, _, _, _, _, h1, h2, _⟩ |
    ⟨_, _, _, _, _, _, h1, h2⟩ | ⟨_, _, _, _, h1, h2⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hn, _, _,
      hr⟩ | hf)
  all_goals first
    | exact not_fenceSync_of_noFence hnf _ _ hf
    | omega
    | (have := hr 0 hn; obtain ⟨g0, k0⟩ := e; rcases g0 with _ | _ | _ | g0 <;>
        rcases k0 with _ | k0 <;> simp_all [X, byte])

private theorem no_baseCausality {a1 : Acc} {bs : List Byte} {tail : List Event}
    (ht : tail = [] ∨ tail = rd)
    (e g : EvId) : ¬ baseCausality L (X a1 bs tail) e g := by
  intro h
  induction h with
  | single h => exact no_base ht _ _ h
  | tail _ h _ => exact no_base ht _ _ h

/-- No causality order relates the single-event traces. -/
private theorem no_modelCausality {a1 : Acc} {bs : List Byte} {tail : List Event}
    (ht : tail = [] ∨ tail = rd) {l : Loc} (e g : EvId) :
    ¬ modelCausality L (X a1 bs tail) l (.thread e) (.thread g) := by
  rintro (hb | ⟨_, _, _, _, hr, _, _, _, _⟩)
  · exact no_baseCausality ht e g hb
  · obtain ⟨_, _, _, _, j, _, _, _, _, _, heq, _, _, _, _, he⟩ := hr
    have hlength : tail.length ≤ 1 := by rcases ht with rfl | rfl <;> simp [rd]
    have hlen := len_le (a1 := a1) (bs := bs) hlength e.1
    have hlt := len_of_get he
    omega

private theorem no_byteCausality {a1 : Acc} {bs : List Byte} {tail : List Event}
    (ht : tail = [] ∨ tail = rd) (e g : EvId) :
    ¬ ByteCausality L (X a1 bs tail) f (.thread e) (.thread g) := by
  rw [ByteCausality.direct_iff_of_no_operand]
  · exact no_modelCausality ht e g
  · rintro ⟨i, k⟩ d s accum mask ⟨pc, h⟩
    rcases ht with rfl | rfl <;> rcases i with _ | _ | _ | i <;> rcases k with _ | k <;>
      simp [Execution.get, X, rd] at h
  · rintro ⟨i, k⟩ c ⟨pc, h⟩
    rcases ht with rfl | rfl <;> rcases i with _ | _ | _ | i <;> rcases k with _ | k <;>
      simp [Execution.get, X, rd] at h

/-- Every access intent is a thread access. -/
private theorem intent_thread {a1 : Acc} {bs : List Byte} {tail : List Event} (ht : tail = [] ∨
    tail = rd) {r : AsyncCopy.Ref} {a : Acc} {w : Bool} (h : (X a1 bs tail).Intent r a w) :
    ∃ i, r = .thread i ∧ (X a1 bs tail).Access i a w := by
  cases r with
  | thread i => exact ⟨i, rfl, h⟩
  | async i p =>
    exfalso
    obtain ⟨g, k⟩ := i
    rcases ht with rfl | rfl <;>
    rcases g with _ | _ | _ | g <;> rcases k with _ | k <;> cases p <;>
      simp [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint, and_false,
        Execution.TensorStoreIssue, Execution.TensorIssue, Execution.TensorPrefetchIssue,
        Execution.ClcIssue, Execution.Copy, Execution.BulkPrefetch,
        Execution.MmaFootprint, Execution.MmaIssue,
        Execution.CpIssue, Execution.get, X, rd] at h

private theorem w0 : (X byte [b] []).Writes (0, 0) byte [b] := ⟨0, rfl⟩

/-- (a) **No race**: the only conflicting pair writes the same byte with the same value. -/
theorem identical_no_race : ¬ Race L (X byte [b] []) := by
  rintro ⟨e, g, a, a', l, ⟨hne, we, wg, he, hg, -, -⟩, -, -, -, -, -, hsv⟩
  obtain ⟨i, rfl, hi⟩ := intent_thread (.inl rfl) he
  obtain ⟨j, rfl, hj⟩ := intent_thread (.inl rfl) hg
  have hacc : ∀ {k : EvId} {a : Acc} {w : Bool}, (X byte [b] []).Access k a w →
      (k = (0, 0) ∨ k = (1, 0)) ∧ a = byte ∧ w = true := by
    intro k a w h
    obtain ⟨g0, k0⟩ := k
    rcases h with ⟨_, ⟨_, hp⟩, rfl⟩ | ⟨_, ⟨_, hp⟩, rfl⟩ | ⟨_, _, _, hp⟩ <;>
      rcases g0 with _ | _ | _ | g0 <;> rcases k0 with _ | k0 <;> simp_all [X, Execution.get]
  obtain ⟨hi', rfl, rfl⟩ := hacc hi
  obtain ⟨hj', rfl, rfl⟩ := hacc hj
  have hw : ∀ {k : EvId} {bs : List Byte}, k = (0, 0) ∨ k = (1, 0) →
      (X byte [b] []).MemWrites (.thread k) byte bs → bs = [b] := by
    rintro k bs (rfl | rfl) (⟨_, hp⟩ | ⟨_, _, hp⟩) <;> simp_all [X, Execution.get]
  exact hsv ⟨he, hg, ⟨rfl, rfl⟩, fun bs bs' h h' => (hw hi' h).trans (hw hj' h').symm⟩

/-- The two stores of `X a1 bs tail` conflict at `f`. -/
private theorem conflict01 {a1 : Acc} {bs : List Byte} {tail : List Event} (hf : a1.loc = f)
    (hs : 0 < a1.size) :
    Conflict (X a1 bs tail) (.thread (0, 0)) (.thread (1, 0)) byte a1 := by
  refine ⟨by simp, true, true, .inr (.inl ⟨[b], ⟨0, rfl⟩, rfl⟩), .inr (.inl ⟨bs, ⟨0, rfl⟩, rfl⟩),
    .inl rfl, f,
    ?_, ?_⟩ <;> simp [Acc.Covers, Loc.InRange, byte, f, hf, hs]

/-- Two weak stores of different threads are not morally strong. -/
private theorem not_strong {a1 : Acc} {bs : List Byte} {tail : List Event} {k : EvId} {a : Acc}
    (hk : k.1 = 1 ∨ k.1 = 2) :
    ¬ MorallyStrong L (X a1 bs tail) (.thread (0, 0)) (.thread k) byte a := by
  rintro ⟨⟨i, j, hi, hj, hij⟩ | ⟨⟨-, hr, -⟩, -⟩, -⟩
  · cases hi; cases hj; simp at hij; omega
  · simp [byte, Acc.Strong] at hr

/-- (b) **Different values race.** -/
theorem different_race : Race L (X byte [c] []) := by
  refine ⟨.thread (0, 0), .thread (1, 0), byte, byte, f, conflict01 rfl (by decide), ⟨rfl, rfl⟩,
    by simp [Acc.Covers, Loc.InRange, byte, f], not_strong (.inl rfl),
    no_byteCausality (.inl rfl) _ _, no_byteCausality (.inl rfl) _ _, ?_⟩
  rintro ⟨-, -, -, hv⟩
  have := hv [b] [c] (.inl ⟨0, rfl⟩) (.inl ⟨0, rfl⟩)
  simp [b, c] at this

/-- (c) **A read unordered with one of two identical writes races with it.** -/
theorem read_race : Race L (X byte [b] rd) := by
  refine ⟨.thread (0, 0), .thread (2, 0), byte, byte, f,
    ⟨by simp, true, false, .inr (.inl ⟨[b], ⟨0, rfl⟩, rfl⟩), .inl ⟨[some b], ⟨0, rfl⟩, rfl⟩,
      .inl rfl, f,
      by simp [Acc.Covers, Loc.InRange, byte, f], by simp [Acc.Covers, Loc.InRange, byte, f]⟩,
    ⟨rfl, rfl⟩, by simp [Acc.Covers, Loc.InRange, byte, f],
    not_strong (.inr rfl), no_byteCausality (.inr rfl) _ _,
    no_byteCausality (.inr rfl) _ _, ?_⟩
  rintro ⟨-, ⟨_, -, hf⟩ | ⟨_, ⟨_, hp⟩, -⟩ | ⟨_, _, _, hp⟩, -⟩
  · cases hf
  · simp [Execution.get, X, rd] at hp
  · simp [Execution.get, X, rd] at hp

/-- (d) **A partial overlap is a mixed-size race**, whatever the bytes. -/
theorem partial_mixed : Mixed L (X half [b, b] []) :=
  ⟨.thread (0, 0), .thread (1, 0), byte, half, f, conflict01 rfl (by decide),
    fun h => absurd h.2 (by decide), by simp [Acc.Covers, Loc.InRange, byte, f],
    by simp [Acc.Covers, Loc.InRange, half, f], no_byteCausality (.inl rfl) _ _,
    no_byteCausality (.inl rfl) _ _⟩

end
end PTX.Tests.IdenticalWrites

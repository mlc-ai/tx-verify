-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Events
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # `copy_ldg`: the values of the reads and writes

The bytes an `nc` read returns are the launch content of `A[g]` (assumption `ncInput`);
they rebuild the element `x g`, so the thread writes `x g` to `B[g]` and no thread faults. -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- The `nc` reads of an execution are the first events of threads below `N`, of `A[g]`. -/
theorem ncreads_cases (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {a : Acc} {bs : List (Option Byte)}
    (h : X.NcReads e a bs) :
    e.1 < L.threads ∧ e.1 < N ∧ e.2 = 0 ∧ a = { loc := gA A e.1, size := 4 } := by
  obtain ⟨pc, hp⟩ := h
  obtain ⟨hg, hc⟩ := event_cases hpre hX ht hp
  rcases hc with ⟨hgN, h0, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ | ⟨he, -⟩ | ⟨-, ⟨f, hf⟩, -⟩
  · simp only [ncE, Event.mk.injEq, Kind.nc.injEq] at he
    exact ⟨hg, hgN, h0, he.2.1⟩
  · simp [wrE] at he
  · simp [exE] at he
  · simp at hf

theorem no_rd (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {a : Acc} {bs : List (Option Byte)} :
    ¬ X.Reads e a bs := by
  rintro ⟨pc, hp⟩
  rcases (event_cases hpre hX ht hp).2 with ⟨-, -, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ |
    ⟨he, -⟩ | ⟨-, ⟨f, hf⟩, -⟩
  · simp [ncE] at he
  · simp [wrE] at he
  · simp [exE] at he
  · simp at hf

theorem no_rmw (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {a : Acc} {old : List (Option Byte)}
    {new : Option (List Byte)} : ¬ X.Rmw e a old new := by
  rintro ⟨pc, hp⟩
  rcases (event_cases hpre hX ht hp).2 with ⟨-, -, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ |
    ⟨he, -⟩ | ⟨-, ⟨f, hf⟩, -⟩
  · simp [ncE] at he
  · simp [wrE] at he
  · simp [exE] at he
  · simp at hf

theorem no_bar (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {id : Nat} {count : Option Nat} {pc : Nat} :
    ¬ X.IsBarrier e id count pc := by
  intro hp
  rcases (event_cases hpre hX ht hp).2 with ⟨-, -, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ |
    ⟨he, -⟩ | ⟨-, ⟨f, hf⟩, -⟩
  · simp [ncE] at he
  · simp [wrE] at he
  · simp [exE] at he
  · simp at hf

/-- The writes of an execution are the second events of threads below `N`, of `B[g]`. -/
theorem writes_cases (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {w : EvId} {a : Acc} {bs : List Byte} (h : X.Writes w a bs) :
    w.1 < L.threads ∧ w.1 < N ∧ w.2 = 1 ∧ a = { loc := gB B w.1, size := 4 } ∧
      ∃ bs0 v, bs0.length = 4 ∧ rebuild 3 bs0 = .ok v ∧
        X.get (w.1, 0) = some (ncE A w.1 bs0) ∧ bs = v.toBytes := by
  obtain ⟨pc, hp⟩ := h
  obtain ⟨hg, hc⟩ := event_cases hpre hX ht hp
  rcases hc with ⟨-, -, bs', -, he⟩ | ⟨hgN, h1, bs0, v, hl, hv, -, h0, he⟩ | ⟨he, -⟩ |
    ⟨-, ⟨f, hf⟩, -⟩
  · simp [ncE] at he
  · simp only [wrE, Event.mk.injEq, Kind.wr.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact ⟨hg, hgN, h1, rfl, bs0, v, hl, hv, h0, rfl⟩
  · simp [exE] at he
  · simp at hf

/-- The `nc` reads of an execution are at the load site, the site of assumption `ncInput`. -/
theorem nc_site (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (h : X.get e = some ⟨pc, .nc a bs⟩) : [12].contains pc = true := by
  obtain ⟨-, hc⟩ := event_cases hpre hX ht h
  rcases hc with ⟨-, -, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ | ⟨he, -⟩ | ⟨-, ⟨f, hf⟩, -⟩
  · simp only [ncE, Event.mk.injEq] at he
    simp [he.1, Flow.load_0]
  · simp [wrE] at he
  · simp [exE] at he
  · simp at hf

/-- What the `nc` read of `A[g]` returns: its launch content (assumption `ncInput`). -/
theorem read_bytes (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {g : Nat} {bs : List (Option Byte)}
    (h : X.NcReads (g, 0) { loc := gA A g, size := 4 } bs) : bs = (x g).toBytes.map some := by
  obtain ⟨-, hgN, -, -⟩ := ncreads_cases hpre hX ht h
  obtain ⟨pc, hp⟩ := h
  obtain ⟨hlen, hsrc⟩ :=
    hX.asm Assumptions.ncInput (by simp) _ _ _ _ hp (nc_site hpre hX ht hp)
  have hat := hpre.atom g hgN
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hb : ((x g).toBytes.map some)[k]? = some (some (x g, k)) := by
      simp [Value.toBytes, hat.1, List.getElem?_range hk, hat.2 k hk]
    rw [hb]
    exact hsrc k hk _ (by simpa [gA, Loc.at, Nat.add_assoc] using hpre.input g hgN k hk)
  · rw [List.getElem?_eq_none (by simp at hlen; omega), List.getElem?_eq_none]
    simp [Value.toBytes, hat.1]; omega

/-- The bytes read rebuild the element of `A`, a four-byte word. -/
theorem read_ok (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {g : Nat} {bs : List (Option Byte)}
    (h : X.NcReads (g, 0) { loc := gA A g, size := 4 } bs) :
    rebuild 3 bs = .ok (x g) ∧ (x g).bytes = 4 := by
  obtain ⟨-, hgN, -, -⟩ := ncreads_cases hpre hX ht h
  have hat := hpre.atom g hgN
  rw [read_bytes hpre hX ht h]
  exact ⟨rebuild_scalar (by omega) (hat.2 0 (by decide)), hat.1⟩

/-- **The value written to `B[g]` is `x g`.** -/
theorem written_value (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {w : EvId} {a : Acc} {bs : List Byte} (h : X.Writes w a bs) :
    w.1 < L.threads ∧ w.1 < N ∧ w.2 = 1 ∧ a = { loc := gB B w.1, size := 4 } ∧
      bs = (x w.1).toBytes := by
  obtain ⟨hg, hgN, h1, ha, bs0, v, hl, hv, h0, rfl⟩ := writes_cases hpre hX ht h
  have hrd : X.NcReads (w.1, 0) { loc := gA A w.1, size := 4 } bs0 := ⟨_, h0⟩
  obtain ⟨hv', -⟩ := read_ok hpre hX ht hrd
  rw [hv] at hv'
  cases hv'
  exact ⟨hg, hgN, h1, ha, rfl⟩

/-- **No thread has undefined behaviour**: the bytes a read returns rebuild a word. -/
theorem no_ub (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {ev : Event} (h : X.get e = some ev) :
    ∀ f, ev.kind ≠ .ub f := by
  intro f hf
  rcases (event_cases hpre hX ht h).2 with ⟨-, -, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ |
    ⟨he, -⟩ | ⟨hgN, -, bs, hl, h0, hbad⟩
  · simp [ncE] at he; rw [he] at hf; cases hf
  · simp [wrE] at he; rw [he] at hf; cases hf
  · simp [exE] at he; rw [he] at hf; cases hf
  · obtain ⟨hv, hb⟩ := read_ok hpre hX ht (g := e.1) (bs := bs) ⟨_, h0⟩
    exact hbad _ hv hb

/-- **A thread below `N` that has exited has written `x g` to `B[g]`.** -/
theorem written_of_exit (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {g : Nat} (hgN : g < N)
    (hexit : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    X.Writes (g, 1) { loc := gB B g, size := 4 } (x g).toBytes := by
  obtain ⟨pc, hl⟩ := hexit
  rw [List.getLast?_eq_getElem?] at hl
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := hl
  rcases (event_cases hpre hX ht hget).2 with ⟨-, -, bs', -, he⟩ | ⟨-, -, bs', v, -, -, -, -, he⟩ |
    ⟨-, ⟨h0, hNg⟩ | ⟨-, -, bs, v, hl4, hv, hb, h0, h1⟩⟩ | ⟨-, ⟨f, hf⟩, -⟩
  · simp [ncE] at he
  · simp [wrE] at he
  · simp only at hNg; omega
  · obtain ⟨hv', -⟩ := read_ok hpre hX ht (g := g) (bs := bs) ⟨_, h0⟩
    rw [hv] at hv'
    cases hv'
    exact ⟨_, h1⟩
  · simp at hf

end
end PTX.Kernels.CopyLdg.Proof

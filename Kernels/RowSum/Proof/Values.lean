-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Events
public import Lemmas.Kernel.Memory

@[expose] public section

/-! # `row_sum`: the bytes read and written

Nothing writes `A`, so every read returns the launch content of its element; every write stores
the sum of its row. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

theorem b32_byte (n : Nat) {k : Nat} (hk : k < 4) : (b32 n).toBytes[k]? = some (b32 n, k) := by
  rw [Value.toBytes, show (b32 n).bytes = 4 from rfl]
  simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some]
  rfl

/-- No event of the kernel is an atomic read-modify-write. -/
theorem no_rmw (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X)
    {e : EvId} {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)} :
    ¬ X.Rmw e a old new := by
  rintro ⟨pc, he⟩
  obtain ⟨-, hc⟩ := event_cases htf hX he
  rcases hc with ⟨-, -, bs, h⟩ | ⟨-, -, d, -, -, h⟩ | h | ⟨_, _, h, -⟩ <;>
    simp [rdE, wrE, exE] at h

/-- **What a read returns**: its launch content, since nothing writes `A`. -/
theorem read_bytes (hpre : Pre L A B M K x mem0) (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) {e : EvId} {a : Acc} {bs : List (Option Byte)}
    (h : X.Reads e a bs) : bs = good x K e.1 e.2 := by
  obtain ⟨hgM, hjK, rfl⟩ := reads_cases htf hX h
  have hlen : bs.length = 4 := hX.read_length (e := .thread e) (Or.inl h)
  have hrow := row_le hgM (show e.2 + 1 ≤ K by omega)
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hb : (good x K e.1 e.2)[k]? = some (some (fl (x (K * e.1 + e.2)), k)) := by
      simp [good, List.getElem?_map, fl_byte _ hk]
    rw [hb]
    refine hX.launch_byte (e := .thread e) (Or.inl h) hk ?_ ?_
    · intro w a' bs' hw hcov
      obtain ⟨w, heRef, hwThread | ⟨old, hrmw⟩⟩ := Execution.NoTma.memWrites_thread
        ((noTma_of_consistent noTma hX).emptyAsync hX) hw
      · subst heRef
        obtain ⟨-, hwM, -, ha'⟩ := writes_cases htf hX hwThread
        subst ha'
        exact covers_gA_gB hpre hgM hjK hwM (Acc.covers_at hk) hcov
      · exact absurd hrmw (no_rmw htf hX)
    · simpa [gA, Loc.at, Nat.add_assoc, fl] using hpre.input (K * e.1 + e.2) (by omega) k hk
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    simp [good]
    rw [show (fl (x (K * e.1 + e.2))).toBytes.length = 4 from rfl]
    omega

/-- **What a write stores**: the row sum. -/
theorem write_bytes (hpre : Pre L A B M K x mem0) (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) {w : EvId} {a : Acc} {bs : List Byte}
    (h : X.Writes w a bs) : bs = (accV x K w.1 K).toBytes := by
  obtain ⟨pc, hp⟩ := h
  obtain ⟨hg, hc⟩ := event_cases htf hX hp
  rcases hc with ⟨-, -, _, he⟩ | ⟨-, hwK, d, hs, hiK, he⟩ | he | ⟨_, _, he, -⟩
  · simp [rdE] at he
  · have hv := htf.value hg hs fun j bs' hj => read_bytes hpre htf hX (e := (w.1, j))
      ⟨Flow.load_0, by unfold rdE at hj; exact hj⟩
    simp only [wrE, Event.mk.injEq, Kind.wr.injEq] at he
    rw [he.2.2, hv, hiK]
  all_goals simp [exE] at he

end
end PTX.Kernels.RowSum.Proof

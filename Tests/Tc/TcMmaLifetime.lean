-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaRead
public import Lemmas.Tmem.TmemRun

namespace PTX.Tests.TcMmaLifetime
open Tmem.Pair
noncomputable section

private def L : Launch :=
  { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def rec (owner base : Nat) : Requests :=
  ⟨⟨owner, 0, fun _ => 0, 0, some ⟨.shared, owner, 0⟩, .alloc 32⟩, .two, .alloc 32 base⟩

-- A CTA-0 issuer can use CTA-1's distinct allocation once its publication is proved.
example (X : Execution) (h : baseCausality L X (32, 0) (0, 2)) :
    Covers L X (rec 1 64) 1 (0, 2) 70 :=
  ⟨32, 64, rfl, rfl, by decide, by decide, .inl h⟩

-- Publication of local columns cannot manufacture peer ownership.
example (X : Execution) : ¬ Covers L X (rec 0 0) 1 (0, 2) 0 := by
  rintro ⟨_, _, _, ho, _⟩
  cases ho

-- Even with the right owner, the peer's base is 64, not the issuer's base 0.
example (X : Execution) : ¬ Covers L X (rec 1 64) 1 (0, 2) 0 := by
  rintro ⟨n, base, ha, _, hb, _⟩
  have he : Tmem.Action.alloc 32 64 = .alloc n base := ha
  cases he
  omega

-- No allocation history means an actual MMA write cannot pass the access check.
example (X : Execution) (empty : ∀ cta, X.tmemHistory cta = [])
    (i : EvId) (cell : TcMma.Cell) (hi : X.MmaCell i cell) :
    AccessUnsafe L X := by
  apply accessUnsafe_of_unallocated (.inl (.inl hi))
  rintro ⟨cta, r, hr, _⟩
  rw [empty] at hr
  cases hr

-- Nor can a load register.
example (X : Execution) (empty : ∀ cta, X.tmemHistory cta = [])
    (e : EvId) (j : Nat) (cell : TcMma.Cell) (hl : TcMma.LoadCell L X e j cell) :
    AccessUnsafe L X := by
  apply accessUnsafe_of_unallocated (.inr (.inl ⟨j, hl⟩))
  rintro ⟨cta, r, hr, _⟩
  rw [empty] at hr
  cases hr

-- Issue-before-release alone cannot replace a completion observation: some delivered commit
-- must track the MMA.
example (X : Execution) (i d : EvId)
    (hn : ∀ c rank, AsyncCopy.TracksMma X i c → rank ∉ X.tcNotified c) :
    ¬ TcMma.DoneBefore L X i d := by
  intro h
  obtain ⟨c, rank, ht, hr⟩ := h.tracked
  exact hn c rank ht hr

-- If an old lifetime has not been replaced, either peer's release requires mmaDone.
example (X : Execution) (hs : AccessSafe L X)
    (hm : AsyncCopy.CommitOk X) (i : EvId) (cell : TcMma.Cell)
    (hi : X.MmaCell i cell) (cta : Nat) (r : Requests)
    (hr : r ∈ X.tmemHistory cta) (hc : Covers L X r cell.cta i cell.column)
    (d : EvId) (hd : ReleaseOf L X r d)
    (hn : ¬ FreshAfter L X d i cell.cta cell.column) :
    X.async.mmaDone i = true := by
  obtain ⟨d', s, a, m, -, -, hmi, -⟩ := id hi
  exact ((TcMma.before_release hs (.inl (.inl hi)) hr hc hd hn).2.2
    (.inl ⟨d', s, a, m, hmi⟩)).done hm

end
end PTX.Tests.TcMmaLifetime

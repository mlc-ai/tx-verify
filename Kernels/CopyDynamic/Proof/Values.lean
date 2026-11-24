-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyDynamic.Proof.Interface
public import Lemmas.Kernel.Memory
public import Lemmas.Execution.NoAsync
public import Lemmas.Order.Order

@[expose] public section

/-! # `copy_dynamic`: the bytes a thread reads

`A` and `B` are disjoint and distinct elements of `B` are disjoint (`covers_A_B`, `covers_B_B`).
Every write is to `B` (`ThreadFacts.writes`), so no write covers a byte of `A`, and the read of
`A[g]` returns its launch content: the bytes of `x g`, which rebuild to `x g`
(`read_value`). -/

namespace PTX.Kernels.CopyDynamic.Proof
open PTX

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- The kernel has no asynchronous instruction. -/
theorem noTma : kernel.NoTma := rfl

/-- No event is a barrier. -/
theorem no_bar (ht : ThreadFacts L A B N X) : ∀ e id count pc, ¬ X.IsBarrier e id count pc :=
  fun _ _ _ _ hb => by
    rcases ht.kinds hb with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h | ⟨_, h⟩ <;> simp at h

/-- `A` and `B` are disjoint. -/
theorem covers_A_B (hpre : Pre L A B N x mem0) {g h : Nat} (hg : g < N) (hh : h < N) {l : Loc}
    (h1 : (accA A g).Covers l) (h2 : (accB B h).Covers l) : False := by
  have := hpre.disjoint
  simp only [Acc.Covers, Loc.InRange, accA, accB] at h1 h2
  omega

/-- Distinct elements of `B` are disjoint. -/
theorem covers_B_B {g h : Nat} {l : Loc} (h1 : (accB B g).Covers l)
    (h2 : (accB B h).Covers l) : g = h := by
  simp only [Acc.Covers, Loc.InRange, accB] at h1 h2
  omega

/-- No event is an atomic read-modify-write. -/
theorem no_rmw (ht : ThreadFacts L A B N X) {e : EvId} {a : Acc} {old : List (Option Byte)}
    {new : Option (List Byte)} : ¬ X.Rmw e a old new := by
  rintro ⟨pc, he⟩
  rcases ht.kinds he with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h | ⟨_, h⟩ <;> simp at h

/-- A write of an execution is a thread's write to `B`. -/
theorem write_B (hX : Consistent L kernel [] mem0 X) (ht : ThreadFacts L A B N X)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs) :
    ∃ g, w = .thread (g, 1) ∧ g < N ∧ a = accB B g ∧
      ∃ rb v v', X.get (g, 0) = some (rdE A g rb) ∧ rebuild 3 rb = .ok v ∧
        storeValue 32 v = .ok v' ∧ bs = v'.toBytes := by
  obtain ⟨⟨g, k⟩, rfl, hw | hrmw⟩ :=
    Execution.NoTma.memWrites_thread ((noTma_of_consistent noTma hX).emptyAsync hX) hw
  · obtain ⟨pc, hw⟩ := hw
    obtain ⟨rfl, hgN, rfl, h⟩ := ht.writes hw
    exact ⟨g, rfl, hgN, rfl, h⟩
  · obtain ⟨old, hrmw⟩ := hrmw
    exact absurd hrmw (no_rmw ht)

/-- **The read of `A[g]` returns the bytes of `x g`**, which rebuild to it. -/
theorem read_value (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A B N X) {g : Nat} {rb : List (Option Byte)}
    (h0 : X.get (g, 0) = some (rdE A g rb)) : rebuild 3 rb = .ok (x g) ∧ (x g).bytes = 4 := by
  obtain ⟨-, hgN, -⟩ := ht.reads h0
  have hr : X.MemReads (.thread (g, 0)) (accA A g) rb := Or.inl ⟨_, h0⟩
  have hat := hpre.atom g hgN
  have hlen := hX.read_length hr
  have hbs : rb = (x g).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hb : ((x g).toBytes.map some)[k]? = some (some (x g, k)) := by
        simp [Value.toBytes, hat.1, List.getElem?_range hk, hat.2 k hk]
      rw [hb]
      refine hX.launch_byte hr hk (fun w a bs hw hc => ?_)
        (by simpa [accA, Loc.at, Nat.add_assoc] using hpre.input g hgN k hk)
      obtain ⟨h, -, hhN, rfl, -⟩ := write_B hX ht hw
      exact covers_A_B hpre hgN hhN (Acc.covers_at hk) hc
    · rw [List.getElem?_eq_none (by simp [accA] at hlen; omega), List.getElem?_eq_none]
      simp [Value.toBytes, hat.1]
      omega
  rw [hbs]
  exact ⟨Proof.rebuild_scalar (by omega) (hat.2 0 (by decide)), hat.1⟩

end

end PTX.Kernels.CopyDynamic.Proof

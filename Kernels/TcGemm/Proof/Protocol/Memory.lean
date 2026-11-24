-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Events

@[expose] public section

/-! # `tc_gemm`: the writes of an execution

The writes are thread 0's store of the address to `tslot`, the threads' stores of their rows of
`D`, and the two bulk copies' writes of `sA` and `sB` (`Wit.memWrites`). So `tslot`, `sA` and
`sB` each have one writer (`Wit.tslot_writer`, `Wit.copyA_writer`, `Wit.copyB_writer`), and no
write reaches the inputs `A` and `B` (`no_write_inputA`, `no_write_inputB`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof AsyncCopy
noncomputable section
variable {L : Launch} {A B D S : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hW : Wit A B D S X P m u)
include hW

theorem Wit.memWrites {w : Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) :
    (w = .thread (0, 1) ∧ dst = { loc := tslot S, size := 4 } ∧ bs = (b32 (P 0).col).toBytes) ∨
    (∃ g < 128, ∃ k < 8, w = .thread (g, ldIdx g (P g) + 2 + k) ∧
      dst = stAcc D g k ∧ bs = stBytes (word (P g).vals k)) ∨
    (w = .async (0, 6) (.write .copy) ∧ dst = { loc := sA S, size := 4096 } ∧
      (X.async.copies (0, 6)).writeBytes = some bs) ∨
    (w = .async (0, 7) (.write .copy) ∧ dst = { loc := sB S, size := 256 } ∧
      (X.async.copies (0, 7)).writeBytes = some bs) := by
  cases w with
  | thread i =>
    obtain ⟨g, j⟩ := i
    rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    swap; · exact (hW.no_rmw he).elim
    obtain ⟨hg, _, hc⟩ := hW.writes he
    rcases hc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, hk, rfl, rfl, rfl⟩
    · exact .inl ⟨rfl, rfl, rfl⟩
    · exact .inr (.inl ⟨g, hg, k, hk, rfl, rfl, rfl⟩)
  | async i p =>
    cases p <;> simp only [Execution.MemWrites] at hw
    case writeCopy =>
      obtain ⟨g, j⟩ := i
      obtain ⟨s, ⟨pc, he⟩, -, rfl, hb⟩ := hw
      obtain ⟨_, _, rfl, hc⟩ := hW.bulk he
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inr (.inl ⟨rfl, rfl, hb⟩))
      · exact .inr (.inr (.inr ⟨rfl, rfl, hb⟩))
    case writeElem k =>
      obtain ⟨s, hc, hk, -⟩ := hw
      obtain ⟨-, hw, -⟩ := hW.copy_spec hc
      simp [Spec.elems, Spec.elemOffsets, hw] at hk
    case writeLoad =>
      obtain ⟨o,addr,b,_,hi,_⟩ := hw
      exact (hW.no_tensor hi).elim
    case writeStore =>
      obtain ⟨o,addr,b,_,hi,_⟩ := hw
      exact (hW.no_tensorStore hi).elim
    case writeCta =>
      obtain ⟨spec,targets,hi,_⟩ := hw
      exact (hW.no_clc hi).elim

/-- Only the address-publication store overlaps a byte of tslot. -/
theorem Wit.tslot_writer {w : Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) {k : Nat} (hk : k < 4)
    (hc : dst.Covers ((tslot S).at k)) :
    w = .thread (0, 1) ∧ dst = { loc := tslot S, size := 4 } ∧ bs = (b32 (P 0).col).toBytes := by
  rcases hW.memWrites hw with h | ⟨g, hg, j, hj, _, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
  · exact h
  all_goals simp [Acc.Covers, Loc.InRange, Loc.at, tslot, stAcc, sA, sB] at hc
  all_goals omega

/-- The two independent copies target disjoint shared buffers. -/
theorem Wit.copyA_writer {w : Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) {k : Nat} (hk : k < 4096)
    (hc : dst.Covers ((sA S).at k)) : w = .async (0, 6) (.write .copy) ∧ dst =
      { loc := sA S, size := 4096 } := by
  rcases hW.memWrites hw with ⟨_, rfl, _⟩ | ⟨g, hg, j, hj, _, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨_, rfl, _⟩
  · simp [Acc.Covers, Loc.InRange, Loc.at, tslot, sA] at hc; omega
  · simp [Acc.Covers, Loc.InRange, Loc.at, stAcc, sA] at hc
  · exact ⟨rfl, rfl⟩
  · simp [Acc.Covers, Loc.InRange, Loc.at, sA, sB] at hc; omega

theorem Wit.copyB_writer {w : Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) {k : Nat} (hk : k < 256)
    (hc : dst.Covers ((sB S).at k)) : w = .async (0, 7) (.write .copy) ∧ dst =
      { loc := sB S, size := 256 } := by
  rcases hW.memWrites hw with ⟨_, rfl, _⟩ | ⟨g, hg, j, hj, _, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨rfl, rfl, _⟩
  · simp [Acc.Covers, Loc.InRange, Loc.at, tslot, sB] at hc; omega
  · simp [Acc.Covers, Loc.InRange, Loc.at, stAcc, sB] at hc
  · simp [Acc.Covers, Loc.InRange, Loc.at, sA, sB] at hc
  · exact ⟨rfl, rfl⟩

end

section
variable (hpre : Pre L A B D a b mem0) (hW : Wit A B D S X P m u)
include hpre hW

theorem no_write_inputA {w : Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) {k : Nat} (hk : k < 4096) : ¬ dst.Covers ((gA A).at k) := by
  intro hc
  rcases hW.memWrites hw with ⟨_, rfl, _⟩ | ⟨g, hg, j, hj, _, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
  all_goals simp only [Acc.Covers, Loc.InRange, Loc.at, gA, stAcc, tslot, sA, sB] at hc
  all_goals try (simp at hc)
  have hd := hpre.disjointA
  omega

theorem no_write_inputB {w : Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) {k : Nat} (hk : k < 256) : ¬ dst.Covers ((gB B).at k) := by
  intro hc
  rcases hW.memWrites hw with ⟨_, rfl, _⟩ | ⟨g, hg, j, hj, _, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
  all_goals simp only [Acc.Covers, Loc.InRange, Loc.at, gB, stAcc, tslot, sA, sB] at hc
  all_goals try (simp at hc)
  have hd := hpre.disjointB
  omega

end
end
end PTX.Kernels.TcGemm.Proof

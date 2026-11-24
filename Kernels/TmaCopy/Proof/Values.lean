-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Protocol.Mbar

@[expose] public section

/-! # `tma_copy`: the values of the copy and of the read

The writes of an execution are thread 0's write of `B` and the bulk copy's write of `buf`
(`memWrites_cases`); none covers the copy's source, so the copy reads the launch content of `A`
and writes its first word to `buf` (`copy_write_byte`). The read of `buf` follows the successful
poll, which observes the copy's completion (`wait_observes_copy`), so it returns the copy's
bytes (`Consistent.read_copy_byte`): the first word of `A` (`read_bytes`). So the write of `B`
writes that word (`written_bytes`), and no thread has undefined behaviour (`no_local_ub`). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof AsyncCopy
noncomputable section
variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}
variable (hpre : Pre L A B x mem0) (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)

section
include ht hX

/-- The writes of an execution: thread 0's write of `B` and the copy's write of `buf`. -/
theorem memWrites_cases {w : Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs) :
    (∃ i, w = .thread i ∧ a = { loc := gB B, size := 4 } ∧ X.Writes i a bs) ∨
    (w = .async (0, 3) (.write .copy) ∧ a = { loc := buf L.sharedBase, size := 16 } ∧
      (X.async.copies (0, 3)).writeBytes = some bs) := by
  cases w with
  | thread i =>
    rcases hw with hw | ⟨old, pc, hp⟩
    · exact .inl ⟨i, rfl, (writes_cases ht hX hw).2.1, hw⟩
    · exact (no_rmw ht hX hp).elim
  | async i p =>
    cases p <;> simp only [Execution.MemWrites] at hw
    case writeCopy =>
      obtain ⟨s, hb, -, rfl, hbytes⟩ := hw
      obtain ⟨rfl, rfl⟩ := bulk_cases ht hX hb
      exact .inr ⟨rfl, rfl, hbytes⟩
    case writeElem j =>
      obtain ⟨s, hb, hj, -⟩ := hw
      obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
      simp [copySpec, bulkSpec, Spec.elems, Spec.elemOffsets] at hj
    case writeLoad x y k =>
      obtain ⟨o, addr, b, _, ⟨pc, hp⟩, _⟩ := hw
      exact (not_class ht hX hp rfl).elim
    case writeStore x y k =>
      obtain ⟨o, addr, b, _, ⟨pc, hp⟩, _⟩ := hw
      exact (not_class ht hX hp rfl).elim
    case writeCta c =>
      obtain ⟨s, targets, ⟨pc, hp⟩, _⟩ := hw
      exact (not_class ht hX hp rfl).elim

/-- A read of `buf` follows a successful poll that observes the copy's completion. -/
theorem read_copy_visible {e : EvId} {a : Acc} {bs : List (Option Byte)}
    (hr : X.Reads e a bs) :
    ∃ w ws, AsyncObserved X (0, 3) (.notify .copy) w true ws ∧
      ScopesMeet L .cluster (0, 3).1 ws w.1 ∧ baseCausality L X w e := by
  obtain ⟨hg, _, i, _, hi, hw, _⟩ := reads_cases ht hX hr
  obtain ⟨ws, ho⟩ := wait_observes_copy ht hX ⟨Flow.mbarWait_0, 0, .cta, hw⟩
  have h0 : 0 < L.threads := by
    by_contra h
    have hl := len_of_get hw
    rw [hX.outside 0 (by omega)] at hl
    simp at hl
  refine ⟨(0, i), ws, ho, .of_sameCta ⟨h0, h0, rfl⟩, ?_⟩
  exact .single (.inl (po_of_source_not_access hg.symm hi (len_of_get hr.choose_spec)
    (by simp [hw, Event.acc, waitE])))

end

include hpre ht hX

/-- No write covers the copy's source. -/
theorem no_write_input {w : Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs)
    {k : Nat} (hk : k < 16) : ¬ a.Covers ((gA A).at k) := by
  rcases memWrites_cases ht hX hw with ⟨i, _, rfl, _⟩ | ⟨_, rfl, _⟩
  · intro hc
    have hd := hpre.disjoint
    simp only [Acc.Covers, Loc.InRange, gB, gA, Loc.at] at hc
    omega
  · simp [Acc.Covers, Loc.InRange, buf, gA, Loc.at]

/-- The copy's read of the first word of `A` returns the word `x`. -/
theorem copy_source_byte {bs : List Byte}
    (hr : X.MemReads (.async (0, 3) (.read .copy)) { loc := gA A, size := 16 } (bs.map some))
    {k : Nat} (hk : k < 4) : bs[k]? = some (x, k) := by
  have hs := (hX.rf _ _ _ hr).2 k (by omega : k < 16)
  cases hrf : X.rf (.async (0, 3) (.read .copy)) k with
  | none =>
    rw [hrf] at hs
    have hb := hs (some (x, k)) (by simpa [gA, Loc.at] using hpre.input k hk)
    simp only [List.getElem?_map, Execution.initialByte, Option.getD_some] at hb
    cases h : bs[k]? with
    | none => simp [h] at hb
    | some b => simpa [h] using hb
  | some w =>
    rw [hrf] at hs
    obtain ⟨a', written, hw, hc, _⟩ := hs
    exact (no_write_input hpre ht hX hw (by omega) hc).elim

/-- The copy writes the word `x` to the first word of `buf`. -/
theorem copy_write_byte {bs : List Byte}
    (hw : X.MemWrites (.async (0, 3) (.write .copy)) { loc := buf L.sharedBase, size := 16 } bs)
    {k : Nat} (hk : k < 4) : bs[k]? = some (x, k) := by
  obtain ⟨s, hb, -, -, hbytes⟩ := hw
  obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
  have hn : nonempty (X.async.copies (0, 3)) := ⟨.write .copy, by simp [present, hbytes]⟩
  obtain ⟨spec, hs, hc⟩ := hX.tma.1 (0, 3) hn
  obtain ⟨pc, hp⟩ := hb
  simp only [issuedBy, hp, Option.some.injEq] at hs
  subst spec
  have hr := ((copyOk_iff_of_size_eq rfl rfl rfl rfl).mp hc).1.2.2.1 bs hbytes
  exact copy_source_byte hpre ht hX ⟨_, bs, ⟨pc, hp⟩, rfl, hr, rfl⟩ hk

/-- **The read of `buf` returns the word `x`.** -/
theorem read_bytes {e : EvId} {a : Acc} {bs : List (Option Byte)}
    (hr : X.Reads e a bs) : bs = x.toBytes.map some := by
  obtain ⟨_, rfl, _⟩ := reads_cases ht hX hr
  obtain ⟨w, ws, ho, hs, hhb⟩ := read_copy_visible ht hX hr
  have hlen := (hX.rf (.thread e) _ _ (.inl hr)).1
  -- the observed copy has written `buf`
  obtain ⟨m, bytes, ⟨spec, hspec, hn, -⟩, -⟩ := ho.copy
  have hb := issuedBy_some.mp hspec
  obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
  obtain ⟨spec', hs', hc⟩ := hX.tma.1 (0, 3) ⟨.notify .copy, by simp [present, hn]⟩
  rw [hspec] at hs'
  cases hs'
  obtain ⟨raw, hraw⟩ := (hc.2.2.2.1 hn).2
  have hwrite : X.MemWrites (.async (0, 3) (.write .copy))
      { loc := buf L.sharedBase, size := 16 } raw := ⟨_, hb, rfl, rfl, hraw⟩
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hcov : ({ loc := buf L.sharedBase, size := 16 } : Acc).Covers ((buf L.sharedBase).at k) :=
      Acc.covers_at (by change k < 16; omega)
    rw [hX.read_copy_byte ho hs hhb hr hk hwrite hcov fun w' a' bs' hw' hc' => by
      rcases memWrites_cases ht hX hw' with ⟨i, _, rfl, _⟩ | ⟨rfl, rfl, _⟩
      · simp [Acc.Covers, Loc.InRange, gB, buf, Loc.at] at hc'
      · rfl]
    have hout : (x.toBytes.map some)[k]? = some (some (x, k)) := by
      simp [Value.toBytes, hpre.atom.1, List.getElem?_range hk, hpre.atom.2 k hk]
    rw [hout]
    simp only [wbyte, Loc.at, Nat.add_sub_cancel_left]
    exact congrArg some (copy_write_byte hpre ht hX hwrite hk)
  · rw [List.getElem?_eq_none (by simp at hlen; omega), List.getElem?_eq_none]
    simp [Value.toBytes, hpre.atom.1]; omega

/-- **The write of `B` writes the word `x`.** -/
theorem written_bytes {e : EvId} {a : Acc} {bs : List Byte}
    (hw : X.Writes e a bs) : bs = x.toBytes := by
  obtain ⟨_, _, raw, v, hr, hv, _, rfl⟩ := writes_cases ht hX hw
  have hraw := read_bytes hpre ht hX (show X.Reads (0, e.2 - 1) _ raw from ⟨Flow.load_0, hr⟩)
  have hrebuild : rebuild 3 (x.toBytes.map some) = .ok x :=
    rebuild_scalar (by have := hpre.atom.1; omega) (hpre.atom.2 0 (by decide))
  rw [hraw, hrebuild] at hv
  cases hv
  rfl

/-- **No thread has undefined behaviour.** -/
theorem no_local_ub : ¬ HasUb X := by
  rintro ⟨e, pc, f, he⟩
  rcases (event_cases ht hX he).2 with ⟨_, heq⟩ | ⟨_, _, heq⟩ | ⟨_, _, heq⟩ |
    ⟨_, _, heq⟩ | ⟨_, _, heq⟩ | ⟨hg, _, _, ⟨ok, heq⟩ | ⟨i, _, _, _, hc⟩⟩
  all_goals try (simp [exE, initE, fenceE, arriveE, bulkE, waitE] at heq)
  rcases hc with ⟨bs, heq⟩ | ⟨_, _, _, _, _, heq⟩ | heq | ⟨pc', f', _, bs, hr, hbad⟩
  all_goals try (simp [rdE, wrE, exE] at heq)
  have hraw := read_bytes hpre ht hX (show X.Reads (0, e.2 - 1) _ bs from ⟨Flow.load_0, hr⟩)
  rw [hraw] at hbad
  exact hbad x (rebuild_scalar (by have := hpre.atom.1; omega)
    (hpre.atom.2 0 (by decide))) hpre.atom.1

end

end PTX.Kernels.TmaCopy.Proof

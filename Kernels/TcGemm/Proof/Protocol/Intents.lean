-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Mma

@[expose] public section

/-! # `tc_gemm`: the access intents of an execution

The writes intended are thread 0's address store, the row stores and the copies' writes of `sA`
and `sB` (`Wit.write_intent`); the reads intended are the address reads, the copies' reads of `A`
and `B`, and the MMA's reads of its operand bytes in `sA` and `sB` (`Wit.read_intent`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof AsyncCopy
noncomputable section

def WriteShape (D S : Nat) (P : Nat → Par) (e : Ref) (dst : Acc) : Prop :=
  (e = .thread (0, 1) ∧ dst = { loc := tslot S, size := 4 }) ∨
  (∃ g < 128, ∃ k < 8, e = .thread (g, ldIdx g (P g) + 2 + k) ∧
    dst = stAcc D g k) ∨
  (e = .async (0, 6) (.write .copy) ∧ dst = { loc := sA S, size := 4096 }) ∨
  (e = .async (0, 7) (.write .copy) ∧ dst = { loc := sB S, size := 256 })

def ReadShape (A B S : Nat) (P : Nat → Par) (e : Ref) (src : Acc) : Prop :=
  (∃ g < 128, e = .thread (g, hd g) ∧ src = { loc := tslot S, size := 4 }) ∨
  (e = .async (0, 6) (.read .copy) ∧ src = { loc := gA A, size := 4096 }) ∨
  (e = .async (0, 7) (.read .copy) ∧ src = { loc := gB B, size := 256 }) ∨
  (∃ k < 4096, ∃ q < 4096, e = .async (0, hd 0 + 2 + (P 0).n0) (.mmaRead false k) ∧
    src.SameFootprint { loc := (sA S).at q, size := 1 }) ∨
  (∃ k < 256, ∃ q < 256, e = .async (0, hd 0 + 2 + (P 0).n0) (.mmaRead true k) ∧
    src.SameFootprint { loc := (sB S).at q, size := 1 })

variable {A B D S : Nat} {X : Execution} {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
variable (hW : Wit A B D S X P m u)
include hW

theorem Wit.write_intent {e : Ref} {dst : Acc} (he : X.Intent e dst true) : WriteShape D S P e dst
    := by
  cases e with
  | thread i =>
    obtain ⟨g, j⟩ := i
    rcases he with ⟨_, _, hfalse⟩ | ⟨bs, ⟨pc, hw⟩, _⟩ | ⟨o, n, pc, hm⟩
    · cases hfalse
    rotate_left
    · exact (hW.no_rmw hm).elim
    obtain ⟨hg, _, hc⟩ := hW.writes hw
    rcases hc with ⟨rfl, rfl, rfl, _⟩ | ⟨k, hk, rfl, rfl, _⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (.inl ⟨g, hg, k, hk, rfl, rfl⟩)
  | async i p =>
    cases p <;> simp only
      [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint, and_false,
      Bool.true_eq_false, false_and] at he
    case writeCopy =>
      obtain ⟨g, j⟩ := i
      obtain ⟨_, s, ⟨pc, hb⟩, -, rfl⟩ := he
      obtain ⟨_, _, rfl, hc⟩ := hW.bulk hb
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
      · exact .inr (.inr (.inr ⟨rfl, rfl⟩))
    case writeElem k =>
      obtain ⟨_, s, hc, hk⟩ := he
      obtain ⟨-, hw, -⟩ := hW.copy_spec hc
      simp [Spec.elems, Spec.elemOffsets, hw] at hk
    case writeLoad =>
      obtain ⟨_,spec,addr,hi,_⟩ := he
      exact (hW.no_tensor hi).elim
    case writeStore =>
      obtain ⟨_,spec,addr,hi,_⟩ := he
      exact (hW.no_tensorStore hi).elim
    case writeCta =>
      obtain ⟨_,spec,targets,hi,_⟩ := he
      exact (hW.no_clc hi).elim

theorem Wit.read_intent {e : Ref} {src : Acc} (he : X.Intent e src false) : ReadShape A B S P e src
    := by
  cases e with
  | thread i =>
    obtain ⟨g, j⟩ := i
    rcases he with ⟨bs, ⟨pc, hr⟩, _⟩ | ⟨_, _, hfalse⟩ | ⟨o, n, pc, hm⟩
    rotate_left
    · cases hfalse
    · exact (hW.no_rmw hm).elim
    obtain ⟨hg, _, rfl, rfl, _⟩ := hW.reads hr
    exact .inl ⟨g, hg, rfl, rfl⟩
  | async i p =>
    cases p <;> simp only
      [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint, and_false,
      Bool.false_eq_true, false_and] at he
    case readCopy =>
      obtain ⟨g, j⟩ := i
      obtain ⟨_, ⟨s, ⟨pc, hb⟩, rfl⟩ | ⟨pc, hb⟩⟩ := he
      swap; · exact (hW.no_bulkPrefetch hb).elim
      obtain ⟨_, _, rfl, hc⟩ := hW.bulk hb
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
    case oldElem k =>
      obtain ⟨_, s, r, hc, hr, -⟩ := he
      obtain ⟨-, hw, -⟩ := hW.copy_spec hc
      rw [hw] at hr
      cases hr
    case mmaRead isB k =>
      obtain ⟨_, hsize, ⟨d, s, accum, mask, ⟨pc, hm⟩, hl⟩ | ⟨_, _, _, ⟨pc, hm⟩, -⟩⟩ := he
      swap; · obtain ⟨g, j⟩ := i; exact (hW.no_cp hm).elim
      obtain ⟨g, j⟩ := i
      obtain ⟨_, _, rfl, rfl, _, rfl, _, _⟩ := hW.mma hm
      cases isB
      · simp only [Bool.false_eq_true, ↓reduceIte, mmaSpec_a] at hl
        split_ifs at hl with hk
        let q := offA (k / 32) (k % 32)
        have hq : q < 4096 := by dsimp [q, offA]; omega
        exact .inr (.inr (.inr (.inl ⟨k, hk, q, hq, rfl, (Option.some.inj hl).symm, hsize⟩)))
      · simp only [↓reduceIte, mmaSpec_b] at hl
        split_ifs at hl with hk
        let q := offB (k % 32) (k / 32)
        have hq : q < 256 := by dsimp [q, offB]; omega
        exact .inr (.inr (.inr (.inr ⟨k, hk, q, hq, rfl, (Option.some.inj hl).symm, hsize⟩)))
    case readLoad =>
      obtain ⟨_,spec,addr,hi,_⟩ := he
      exact (hW.no_tensor hi).elim
    case readPrefetch =>
      obtain ⟨_,spec,addr,hi,_⟩ := he
      exact (hW.no_tensorPrefetch hi).elim
    case readStore | oldStore =>
      obtain ⟨_,spec,addr,hi,_⟩ := he
      exact (hW.no_tensorStore hi).elim

end
end PTX.Kernels.TcGemm.Proof

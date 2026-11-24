-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Lemmas.Kernel.Progress.Warp
import Lemmas.Kernel.FullVote
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The kinds of events that count as warp collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An event that is a full ballot, an election, a shuffle, or no collective. -/
inductive CollKind : Kind → Bool → Prop
  | shfl (m : ShflMode) (a : Value) (b c : Nat) (r : Value) (o : Bool) :
      CollKind (.shfl m a b c r o) true
  | vote (mk : Nat) (a : Bool) (b : BitVec 32) (hm : mk = 4294967295) : CollKind (.vote mk a b) true
  | elect (mk inst ld : Nat) : CollKind (.elect mk inst ld) true
  | bar (id : Nat) (c : Option Nat) (md : BarMode) : CollKind (.bar id c md) false
  | rd (a : Acc) (bs : List (Option Byte)) : CollKind (.rd a bs) false
  | wait (l : Loc) (q : Nat) (ok acq : Bool) (sc : MbarScope) :
      CollKind (.wait l q ok acq sc) false
  | tc (k : TcKind) : CollKind (.tc k) false
  | exit : CollKind .exit false
  | fenceProxy (k : _) (sc : _) : CollKind (.fenceProxy k sc) false
  | fenceInit : CollKind .fenceMbarInit false
  | mbInit (l : Loc) (c : Nat) : CollKind (.mbInit l c) false
  | setMax (i : Bool) (n t : Nat) : CollKind (.setMaxReg i n t) false
  | wr (a : Acc) (bs : List Byte) : CollKind (.wr a bs) false
  | copy (o : AsyncCopy.Spec) : CollKind (.copy o) false
  | commit : CollKind .asyncCommit false
  | asyncArr (l : Loc) (b : Bool) : CollKind (.asyncArrive l b) false
  | arrive (l : Loc) (t n : Nat) (b : Bool) (sc : MbarScope) : CollKind (.arrive l t n b sc) false
  | tensor (a : Nat) (s : TensorCopy.Spec) : CollKind (.tensorIssue a s) false

theorem CollKind.counts {pc : Nat} {k : Kind} {b : Bool} (h : CollKind k b) :
    Sched.isWarpColl ⟨pc, k⟩ = b ∧ (if Sched.isWarpColl ⟨pc, k⟩ then 1 else 0) =
      (if isColl ⟨pc, k⟩ then 1 else 0) + (if isElectEv ⟨pc, k⟩ then 1 else 0) := by
  have nv : ∀ {k : Kind}, voteClass k = none → isFullVote ⟨pc, k⟩ = false := fun h => by
    simp [isFullVote, h]
  cases h with
  | vote mk a b hm =>
    subst hm
    have h1 : isFullVote ⟨pc, .vote 4294967295 a b⟩ = true := voteWith_vote _ _ _ _
    refine ⟨rfl, ?_⟩
    simp only [isColl, h1, Bool.or_true, ite_true]
    rfl
  | _ =>
    refine ⟨rfl, ?_⟩
    unfold isColl
    rw [nv (by rfl)]
    rfl

/-- An election or a warp barrier. -/
def roundColl (e : Event) : Bool :=
  isElectEv e || match e.kind with | .warpBar _ _ => true | _ => false

/-- An event of one of those kinds, or a warp barrier. -/
def CollKindW (k : Kind) (b : Bool) : Prop :=
  CollKind k b ∨ (∃ m i, k = .warpBar m i) ∧ b = true

theorem CollKindW.counts {pc : Nat} {k : Kind} {b : Bool} (h : CollKindW k b) :
    Sched.isWarpColl ⟨pc, k⟩ = b ∧ (if Sched.isWarpColl ⟨pc, k⟩ then 1 else 0) =
      (if isColl ⟨pc, k⟩ then 1 else 0) + (if roundColl ⟨pc, k⟩ then 1 else 0) := by
  rcases h with h | ⟨⟨m, i, rfl⟩, rfl⟩
  · obtain ⟨h1, h2⟩ := h.counts (pc := pc)
    refine ⟨h1, ?_⟩
    rw [h2]
    cases h <;> rfl
  · exact ⟨rfl, rfl⟩

/-- The kind of an event of a scan site. -/
theorem epi_kind {dE : Epilogue.D} {e : Event} (hev : Epilogue.Ev p L g dE e)
    (hs : (∃ k, dE.site = .word k) ∨ (∃ k, dE.site = .down k) ∨ (∃ k j, dE.site = .up k j) ∨
      (∃ k, dE.site = .total k) ∨ (∃ l, dE.site = .vote l) ∨ (∃ l, dE.site = .pre l) ∨
      ∃ l, dE.site = .tiles l) (hub : ∀ f, e.kind ≠ .ub f) :
    CollKind e.kind (Progress.Out.coll dE.site) := by
  rcases hs with ⟨k, hs⟩ | ⟨k, hs⟩ | ⟨k, j, hs⟩ | ⟨k, hs⟩ | ⟨l, hs⟩ | ⟨l, hs⟩ | ⟨l, hs⟩ <;>
    simp only [Epilogue.Ev, hs] at hev ⊢
  · rcases hev with ⟨_, h⟩ | ⟨f, h⟩
    · rw [h]; exact .rd _ _
    · exact absurd h (hub f)
  · obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _
  · obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _
  · obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _
  · obtain ⟨_, h⟩ := hev; rw [h]; exact .vote _ _ _ (by norm_num)
  · obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _
  · obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _

end PTX.Kernels.TmlFa4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Sync.WarpInstance
public import Core.Sync.Elect

@[expose] public section

/-!
# Warp vote events and values

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## THREAD-VOTE — warp vote

Statement: `vote.sync.ballot.b32` with the full member mask in a CTA whose size is a multiple of 32
  produces a ballot event with the lane's predicate, complemented when requested, and the ballot is
  written to the destination as a 32-bit integer. `vote.sync` with mode `.all`, `.any` or `.uni`
  produces a vote event with the mode, the member mask and the lane's predicate, complemented when
  requested, and the predicate received is written to the destination. The behaviour is undefined
  when the executing lane is not named in the member mask.

Defs: voteTmpl, voteModeTmpl

Source:
- §9.7.15.10 (vote.sync): "Operand a is a predicate register."
- §9.7.15.10 (vote.sync): "In the ballot form, the destination operand d is a .b32 register."
- §9.7.15.10 (vote.sync): "The destination operand d is a predicate register and its value is the
    same across all threads in membermask ."
- §9.7.15.10 (vote.sync): "The behavior of vote.sync is undefined if the executing thread is not in
    the membermask ."

Direction: stricter

Applies: `vote.sync.ballot.b32` with the full member mask; `vote.sync.{all,any,uni}.pred`

Premises: For the ballot, the CTA size is a multiple of 32 and the member mask is full. For a mode,
  the executing lane is named in the member mask and every lane named in it is a thread of the warp.
  The source is a predicate.

Effect: Event production; a mode form whose executing lane is outside the member mask is a
  `badValue` fault. Other masks of the ballot have no rule (`noRule`, as for `shfl.sync`): every
  lane of the warp is then in the member mask, so the undefined case of an executing thread outside
  the mask cannot arise. A mode form with a member mask that names a lane with no thread (the last
  warp of a CTA whose size is not a multiple of 32) has no rule (`noRule`): the text does not say
  whether such a lane counts as exited.
-/

/-- Warp ballot (VOTE). -/
def voteTmpl (L : Launch) (g : Nat) (t : TState) (d a : Nat) (neg : Bool) (mask : Opnd) :
    Tmpl :=
  match readBits L g t 32 mask, readPred L g t (.reg a) with
  | .ok m, .ok p =>
    if m.toNat = 2 ^ 32 - 1 ∧ L.block % 32 = 0 then
      .vote m.toNat (p != neg) (fun ballot =>
        next (setReg t d (.bits 32 (BitVec.ofNat 64 ballot.toNat))))
    else .ub .noRule
  | .error f, _ | _, .error f => .ub f

/-- A `vote.sync` with mode `.all`, `.any` or `.uni` (VOTE). -/
def voteModeTmpl (L : Launch) (g : Nat) (t : TState) (mode : VoteMode) (d a : Nat) (neg : Bool)
    (mask : Opnd) : Tmpl :=
  match readBits L g t 32 mask, readPred L g t (.reg a) with
  | .ok m, .ok p =>
    if electMember m.toNat (laneOf L g) then
      if maskInWarp L g m.toNat then
        .voteMode mode m.toNat (p != neg) (fun r => next (setReg t d (.pred r)))
      else .ub .noRule
    else .ub .badValue
  | .error f, _ | _, .error f => .ub f

/-! ## DEP-WARP-VOTE — warp vote instances

Statement: The n-th `vote.sync` executions with one member mask of the lanes of a warp form one
  instance, and every lane named in the member mask either takes part in it with the same
  qualifiers or has exited before reaching it. The bit
  of a participating lane in the ballot is that lane's predicate, and the bit of a lane outside the
  mask is zero. In an instance of a vote with mode `.all`, `.any` or `.uni` the lanes share the
  mode, and every lane
  receives the reduction of the predicates of the lanes that take part. A lane returns from a vote
  only after every non-exited lane of the member mask has executed its vote of the instance
  (DEP-WARP-INSTANCE). A vote orders no memory operation.

Defs: voteClass, voteResult, VoteOk, VoteModeOk

Source:
- §9.7.15.10 (vote.sync): "vote.sync will cause executing thread to wait until all non-exited
    threads corresponding to membermask have executed vote.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.15.10 (vote.sync): "In this form, vote.sync.ballot.b32 simply copies the predicate from each
    thread in membermask into the corresponding bit position of destination register d , where the
    bit position corresponds to the thread’s lane id. A thread not specified in membermask will
    contribute a 0 for its entry in vote.sync.ballot.b32 ."
- §9.7.15.10 (vote.sync): "In the mode form, vote.sync performs a reduction of the source predicate
    across all non-exited threads in membermask ."
- §9.7.15.10 (vote.sync): ".all True if source predicate is True for all non-exited threads in
    membermask ."
- §9.7.15.10 (vote.sync): ".any True if source predicate is True for some thread in membermask ."
- §9.7.15.10 (vote.sync): ".uni True if source predicate has the same value in all non-exited
    threads in membermask ."

Direction: stricter

Applies: Ballot instances; instances of `vote.sync.{all,any,uni}.pred`

Premises: A ballot or mode event exists at a given per-mask ordinal.

Effect: Execution constraints in `Consistent.vote` and `Consistent.warpValue` (the received
  values); the waiting dependency `MaskWait L voteClass` (DEP-WARP-INSTANCE) gives the needs of
  every `vote.sync` in `KindNeeds` (DEP-ORDER). Ballots and mode votes have one instance
  identification, the per-mask ordinal of every `vote.sync` execution (`MaskK voteClass`), in the
  value rules and in the needs alike. A lane whose execution at that ordinal has other qualifiers
  (a ballot against a mode, or another mode) fills no need, so the waiting vote does not exist in
  a consistent execution, as the text requires the same qualifiers. The negation of the source is
  part of the lane's predicate and is no qualifier. `.any` takes the predicates of the lanes that
  take part: a lane that exited has no predicate. `.uni` holds when the predicates of the lanes
  that take part are all true or all false.

Review: The bit of a lane of the mask that exited before its `n`-th execution is unconstrained
  (stricter: every value is kept). The text gives an exited thread no predicate to copy. Lanes may
  reach it from different source positions (sm_70 and later), as for `shfl.sync`. A lane whose guard
  is false performs no ballot event; lanes that may execute a guarded `vote.sync` together with
  different guards are unsafe (ERR-NONUNIFORM-GUARD).
-/

/-- The `vote.sync` class (DEP-WARP-INSTANCE): a ballot or a mode vote contributes its member
mask, its mode (`.ballot` for a ballot) and its predicate. -/
def voteClass : Kind → Option (WarpPart VoteMode Bool)
  | .vote mask a _ => some ⟨mask, .ballot, a⟩
  | .voteMode mode mask a _ => some ⟨mask, mode, a⟩
  | _ => none

/-- The predicate a mode vote returns, from the predicates of the lanes that take part. -/
def voteResult (mode : VoteMode) (part : Nat → Option Bool) : Bool :=
  let ps := (List.range 32).filterMap part
  match mode with
  | .all => ps.all id
  | .any => ps.any id
  | .uni => ps.all id || ps.all (!·)
  | .ballot => false

/-- Every ballot received, at the bit of each lane that takes part in its instance, that lane's
predicate, and zero at the bit of each lane outside the member mask. The instance pairs the
`n`-th `vote.sync` executions with one member mask (`MaskK voteClass`), the same pairing as the
needs of the vote (DEP-ORDER). -/
def VoteOk (X : Execution) : Prop :=
  ∀ g i n pc mask a ballot, X.get (g, i) = some ⟨pc, .vote mask a ballot⟩ →
    X.MaskK voteClass (g, i) mask n →
    ∀ part, MaskInstance L voteClass X g mask n .ballot part → ∀ lane < 32,
      (∀ b, part lane = some b → ballot.getLsbD lane = b) ∧
      (mask.testBit lane = false → ballot.getLsbD lane = false)

/-- Every mode vote received the reduction of the predicates of the lanes that take part in its
instance (the lanes of its member mask with the same mode). -/
def VoteModeOk (X : Execution) : Prop :=
  ∀ g i pc mode mask a r n, X.get (g, i) = some ⟨pc, .voteMode mode mask a r⟩ →
    X.MaskK voteClass (g, i) mask n →
    ∀ part, MaskInstance L voteClass X g mask n mode part → r = voteResult mode part

end

end PTX

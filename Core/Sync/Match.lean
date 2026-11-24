-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Sync.WarpInstance
public import Core.Sync.Elect

@[expose] public section

/-!
# Warp match events and values

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## THREAD-MATCH — warp match

Statement: `match.sync` produces a match event with its mode, its type, its member mask and the
  lane's operand of 32 or 64 bits. The mask received is written to the 32-bit destination, and for
  `.all` the optional predicate destination receives whether the operands of the instance are all
  equal; a sink destination is not written. The behaviour is undefined when the executing lane is
  not named in the member mask.

Defs: matchTmpl

Source:
- §9.7.15.11 (match.sync): "Operand a has instruction type and d has .b32 type."
- §9.7.15.11 (match.sync): "The sink symbol ‘_’ may be used in place of any one of the destination
    operands."
- §9.7.15.11 (match.sync): "The behavior of match.sync is undefined if the executing thread is not
    in the membermask ."

Direction: stricter

Applies: `match.any.sync.{b32,b64}` and `match.all.sync.{b32,b64}`, with or without the predicate
  destination

Premises: The executing lane is named in the member mask, every lane named in it is a thread of the
  warp, and the operands can be read.

Effect: Event production; an executing lane outside the member mask is a `badValue` fault. A member
  mask that names a lane with no thread (the last warp of a CTA whose size is not a multiple of 32)
  has no rule (`noRule`): the text does not say whether such a lane counts as exited.
-/

/-- Warp match (MATCH): mode `all`, operand width `w` (32 or 64), destination `d` and predicate
destination `p` (none for a sink or an absent predicate). -/
def matchTmpl (L : Launch) (g : Nat) (t : TState) (all : Bool) (w : Nat) (d p : Option Nat)
    (a mask : Opnd) : Tmpl :=
  match readBits L g t 32 mask, readBits L g t w a with
  | .ok m, .ok v =>
    if electMember m.toNat (laneOf L g) then
      if maskInWarp L g m.toNat then
        .match_ all (w == 64) m.toNat v (fun r ok =>
          let t1 := match d with
            | some d => setReg t d (.bits 32 (r.setWidth 64))
            | none => t
          next (match p with
            | some p => setReg t1 p (.pred ok)
            | none => t1))
      else .ub .noRule
    else .ub .badValue
  | .error f, _ | _, .error f => .ub f

/-! ## DEP-WARP-MATCH — warp match instances

Statement: A match belongs to an instance of the `match.sync` executions with its member mask
  (DEP-WARP-INSTANCE) whose lanes share the mode and type. In `.any` mode a lane receives the mask
  of the lanes that take part and whose operand equals its own. In `.all` mode a lane receives the
  mask of the lanes that take part when all their operands are equal and zero otherwise, and its
  predicate is whether they are all equal. A match orders no memory operation.

Defs: matchEqual, matchMask, matchClass, MatchOk

Source:
- §9.7.15.11 (match.sync): "match.sync performs broadcast and compare of operand a across all
    non-exited threads in membermask and sets destination d and optional predicate p based on mode."
- §9.7.15.11 (match.sync): "Destination d is a 32-bit mask where bit position in mask corresponds to
    thread’s laneid."
- §9.7.15.11 (match.sync): ".all d is set to mask corresponding to non-exited threads in membermask
    if all non-exited threads in membermask have same value of operand a ; otherwise d is set to 0.
    Optionally predicate p is set to true if all non-exited threads in membermask have same value of
    operand a ; otherwise p is set to false."
- §9.7.15.11 (match.sync): ".any d is set to mask of non-exited threads in membermask that have same
    value of operand a ."
- EXT-WARP-INSTANCE

Direction: reading

Applies: Instances of `match.sync`

Premises: A match event exists at a given per-mask ordinal.

Effect: Execution constraint in `Consistent.warpValue`. The event of an `.any` match records the
  equality predicate as well; THREAD-MATCH does not write it. In `.any` mode the lanes that "have
  same value of operand a" are those whose operand equals the operand of the receiving lane, which
  takes part in the instance.
-/

/-- The operands of the lanes that take part are all equal to `a`. -/
def matchEqual (a : BitVec 64) (part : Nat → Option (BitVec 64)) : Bool :=
  (List.range 32).all fun lane => (part lane).all (· == a)

/-- The mask a match returns to a lane with operand `a`, from the operands of the lanes that take
part. -/
def matchMask (all : Bool) (a : BitVec 64) (part : Nat → Option (BitVec 64)) : BitVec 32 :=
  if all then (if matchEqual a part then laneBits fun lane => (part lane).isSome else 0)
  else laneBits fun lane => part lane == some a

/-- The `match.sync` class (DEP-WARP-INSTANCE): a match contributes its member mask, its mode and
type, and its operand. -/
def matchClass : Kind → Option (WarpPart (Bool × Bool) (BitVec 64))
  | .match_ all wide mask a _ _ => some ⟨mask, (all, wide), a⟩
  | _ => none

/-- Every match received the mask and the predicate of the operands of the lanes that take part
in its instance (the lanes of its member mask with the same mode and type). -/
def MatchOk (X : Execution) : Prop :=
  ∀ g i pc all wide mask a r p n, X.get (g, i) = some ⟨pc, .match_ all wide mask a r p⟩ →
    X.MaskK matchClass (g, i) mask n →
    ∀ part, MaskInstance L matchClass X g mask n (all, wide) part →
      r = matchMask all a part ∧ p = matchEqual a part

end

end PTX

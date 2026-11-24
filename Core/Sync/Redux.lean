-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Sync.WarpInstance
public import Core.Sync.Elect

@[expose] public section

/-!
# Warp reduction events and values

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## THREAD-REDUX — integer warp reduction

Statement: An integer `redux.sync` produces a reduction event with its operation, its member mask
  and the lane's 32-bit source, and the result received is written to the destination as a 32-bit
  integer. The behaviour is undefined when the executing lane is not named in the member mask.

Defs: reduxTmpl

Source:
- §9.7.15.13 (redux.sync): "redux.sync performs a reduction operation .op of the 32 bit source
    register src across all non-exited threads in the membermask ."
- §9.7.15.13 (redux.sync): "The result of the reduction operation is written to the 32 bit
    destination register dst ."
- §9.7.15.13 (redux.sync): "The behavior of redux.sync is undefined if the executing thread is not
    in the membermask ."

Direction: stricter

Applies: `redux.sync.{add,min,max}.{u32,s32}` and `redux.sync.{and,or,xor}.b32`

Premises: The executing lane is named in the member mask, every lane named in it is a thread of the
  warp, and the operands can be read.

Effect: Event production; an executing lane outside the member mask is a `badValue` fault. A member
  mask that names a lane with no thread (the last warp of a CTA whose size is not a multiple of 32)
  has no rule (`noRule`): the text does not say whether such a lane counts as exited. The `.f32`
  forms have no rule (`WarpInstr.rule`).
-/

/-- Integer warp reduction (REDUX). -/
def reduxTmpl (L : Launch) (g : Nat) (t : TState) (op : ReduxOp) (signed : Bool) (d : Nat)
    (a mask : Opnd) : Tmpl :=
  match readBits L g t 32 mask, readBits L g t 32 a with
  | .ok m, .ok v =>
    if electMember m.toNat (laneOf L g) then
      if maskInWarp L g m.toNat then
        .redux op signed m.toNat (v.setWidth 32) (fun r =>
          next (setReg t d (.bits 32 (r.setWidth 64))))
      else .ub .noRule
    else .ub .badValue
  | .error f, _ | _, .error f => .ub f

/-! ## DEP-WARP-REDUX — integer warp reduction instances

Statement: A reduction belongs to an instance of the `redux.sync` executions with its member mask
  (DEP-WARP-INSTANCE) whose lanes share the operation and type, and every lane receives the
  operation applied to the sources of the lanes that take part. Addition wraps modulo 2^32, `.min`
  and `.max` compare as signed integers for `.s32` and as unsigned integers for `.u32`, and `.and`,
  `.or`, `.xor` are bitwise. A reduction orders no memory operation.

Defs: reduxStep, reduxResult, reduxClass, ReduxOk

Source:
- §9.7.15.13 (redux.sync): "redux.sync performs a reduction operation .op of the 32 bit source
    register src across all non-exited threads in the membermask ."
- §9.7.15.13 (redux.sync): "Reduction operation can be one of the bitwise operation in .and , .or ,
    .xor or arithmetic operation in .add , .min , .max ."
- §9.7.15.13 (redux.sync): "For the .add operation result is truncated to 32 bits."
- EXT-WARP-INSTANCE

Direction: reading

Applies: Instances of the integer `redux.sync` forms

Premises: A reduction event exists at a given per-mask ordinal.

Effect: Execution constraint in `Consistent.warpValue`. The operations are associative and
  commutative, so the result does not depend on the order in which `reduxResult` combines the
  sources; it takes them by lane. `.min` and `.max` on `.u32` and `.s32` compare the values of the
  type. A lane that exited contributes no source.
-/

/-- One step of the reduction: `op` on two 32-bit values (`signed` for `.s32`). -/
def reduxStep (op : ReduxOp) (signed : Bool) (x y : BitVec 32) : BitVec 32 :=
  match op with
  | .add => x + y
  | .min => if (if signed then x.sle y else x.ule y) then x else y
  | .max => if (if signed then x.sle y else x.ule y) then y else x
  | .and => x &&& y
  | .or => x ||| y
  | .xor => x ^^^ y

/-- The result of a reduction over the sources `vs`, in lane order. -/
def reduxResult (op : ReduxOp) (signed : Bool) : List (BitVec 32) → BitVec 32
  | [] => 0
  | v :: vs => vs.foldl (reduxStep op signed) v

/-- The `redux.sync` class (DEP-WARP-INSTANCE): a reduction contributes its member mask, its
operation and type, and its source. -/
def reduxClass : Kind → Option (WarpPart (ReduxOp × Bool) (BitVec 32))
  | .redux op signed mask a _ => some ⟨mask, (op, signed), a⟩
  | _ => none

/-- Every reduction received the reduction of the sources of the lanes that take part in its
instance (the lanes of its member mask with the same operation and type). -/
def ReduxOk (X : Execution) : Prop :=
  ∀ g i pc op signed mask a r n, X.get (g, i) = some ⟨pc, .redux op signed mask a r⟩ →
    X.MaskK reduxClass (g, i) mask n →
    ∀ part, MaskInstance L reduxClass X g mask n (op, signed) part →
      r = reduxResult op signed ((List.range 32).filterMap part)

end

end PTX

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule

@[expose] public section

/-!
# Warp collectives

`shfl.sync`, `vote.sync`, `match.sync`, `redux.sync`, `activemask`, `elect.sync` and
`bar.warp.sync`.
-/

namespace PTX

/-! ## PROG-ISA-WARP — warp collectives
Statement: A warp collective is its kind with the kind's qualifiers, its data type, its
  destinations, its sources and its member mask. Every entry of the `warp` family decodes to it. The
  predicate source of `vote.sync` may be negated; no other source may.

Defs: ShflMode, VoteMode, ReduxOp, WarpKind, WarpInstr, Decode.WarpInstr.ofRaw, ReduxOp.intForm,
  WarpInstr.rule

Source:
- §9.7.10.6: "shfl.sync.mode.b32 d[|p], a, b, c, membermask;"
- §9.7.10.6: ".mode = { .up, .down, .bfly, .idx };"
- §9.7.15.10: "vote.sync.mode.pred d, {!}a, membermask;"
- §9.7.15.10: "vote.sync.ballot.b32 d, {!}a, membermask;"
- §9.7.15.11: "match.any.sync.type d, a, membermask; match.all.sync.type d[|p], a, membermask; .type
    = { .b32, .b64 };"
- §9.7.15.11: "The sink symbol ‘_’ may be used in place of any one of the destination operands."
- §9.7.15.12: "activemask.b32 d;"
- §9.7.15.13: "redux.sync.op.type dst, src, membermask; .op = {.add, .min, .max} .type = {.u32,
    .s32} redux.sync.op.b32 dst, src, membermask; .op = {.and, .or, .xor}"
- §9.7.15.15: "elect.sync d|p, membermask;"
- §9.7.15.2: "bar.warp.sync membermask;"

Direction: representation

Applies: Every instruction of the `warp` family

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `WarpInstr.rule` selects THREAD-SHFL for `shfl.sync`, THREAD-VOTE for
  `vote.sync`, THREAD-REDUX for the integer forms of `redux.sync` (`ReduxOp.intForm`),
  THREAD-MATCH for `match.sync`, THREAD-ACTIVEMASK for `activemask`, THREAD-ELECT for
  `elect.sync` and THREAD-WARP-BAR for `bar.warp.sync`. The `.f32` forms of `redux.sync` have no
  rule.
-/

/-- `shfl.sync` modes. -/
inductive ShflMode where
  | up | down | bfly | idx
  deriving DecidableEq, Repr

/-- `vote.sync` modes. -/
inductive VoteMode where
  | all | any | uni | ballot
  deriving DecidableEq, Repr

/-- `redux.sync` operations. -/
inductive ReduxOp where
  | add | min | max | and | or | xor
  deriving DecidableEq, Repr

/-- The kind of a warp collective. -/
inductive WarpKind where
  | shfl (m : ShflMode)
  /-- `neg` for a complemented predicate source `!a`. -/
  | vote (m : VoteMode) (neg : Bool)
  | match_ (all : Bool)
  | redux (op : ReduxOp) (abs nan : Bool)
  | activemask
  | elect
  | barWarp
  deriving DecidableEq, Repr

/-- A warp collective: kind, data type (none for `elect.sync` and `bar.warp.sync`), destinations
(`none` for `_`), sources and member mask (none for `activemask`). -/
structure WarpInstr where
  kind : WarpKind
  ty : Option DType := none
  dsts : List (Option Nat) := []
  srcs : List Opnd := []
  mask : Option Opnd := none
  deriving DecidableEq, Repr

namespace Decode
open PTX.Syntax

/-- The warp collective of a recognized instruction. -/
def WarpInstr.ofRaw (env : Env) (r : Isa.Raw) : M WarpInstr := do
  let ty ← match r.get .type with
    | some t => some <$> dtype (some t)
    | none => pure none
  let mask ← match opnd? r "membermask" with
    | some o => some <$> src env 32 o.op
    | none => pure none
  let others := r.opnds.filter (·.name != "membermask")
  match r.entry with
  | .vote_sync | .vote_sync_ballot => do
    let mode : VoteMode := match r.get .mode with
      | some .all => .all | some .any => .any | some .uni => .uni | _ => .ballot
    let (a, neg) ← match ← arg r "a" with
      | .negate p => pure (p, true)
      | p => pure (p, false)
    let d ← rdsts env (← (opnd? r "d").elim (throw "vote destination") pure)
    return { kind := .vote mode neg, ty, dsts := d, srcs := [.reg (← reg env 1 a)], mask }
  | _ => do
    let kind : WarpKind ← match r.entry with
      | .shfl_sync | .shfl_sync_p => pure (.shfl (match r.get .mode with
          | some .up => .up | some .down => .down | some .bfly => .bfly | _ => .idx))
      | .match_any_sync => pure (.match_ false)
      | .match_all_sync | .match_all_sync_p => pure (.match_ true)
      | .redux_sync | .redux_sync_bitwise | .redux_sync_f32 =>
        let op : ReduxOp := match r.get .op with
          | some .add => .add | some .min => .min | some .max => .max | some .and => .and
          | some .or => .or | _ => .xor
        pure (.redux op (flag r .abs) (flag r .nan))
      | .activemask => pure .activemask
      | .elect_sync => pure .elect
      | .bar_warp_sync => pure .barWarp
      | _ => throw "not a warp collective"
    let (dsts, srcs) ← operands env { r with opnds := others }
    return { kind, ty, dsts, srcs, mask }

end Decode

/-- The integer `redux.sync` forms: `.add`, `.min`, `.max` on `.u32` or `.s32`, and `.and`, `.or`,
`.xor` on `.b32`. -/
def ReduxOp.intForm (op : ReduxOp) (k : IType) : Bool :=
  match op, k with
  | .add, .u | .add, .s | .min, .u | .min, .s | .max, .u | .max, .s => true
  | .and, .b | .or, .b | .xor, .b => true
  | _, _ => false

/-- The rule of a warp collective: THREAD-SHFL for `shfl.sync.b32` (with or without the validity
predicate), THREAD-VOTE for `vote.sync`, THREAD-REDUX for the integer forms of `redux.sync`,
THREAD-MATCH for `match.sync`, THREAD-ACTIVEMASK for `activemask`, THREAD-ELECT for `elect.sync`
and THREAD-WARP-BAR for `bar.warp.sync`. -/
def WarpInstr.rule (w : WarpInstr) : Option RuleId :=
  match w.kind, w.dsts, w.srcs, w.mask with
  | .shfl _, some _ :: _, [_, _, _], some _ =>
    match w.dsts with
    | [_] | [_, some _] => some .threadShfl
    | _ => none
  | .vote _ _, [some _], [.reg _], some _ => some .threadVote
  | .redux op false false, [some _], [_], some _ =>
    match w.ty with
    | some (.int k 32) => if op.intForm k then some .threadRedux else none
    | _ => none
  | .match_ all, ds, [_], some _ =>
    match w.ty, all, ds with
    | some (.int .b 32), _, [some _] | some (.int .b 64), _, [some _]
    | some (.int .b 32), true, [some _, _] | some (.int .b 64), true, [some _, _]
    | some (.int .b 32), true, [none, some _] | some (.int .b 64), true, [none, some _] =>
      some .threadMatch
    | _, _, _ => none
  | .activemask, [some _], [], none => some .threadActivemask
  | .elect, [_, some _], [], some _ => some .threadElect
  | .barWarp, [], [], some _ => some .threadWarpBar
  | _, _, _, _ => none

end PTX

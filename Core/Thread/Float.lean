-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Float.Approx

@[expose] public section

/-!
# Thread semantics: floating instructions per lane

What one lane of a floating instruction produces from the data of its sources.
-/

namespace PTX

noncomputable section

/-! ## THREAD-FLOAT — floating instructions
Statement: A floating instruction reads each source as a datum of its format and computes each
  lane of its result from the data of that lane: the IEEE operations and the instructions defined
  by their text by THREAD-FLOAT-IEEE, and the approximate instructions by THREAD-FLOAT-APPROX. A
  result the manual leaves open has no rule.

Defs: FOut, FloatInstr.lane

Source:
- §9.7.3.3: "fA[0] = a[0:31]; fA[1] = a[32:63]; fB[0] = b[0:31]; fB[1] = b[32:63]; for (i = 0; i <
    2; i++) { d[i] = fA[i] + fB[i]; }"
- §9.7.4.1: "fA[0] = a[0:15]; fA[1] = a[16:31]; fB[0] = b[0:15]; fB[1] = b[16:31];"
- §9.7.3: "Single-precision instructions return an unspecified NaN"
- §9.7.4: "Half-precision instructions return an unspecified NaN ."

Direction: stricter

Applies: Every floating instruction whose rule is THREAD-FLOAT (`FloatInstr.rule`,
  PROG-ISA-FLOAT)

Premises: The operands satisfy the register rules (THREAD-REG); each floating source is read by
  `classify` as a datum of its format (THREAD-NUM).

Effect: Local evaluation. Each floating source is read with `classify` in its format, which is
  the source's entry of `srcTys` for a mixed-precision form and the instruction's type otherwise;
  an opaque NaN reads as the NaN with an unknown pattern. A packed source of an `x2` type has two
  elements, its halves, the low half first; lane `i` takes element `i` of every packed source,
  and the result of lane `i` is element `i` of the destination. `FloatInstr.lane` gives the
  result of one lane from the lane's floating sources in operand order (`FOut`): the Boolean of
  `testp` and of the comparison of `setp` and `set`, and the datum in the destination format for
  every other operation; `setp` and `set` combine it with their `BoolOp` and predicate operand,
  and `set` encodes it, in `execFloat`, which runs the lanes. A `set` with an integer source type
  compares integers and has no floating lane. The result is written by `FVal.toValue`: a payload
  for a number and `+0`, the opaque NaN value for a NaN with an unknown pattern, and the bit
  pattern for `-0`, an infinity and a NaN with a known pattern; a packed result is the pair of its
  elements, the low element first. A form whose rule is not THREAD-FLOAT has no lane. The rule is
  stricter than the manual where a result is open: a NaN with unknown bits stays opaque, and every
  case THREAD-FLOAT-IEEE and THREAD-FLOAT-APPROX leave without a rule is rejected.
-/

/-- What one lane of a floating instruction produces: a floating datum, or the Boolean of a
comparison or a test. -/
inductive FOut where
  | val (v : FVal)
  | pred (b : Bool)
  deriving DecidableEq, Repr

/-- THREAD-FLOAT for one lane. `xs` are the lane's floating sources in operand order, each
classified in its own format (`srcTys`, or `ty` when `srcTys = []`), before any `.ftz` flush;
predicate sources (the `c` of a BoolOp) are not in `xs`. `none` is no rule. -/
def FloatInstr.lane (f : FloatInstr) (xs : List FVal) : Option FOut :=
  match f.rule with
  | none => none
  | some _ =>
    match f.op with
    | .testp _ | .setp .. | .set .. => FOut.pred <$> f.compare xs
    | _ => FOut.val <$> match f.mode with
      | .approx => f.approx xs
      | .ieee => f.ieee xs
      | .full => none

end

end PTX

# SPDX-License-Identifier: Apache-2.0
"""Generate `Proof/Ref/Machine.lean`: the successor of the thread machine at the startup sites.

The file states the successor of the generated thread machine at each of the 64 sites of the
startup phase in one of five named forms. Its header and the definitions of the forms are the
template `HEADER` below. The 64 equations `nextR_<site>` are written from the list of the
phase's sites in `machine`: five elections, three shuffles, eleven mbarrier initializations,
three fences, three barriers, the 21 loads of the offsets array, one arrival, sixteen tensor
copies and one poll. The script reads no file.

    python3 Kernels/FlashKdaFwd/Gen/ref_machine.py            # write the file
    python3 Kernels/FlashKdaFwd/Gen/ref_machine.py --check    # write nothing; fail if it is stale
"""

import argparse
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[2] / "Tools"))
import outputs  # noqa: E402
from lean_wrap import wrap_lines  # noqa: E402

OUT = HERE.parent / "Proof" / "Ref" / "Machine.lean"

HEADER = """-- SPDX-License-Identifier: Apache-2.0
-- The equations are written by Gen/ref_machine.py.
module

public import Kernels.FlashKdaFwd.Proof.Thread.Entry
public import Kernels.FlashKdaFwd.Proof.Thread.ParamBridge
public import Kernels.FlashKdaFwd.Proof.Ref.Common

@[expose] public section

/-! # The successor of the thread machine at the sites of the startup phase, by form

The generated machine (`Thread/Next.lean`) states the successor at each site with its own
`match` on the event. The reference layer reads a successor through five named forms, so that
one lemma per form says what a successor means for the event and the next state:

* a plain successor `some (some d')`, whatever the event (initializations, fences, barriers,
  arrivals, tensor copies);
* `loadWord` (the generator's own, `Thread/EventLib.lean`): a load of the offsets array; bytes
  that rebuild to no value stop the thread, a 64-bit integer continues with the word, any
  other value is the machine's only give-up (excluded by the assumption `inputReadOnly`);
* `elNext` and `elNextB`: an election; the successor depends on the elected lane and on
  whether the thread's lane is the elected one (stated with `if` at the first four elections
  and with a Boolean at the fifth, as the generator writes them);
* `shNext`: a shuffle whose received value the code reads as an integer;
* `wtNext`: a poll of an mbarrier.

`nextR_<site>` is the equation of each of the 64 sites of the phase in its form, by `rfl` from
the generated definition. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

/-- The successor after an election: the elected lane goes to `f ld true`, the others to
`f ld false`. -/
def elNext (L : Launch) (g : Nat) (e : Event) (f : Nat → Bool → D) : Option (Option D) :=
  match e.kind with
  | .elect _ _ ld => some (some (if laneOf L g = ld then f ld true else f ld false))
  | _ => none

/-- The successor after an election, with "this lane is the elected one" as a Boolean. -/
def elNextB (L : Launch) (g : Nat) (e : Event) (f : Nat → Bool → D) : Option (Option D) :=
  match e.kind with
  | .elect _ _ ld => some (some (f ld (laneOf L g == ld)))
  | _ => none

/-- The successor after a shuffle whose received value is read as an integer. -/
def shNext (e : Event) (f : BitVec 64 → Bool → D) : Option (Option D) :=
  match e.kind with
  | .shfl _ _ _ _ v ok =>
    match wordOf v with
    | some n => some (some (f (BitVec.ofNat 64 n) ok))
    | none => none
  | _ => none

/-- The successor after a poll of an mbarrier. -/
def wtNext (e : Event) (f : Bool → D) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (f ok))
  | _ => none

variable {L : Launch} {g : Nat} (w : Nat → BitVec 64) (p : Nat → Bool) (x : Nat → Value)
  (e : Event)

"""


def machine():
    """The text of `Machine.lean`."""
    out = [HEADER]

    def st(s):
        return f"⟨{s}, w, p, x⟩"

    eqs = []
    for j in range(4):
        s = f".elect {j}"
        eqs.append(
            (
                f"elect_{j}",
                s,
                f"elNext L g e fun ld b =>\n      after_elect_{j} L g (scope_elect_{j} {st(s)} ld b)",
            )
        )
    s = ".elect 4"
    eqs.append(
        (
            "elect_4",
            s,
            f"elNextB L g e fun ld b =>\n      after_elect_4 L g (scope_elect_4 {st(s)} ld b)",
        )
    )
    eqs.append(("shfl_0", ".shfl 0", None))
    for j in (1, 2):
        s = f".shfl {j}"
        eqs.append((f"shfl_{j}", s, f"shNext e fun n ok => after_shfl_{j} L g {st(s)} n ok"))
    for j in range(11):
        s = f".mbarInit {j}"
        eqs.append((f"mbarInit_{j}", s, f"some (some (after_mbarInit_{j} L g {st(s)}))"))
    for j in range(3):
        s = f".fenceMbarInit {j}"
        eqs.append((f"fenceMbarInit_{j}", s, f"some (some (after_fenceMbarInit_{j} L g {st(s)}))"))
    for j in range(3):
        s = f".bar {j}"
        eqs.append((f"bar_{j}", s, f"some (some (after_bar_{j} L g {st(s)}))"))
    for j in range(21):
        s = f".load {j}"
        eqs.append((f"load_{j}", s, f"loadWord e fun y => after_load_{j} L g {st(s)} y"))
    eqs.append(
        (
            "mbarArrive_0",
            ".mbarArrive 0",
            f"some (some (after_mbarArrive_0 L g {st('.mbarArrive 0')}))",
        )
    )
    for j in range(16):
        s = f".tensorCopy {j}"
        eqs.append((f"tensorCopy_{j}", s, f"some (some (after_tensorCopy_{j} L g {st(s)}))"))
    eqs.append(
        (
            "mbarWait_0",
            ".mbarWait 0",
            f"wtNext e fun ok => after_mbarWait_0 L g {st('.mbarWait 0')} ok",
        )
    )
    for name, s, rhs in eqs:
        if rhs is None:
            out += [
                f"theorem nextR_{name} : Thread.next L g {st(s)} e =",
                "    (match e.kind with",
                f"    | .shfl _ _ _ _ _ ok => some (some (after_shfl_0 L g {st(s)} 0 ok))",
                "    | _ => none) := rfl",
                "",
            ]
        else:
            out += [f"theorem nextR_{name} : Thread.next L g {st(s)} e =", f"    {rhs} := rfl", ""]
    out += ["end", "", "end PTX.Kernels.FlashKdaFwd.Proof.Ref"]
    return "\n".join(wrap_lines("\n".join(out).split("\n"))) + "\n"


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--check", action="store_true", help="write nothing; fail if stale")
    args = cli.parse_args()
    outputs.write_or_check({OUT: machine()}, args.check)


if __name__ == "__main__":
    main()

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tma

@[expose] public section

namespace PTX
noncomputable section

/-! ## THREAD-CLC-QUERY — issuing requests and decoding cancellation responses
Statement: `clusterlaunchcontrol.try_cancel` issues an asynchronous request whose 16-byte aligned
  response is written to shared memory, and which notifies an mbarrier. The query instructions
  decode a response: the status gives whether a cluster was canceled, and a coordinate query gives a
  coordinate of the first CTA of the canceled cluster. A coordinate query of a failed response is a
  fault.

Defs: clcQueryValue, clcTmpl

Source:
- §9.7.15.18–19
- EXT-CLUSTER-RANK (the first CTA's coordinates, OBJ-CLC-ARBITRATION)

Direction: reading

Applies: Shared::cta try_cancel (including multicast) and scalar response queries

Premises: The operand is an opaque response; extracting coordinates requires a successful
  cancellation.

Effect: Asynchronous request issue or register update with explicit response observation. The
  response write is the effect of DEP-CLC-EFFECTS. The vector query form is unsupported by the
  decoder.
-/
/-- The value of a response query: whether the request canceled a cluster, or a coordinate of
its first CTA. -/
def clcQueryValue (q : ClcQuery) (r : ClcResponse) : Exec Value :=
  match q with
  | .isCanceled => .ok (.pred r.firstCta.isSome)
  | .first dim => do
    let some (x, y, z) := r.firstCta | throw .badValue
    let v := match dim with | .x => x | .y => y | .z => z
    pure (.bits 32 (BitVec.ofNat 64 v.toNat))

/-- The event of a cluster launch control instruction in a thread: issuing a request, or
decoding a response. -/
def clcTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .clcTryCancel multicast dst off mb moff => ofExec do
    let d ← effAddr L g t .shared dst off
    let m ← mbarLoc L g t mb moff
    unless d.addr % 16 = 0 do throw .misaligned
    let targets := if multicast then
      (List.range L.grid).filter (fun c => L.clusterOfCta c == L.clusterOfCta (g / L.block))
      else [g / L.block]
    pure (.clcIssue ⟨d, m, multicast⟩ targets (next t))
  | .clcQuery q dst src => ofExec do
    let .clc r ← readValue L g t 128 src | throw .typeMismatch
    let v ← clcQueryValue q r
    pure (.clcQuery q r (next (setReg t dst v)))
  | _ => .ub .noRule

end
end PTX

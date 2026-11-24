-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Core.Thread.Local

@[expose] public section

namespace PTX
noncomputable section

/-! ## THREAD-ELECT — leader election template
Statement: `elect.sync` produces an election event for the executing lane, which must be named in
  the 32-bit member mask. The predicate result is true exactly in the elected leader lane, and the
  optional destination receives the lane number of the leader.

Defs: electMember, electTmpl

Source:
- §9.7.15.15 (elect.sync)

Direction: reading

Applies: 32-bit member masks, a predicate destination and optional lane-ID destination

Premises: The executing lane is named in the mask and operand reads succeed.

Effect: Event template. Other lanes and deterministic choice are constrained by DEP-WARP-ELECT, not
  assumed from the member mask alone.
-/
/-- Lane `lane` is a member of the mask: it is a lane of the warp and its bit is set. -/
def electMember (mask lane : Nat) : Prop := lane < 32 ∧ mask.testBit lane = true
instance (mask lane : Nat) : Decidable (electMember mask lane) := by
  unfold electMember; infer_instance

/-- The event of an `elect.sync` in a thread: an election over the member mask, whose leader
result is left open here. -/
def electTmpl (L : Launch) (g : Nat) (t : TState) (dst : Option Nat)
    (pred : Nat) (mask : Opnd) : Tmpl :=
  match readBits L g t 32 mask with
  | .error f => .ub f
  | .ok bits =>
    if electMember bits.toNat (laneOf L g) then
      .elect bits.toNat (fun leader =>
        let t' := match dst with
          | none => t
          | some d => setReg t d (.bits 32 (BitVec.ofNat 64 leader))
        next (setReg t' pred (.pred (laneOf L g == leader))))
    else .ub .badValue

/-! ## DEP-WARP-ELECT — completed election collectives

Statement: Every lane named in the member mask of an election executes the same `elect.sync`
  instruction with the same mask and receives the same leader, which is a lane of the mask. Repeated
  elections of one warp with equal masks return the same leader.

Defs: Execution.Elect, ElectOk

Source:
- §9.7.15.15 (one leader, deterministic mask choice, mandatory sync)
- EXT-ELECT-SITE (one source instruction per instance)

Direction: reading

Applies: Dynamic warp election instances, including partial masks and repeated calls

Premises: Events identify a member mask, instance label and returned leader. Labels are matching
  witnesses within a warp. They are not timestamps or global instruction ordinals.

Effect: `Consistent.elect` constrains returned results. The needs of an election (`KindNeeds`,
  DEP-ORDER) are the events of every lane of its mask with its label, so each participant's
  arrival is a witness of every return of that instance; this is execution-layer order only. A lane
  contributes at most once to an instance. Repeated elections return the same leader because
  §9.7.15.15 says that "the same leader thread is elected for the same membermask every time", and
  the member mask names lanes of the executing warp. An unfinished collective has no completed
  election event yet. `DependencyOk.acyclic` rules out mutually dependent returns. Every leader
  choice satisfying the instruction's contract is admitted; no lane (including lane zero) is singled
  out.

### EXT-ELECT-SITE — the lanes of one election execute one `elect.sync` instruction

Statement: An election instance consists of the lanes of the member mask that execute the same
  `elect.sync` instruction, at one source position. Lanes that wait at two different `elect.sync`
  instructions never form one instance.

Source:
- §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to
    wait until all threads in the membermask execute the elect instruction before resuming
    execution."

Why it is not spec text: "the elect instruction" does not say whether the other lanes must execute
  this instruction or any `elect.sync`; §9.7.15.2 states the other choice for `bar.warp.sync` ("have
  executed a bar.warp.sync with the same membermask value"), which WarpBarOk follows. The
  same-position reading matches ERR-NONUNIFORM-GUARD, whose collectives are executions of one
  position.

Direction: stricter

Effect: If the lanes of a mask wait at two different `elect.sync` instructions, the model forms no
  instance and they block, so that execution is not Complete and the kernel's progress theorem
  cannot be proved; in a kernel whose theorems are proved no such state is reachable, and the
  reading excludes none of its executions. Disclosed by every kernel whose statement names
  `WarpKind.elect`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.
-/
/-- Event `e` is an election at source position `pc` with member mask `mask`, instance label
`inst` and returned leader `leader`. -/
def Execution.Elect (X : Execution) (e : EvId) (pc mask inst leader : Nat) : Prop :=
  X.get e = some ⟨pc, .elect mask inst leader⟩

/-- Every election event is of a launched lane of its mask and returns a leader of the mask, and
the events of one instance (one label) and the instances of one warp agree on the source
position, the mask and the leader as the rule requires. That every lane of the mask has executed
the instance is the need of the election (`KindNeeds`, DEP-ORDER). -/
def ElectOk (L : Launch) (X : Execution) : Prop :=
  (∀ e pc mask inst leader, X.Elect e pc mask inst leader →
    e.1 < L.threads ∧ electMember mask (laneOf L e.1) ∧ electMember mask leader) ∧
  (∀ e f pc pc' mask mask' inst leader leader',
    X.Elect e pc mask inst leader → X.Elect f pc' mask' inst leader' →
    SameWarp L e.1 f.1 → pc = pc' ∧ mask = mask' ∧ leader = leader' ∧
      (e.1 = f.1 → e = f)) ∧
  (∀ e f pc pc' mask inst inst' leader leader',
    X.Elect e pc mask inst leader → X.Elect f pc' mask inst' leader' → SameWarp L e.1 f.1 →
    leader = leader')

end
end PTX

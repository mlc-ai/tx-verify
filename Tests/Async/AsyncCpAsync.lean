-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Async.CpAsync
public import Core.Async.BulkExecution
public import Core.Async.AsyncCopy
public import Core.MBarrier.MBarrierObject

/-! Decoding, thread events and effect validity of `cp.async`, `cp.async.commit_group`,
`cp.async.wait_group`, `cp.async.wait_all` and `cp.async.mbarrier.arrive`, the membership of
`cp.async` operations in `cp.async`-groups, and the pending-count increment of an mbarrier. -/
namespace PTX.Tests.AsyncCpAsync
noncomputable section
open PTX.Syntax

/-! ## Decoding -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 8, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%p".toList, 1, 1⟩],
    labels := [], params := [] }
private def at' (n : String) : Operand := .address [.register n]
private def isOk : Except String Op → Bool
  | .ok _ => true
  | .error _ => false
private def unmodeled : Except String Op → Bool
  | .ok (.unmodeled _) => true
  | _ => false

-- Registers: `%r0`-`%r7` are 0-7, `%rd0` and `%rd1` are 8 and 9, `%p0` is 10.
example : Decode.op env "cp.async.ca.shared.global" [at' "%r0", at' "%rd0", .literal "4"] =
    .ok (.cpAsync 0 0 8 0 4 .full none) := rfl
example : Decode.op env "cp.async.cg.shared.global" [at' "%r0", at' "%rd0", .literal "16"] =
    .ok (.cpAsync 0 0 8 0 16 .full none) := rfl
example : Decode.op env "cp.async.ca.shared::cta.global" [at' "%r0", at' "%rd0", .literal "8"] =
    .ok (.cpAsync 0 0 8 0 8 .full none) := rfl
-- A 32-bit register after the cp-size is `src-size`; a predicate register is `ignore-src`.
example : Decode.op env "cp.async.ca.shared.global"
    [at' "%r0", at' "%rd0", .literal "4", .register "%r1"] =
    .ok (.cpAsync 0 0 8 0 4 (.size (.reg 1)) none) := rfl
example : Decode.op env "cp.async.cg.shared.global"
    [at' "%r0", at' "%rd0", .literal "16", .literal "7"] =
    .ok (.cpAsync 0 0 8 0 16 (.size (.imm 7)) none) := rfl
example : Decode.op env "cp.async.ca.shared.global"
    [at' "%r0", at' "%rd0", .literal "4", .register "%p0"] =
    .ok (.cpAsync 0 0 8 0 4 (.ignore (.reg 10)) none) := rfl
example : Decode.op env "cp.async.cg.shared.global.L2::cache_hint"
    [at' "%r0", at' "%rd0", .literal "16", .register "%rd1"] =
    .ok (.cpAsync 0 0 8 0 16 .full (some (.reg 9))) := rfl
example : Decode.op env "cp.async.cg.shared::cta.global.L2::128B"
    [at' "%r0", at' "%rd0", .literal "16"] = .ok (.cpAsync 0 0 8 0 16 .full none) := rfl
-- Only 4, 8 and 16 are cp-sizes; `.cg` takes only 16.
example : isOk (Decode.op env "cp.async.ca.shared.global"
    [at' "%r0", at' "%rd0", .literal "12"]) = false := rfl
example : isOk (Decode.op env "cp.async.ca.shared.global"
    [at' "%r0", at' "%rd0", .literal "2"]) = false := rfl
example : isOk (Decode.op env "cp.async.cg.shared.global"
    [at' "%r0", at' "%rd0", .literal "8"]) = false := rfl
example : isOk (Decode.op env "cp.async.cg.shared.global"
    [at' "%r0", at' "%rd0", .literal "4"]) = false := rfl
-- A cache hint needs its operand.
example : isOk (Decode.op env "cp.async.cg.shared.global.L2::cache_hint"
    [at' "%r0", at' "%rd0", .literal "16"]) = false := rfl
-- Group instructions.
example : Decode.op env "cp.async.commit_group" [] = .ok .cpAsyncCommit := rfl
example : Decode.op env "cp.async.wait_group" [.literal "1"] = .ok (.cpAsyncWait false 1) := rfl
example : Decode.op env "cp.async.wait_all" [] = .ok (.cpAsyncWait true 0) := rfl
-- `cp.async.mbarrier.arrive` names a `.shared` or `.shared::cta` mbarrier; the generic form is
-- not modeled.
example : Decode.op env "cp.async.mbarrier.arrive.shared::cta.b64" [at' "%r0"] =
    .ok (.cpAsyncArrive false 0 0) := rfl
example : Decode.op env "cp.async.mbarrier.arrive.noinc.shared::cta.b64" [at' "%r0"] =
    .ok (.cpAsyncArrive true 0 0) := rfl
example : Decode.op env "cp.async.mbarrier.arrive.shared.b64" [at' "%r1"] =
    .ok (.cpAsyncArrive false 1 0) := rfl
-- A generic address takes a 64-bit register.
example : Decode.op env "cp.async.mbarrier.arrive.b64" [at' "%rd0"] =
    .ok (.cpAsyncArrive false 8 0 true) := rfl
example : Decode.op env "cp.async.mbarrier.arrive.noinc.b64" [at' "%rd0"] =
    .ok (.cpAsyncArrive true 8 0 true) := rfl

/-! ## Thread events -/

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 64)
  | 1 => some (.bits 64 4096)
  | 2 => some (.bits 32 3)
  | 3 => some (.bits 32 5)
  | 4 => some (.pred true)
  | 5 => some (.pred false)
  | 6 => some (.bits 32 68)
  | 7 => some (.bits 64 4100)
  | 8 => some (.bits 32 128)
  | 9 => some (.bits 32 132)
  | 10 => some (.bits 64 7)
  | _ => none }

private def acc (l : Loc) (n : Nat) : Acc := { loc := l, size := n }
private def sh (a : Nat) : Loc := ⟨.shared, 0, a⟩
private def gl (a : Nat) : Loc := ⟨.global, 0, a⟩
/-- A `cp.async` operation: generic proxy. -/
private def eff (r w : Option (List Byte)) (n : Bool) : AsyncCopy.Effects :=
  { readBytes := r, writeBytes := w, notified := n }
private def sp (s d : Acc) (c : AsyncCopy.Completion) : AsyncCopy.Spec :=
  { src := s, dst := d, completion := c, generic := true }

/-- The copy spec and continuation (pc, sub) of an issue event. -/
private def issued : Tmpl → Option (AsyncCopy.Spec × Nat × Nat)
  | .copy s u => some (s, u.pc, u.sub)
  | _ => none
private def fault : Tmpl → Option Fault
  | .ub f => some f
  | _ => none
private def ca (d s size : Nat) (src : CpAsyncSource) (p : Option Opnd := none) : Op :=
  .cpAsync d 0 s 0 size src p

private def tm := cpAsyncTmpl L 0 t
-- A full copy of 4 bytes, and of 16 bytes: the destination is the `cp-size` bytes at `dst`.
example : issued (tm (ca 0 1 4 .full)) =
    some ((sp (acc (gl 4096) 4) (acc (sh 64) 4) (.asyncGroup)), 1, 0) := rfl
example : issued (tm (ca 0 1 16 .full)) =
    some ((sp (acc (gl 4096) 16) (acc (sh 64) 16) (.asyncGroup)), 1, 0) := rfl
-- `src-size` 3 of `cp-size` 4 reads 3 bytes and writes 4; 5 is larger than the cp-size.
example : issued (tm (ca 0 1 4 (.size (.reg 2)))) =
    some ((sp (acc (gl 4096) 3) (acc (sh 64) 4) (.asyncGroup)), 1, 0) := rfl
example : issued (tm (ca 0 1 4 (.size (.imm 4)))) =
    some ((sp (acc (gl 4096) 4) (acc (sh 64) 4) (.asyncGroup)), 1, 0) := rfl
example : fault (tm (ca 0 1 4 (.size (.reg 3)))) = some .badValue := rfl
-- `ignore-src` true reads nothing, false reads all bytes.
example : issued (tm (ca 0 1 4 (.ignore (.reg 4)))) =
    some ((sp (acc (gl 4096) 0) (acc (sh 64) 4) (.asyncGroup)), 1, 0) := rfl
example : issued (tm (ca 0 1 4 (.ignore (.reg 5)))) =
    some ((sp (acc (gl 4096) 4) (acc (sh 64) 4) (.asyncGroup)), 1, 0) := rfl
-- `ignore-src` must be a predicate.
example : fault (tm (ca 0 1 4 (.ignore (.reg 2)))) = some .typeMismatch := rfl
-- Both addresses are aligned to the cp-size.
example : fault (tm (ca 6 1 8 .full)) = some .misaligned := rfl
example : fault (tm (ca 0 7 8 .full)) = some .misaligned := rfl
example : issued (tm (ca 6 7 4 .full)) =
    some ((sp (acc (gl 4100) 4) (acc (sh 68) 4) (.asyncGroup)), 1, 0) := rfl
example : fault (tm (ca 6 7 16 .full)) = some .misaligned := rfl
-- A cache policy is a defined 64-bit value with no other effect.
example : issued (tm (ca 0 1 16 .full (some (.reg 10)))) = issued (tm (ca 0 1 16 .full)) := rfl
example : fault (tm (ca 0 1 16 .full (some (.reg 20)))) = some .uninitialized := rfl
-- Commit and wait are one event each; `wait_all` is a commit and then a wait of no group.
example : (match tm .cpAsyncCommit with | .asyncCommit u => some u.pc | _ => none) = some 1 := rfl
example : (match tm (.cpAsyncWait false 2) with | .asyncWait n u => some (n, u.pc) | _ => none)
    = some (2, 1) := rfl
example : (match tm (.cpAsyncWait true 0) with | .asyncCommit u => some (u.pc, u.sub) | _ => none)
    = some (0, 1) := rfl
example : (match cpAsyncTmpl L 0 { t with sub := 1 } (.cpAsyncWait true 0) with
    | .asyncWait n u => some (n, u.pc, u.sub) | _ => none) = some (0, 1, 0) := rfl
-- `cp.async.mbarrier.arrive` names the 8-byte aligned mbarrier and records `.noinc`.
example : (match tm (.cpAsyncArrive false 8 0) with
    | .asyncArrive m n u => some (m, n, u.pc) | _ => none) = some (sh 128, false, 1) := rfl
example : (match tm (.cpAsyncArrive true 8 0) with
    | .asyncArrive m n u => some (m, n, u.pc) | _ => none) = some (sh 128, true, 1) := rfl
example : fault (tm (.cpAsyncArrive false 9 0)) = some .misaligned := rfl
-- Any other instruction is not an event of this rule.
example : fault (tm .ret) = some .noRule := rfl

/-! ## Zero fill -/

private def b0 : Byte := (Value.bits 8 1, 0)
private def b1 : Byte := (Value.bits 8 2, 0)
private def b2 : Byte := (Value.bits 8 3, 0)
private def other : Byte := (Value.bits 8 9, 0)
private def shortSpec : AsyncCopy.Spec := (sp (acc (gl 4096) 3) (acc (sh 64) 4) (.asyncGroup))

example : AsyncCopy.CopyOk shortSpec (eff (some [b0, b1, b2]) (some [b0, b1, b2,
    AsyncCopy.zeroByte]) false) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro bs h; simp only [eff, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · intro bs h; cases h; simp [eff, shortSpec, sp, acc, AsyncCopy.sourceBytes]
  · intro h; cases h
  · exact ⟨fun j bs h => by simp [eff] at h, fun j bs h => by simp [eff] at h⟩
example : ¬ AsyncCopy.CopyOk shortSpec (eff (some [b0, b1, b2]) (some [b0,
                                         b1, b2, other]) false) := by
  intro h
  have hw := h.2.2.1 _ rfl
  simp [eff, shortSpec, sp, acc, other, AsyncCopy.sourceBytes, AsyncCopy.zeroByte,
      Value.byteAt] at hw
-- The written bytes need all the zero bytes of the destination.
example : ¬ AsyncCopy.CopyOk shortSpec (eff (some [b0, b1, b2]) (some [b0,
                                         b1, b2]) false) := by
  intro h
  have hw := h.2.2.1 _ rfl
  simp [eff, shortSpec, sp, acc, AsyncCopy.sourceBytes] at hw
-- A `cp.async` completes through its group; it never has a notification.
example : ¬ AsyncCopy.CopyOk shortSpec
    (eff (some [b0, b1, b2]) (some [b0, b1, b2, AsyncCopy.zeroByte]) true) := by
  intro h
  obtain ⟨⟨m, hm⟩, _⟩ := h.2.2.2.1 rfl
  simp [shortSpec, sp] at hm

/-! ## Group membership -/

private def spec (c : AsyncCopy.Completion) : AsyncCopy.Spec :=
  (sp (acc (gl 4096) 4) (acc (sh 64) 4) (c))
private def ev (k : Kind) : Event := ⟨0, k⟩
private def cpa : Event := ev (.copy (spec .asyncGroup))
private def bulk : Event := ev (.copy (spec .bulkGroup))
private def viaMbar : Event := ev (.copy (spec (.mbarrier (sh 128))))

-- A `cp.async` at position 0, committed, then waited with no group left out, is observed.
private def committed : List Event := [cpa, ev .asyncCommit, ev (.asyncWait 0)]
example : asyncActions 0 committed = [.issue (0, 0), .commit, .wait .full 0] := rfl
example : BulkGroup.Observes (BulkGroup.run (asyncActions 0 (committed.take 2))) 0 (0, 0) := by
  simp [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, asyncActions, committed, cpa, ev,
    spec, sp, asyncAction, BulkGroup.step, List.zipIdx]
-- A `cp.async` after the last commit is pending, so no wait observes it.
private def uncommitted : List Event := [cpa, ev .asyncCommit, cpa, ev (.asyncWait 0)]
example : (BulkGroup.run (asyncActions 0 (uncommitted.take 3))).pending = [(0, 2)] := rfl
example : (BulkGroup.run (asyncActions 0 (uncommitted.take 3))).groups = [[(0, 0)]] := rfl
example : ¬ BulkGroup.Observes (BulkGroup.run (asyncActions 0 (uncommitted.take 3))) 0 (0, 2) := by
  simp [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, asyncActions, uncommitted, cpa,
    ev, spec, sp, asyncAction, BulkGroup.step, List.zipIdx]
example : BulkGroup.Observes (BulkGroup.run (asyncActions 0 (uncommitted.take 3))) 0 (0, 0) := by
  simp [BulkGroup.Observes, BulkGroup.required, BulkGroup.run, asyncActions, uncommitted, cpa,
    ev, spec, sp, asyncAction, BulkGroup.step, List.zipIdx]
-- `wait_group 1` leaves the most recent group out.
private def twoGroups : List Event :=
  [cpa, ev .asyncCommit, cpa, ev .asyncCommit, ev (.asyncWait 1)]
private def twoState := BulkGroup.run (asyncActions 0 (twoGroups.take 4))
example : twoState.groups = [[(0, 0)], [(0, 2)]] := rfl
example : BulkGroup.Observes twoState 1 (0, 0) := by
  simp [BulkGroup.Observes, BulkGroup.required, twoState, twoGroups, BulkGroup.run, asyncActions,
    cpa, ev, spec, sp, asyncAction, BulkGroup.step, List.zipIdx]
example : ¬ BulkGroup.Observes twoState 1 (0, 2) := by
  simp [BulkGroup.Observes, BulkGroup.required, twoState, twoGroups, BulkGroup.run, asyncActions,
    cpa, ev, spec, sp, asyncAction, BulkGroup.step, List.zipIdx]
example : BulkGroup.Observes twoState 0 (0, 2) := by
  simp [BulkGroup.Observes, BulkGroup.required, twoState, twoGroups, BulkGroup.run, asyncActions,
    cpa, ev, spec, sp, asyncAction, BulkGroup.step, List.zipIdx]
-- The completion mechanism selects the group family: a bulk-group copy is no `cp.async` member and
-- a `cp.async` is no bulk-group member, and an mbarrier copy is in neither.
example : asyncAction 0 3 bulk.kind = none := rfl
example : bulkAction 0 3 cpa.kind = none := rfl
example : bulkAction 0 3 bulk.kind = some (.issue (0, 3)) := rfl
example : asyncAction 0 3 cpa.kind = some (.issue (0, 3)) := rfl
example : asyncAction 0 3 viaMbar.kind = none := rfl
example : bulkAction 0 3 viaMbar.kind = none := rfl
-- `cp.async` commits and waits are not bulk-group actions.
example : bulkAction 0 3 .asyncCommit = none := rfl
example : bulkAction 0 3 (.asyncWait 0) = none := rfl
example : asyncAction 0 3 .bulkCommit = none := rfl
example : asyncActions 0 [bulk, ev .asyncCommit, bulk] = [.commit] := rfl

/-! ## The pending-count increment of an mbarrier -/

open MBarrier in
private def obj (pending : Nat) : State := ⟨0, 4, pending, 0, true⟩

open MBarrier in
example : perform (some (obj 2)) .increment = .ok ⟨some (obj 3), none, none⟩ := rfl
open MBarrier in
example : perform (some (obj (limit - 1))) .increment = .ok ⟨some (obj limit), none, none⟩ := rfl
open MBarrier in
example : perform (some (obj limit)) .increment = .error .countRange := rfl
open MBarrier in
example : perform none .increment = .error .invalidObject := rfl

end

end PTX.Tests.AsyncCpAsync

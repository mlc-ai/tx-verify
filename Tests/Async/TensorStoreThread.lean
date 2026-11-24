-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Lemmas.Async.BulkExecution
public import Mathlib.Tactic

namespace PTX.Tests.TensorStoreThread
noncomputable section

private def descriptor : TensorDescriptor.Descriptor 1 :=
  ⟨.f16, 4096, ![8192, 8192], ![16384], ⟨![64, 128], ![1, 1]⟩, .b128, .zero, .small⟩
private def L : Launch := {
  grid := 2, block := 128, params := fun _ => none,
  tensorMaps := fun a => if a = 1024 then some ⟨1, descriptor⟩ else none }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 128)
  | 1 => some (.bits 64 1024)
  | 2 => some (.bits 64 0)
  | _ => none }
private def op : Op := .cpTensorStore (.reg 1) [(.imm 64), (.imm 128)] 0 0 (some (.reg 2)) .tile
    none
private def spec : TensorStore.Spec := ⟨⟨1, descriptor, ![64, 128], ⟨.shared, 0, 128⟩, none⟩, none⟩
private def env : Decode.Env :=
  { classes := [⟨"r".toList, 1, 32⟩, ⟨"rd".toList, 2, 64⟩], labels := [], params := [] }

-- Production syntax, including the cache-hint operand.
example : Decode.op env "cp.async.bulk.tensor.2d.global.shared::cta.tile.bulk_group.L2::cache_hint"
    [.address [.register "rd0", .vector [.literal "64", .literal "128"]],
      .address [.register "r0"], .register "rd1"] = .ok op := rfl
example : Decode.op env "cp.async.bulk.commit_group" [] = .ok .bulkCommit := rfl
example : Decode.op env "cp.async.bulk.wait_group.read" [.literal "1"] = .ok (.bulkWait .read 1) :=
    rfl
example : Decode.op env "cp.async.bulk.wait_group" [.literal "0"] = .ok (.bulkWait .full 0) := rfl
example : Decode.op env "cp.async.bulk.wait_group.sync_restrict::proxy::async" [.literal "2"] =
    .ok (.bulkWait .asyncProxy 2) := rfl
example : Decode.op env "cp.async.bulk.wait_group" [.literal "-1"] =
    .error "negative bulk wait count" := rfl

private theorem issue_eq : tensorStoreTmpl L 0 t op = .tensorStore 1024 spec (next t) := by
  change Tmpl.tensorStore 1024 { spec with origin := (fun axis : Fin 2 =>
                                           (BitVec.ofNat 32 (([truncBits 32 (BitVec.ofInt 64 (64)),
    truncBits 32 (BitVec.ofInt 64 (128))] : List (BitVec 64)).getD axis.val 0).toNat).toInt) } (next
    t) = _
  have h : (fun axis : Fin 2 => (BitVec.ofNat 32 (([truncBits 32 (BitVec.ofInt 64 (64)),
    truncBits 32 (BitVec.ofInt 64 (128))] : List (BitVec 64)).getD axis.val 0).toNat).toInt) =
    spec.origin := by
    funext axis; fin_cases axis <;> rfl
  rw [h]
example : eventTmpl [] L 0 t op = .tensorStore 1024 spec (next t) := issue_eq
example : op.isLocal = false := rfl
example : eventTmpl [] L 0 t .bulkCommit = .bulkCommit (next t) := rfl
example : eventTmpl [] L 0 t (.bulkWait .read 1) = .bulkWait .read 1 (next t) := rfl
example : tensorStoreTmpl L 0 t
    (.cpTensorStore (.reg 1) [(.imm (-1)), (.imm 0)] 0 0 none .tile none) = .ub .badValue := rfl
example : tensorStoreTmpl L 0 t
    (.cpTensorStore (.reg 1) [(.imm 0), (.imm 0)] 0 1 none .tile none) = .ub .misaligned := rfl

private def X : Execution := {
  tr := fun g => if g = 0 then
      [⟨0, .fenceProxy (.async (some (.shared .cta))) none⟩, ⟨1, .tensorStore 1024 spec⟩,
        ⟨2, .bulkCommit⟩, ⟨3, .tensorStore 1024 spec⟩, ⟨4, .bulkCommit⟩,
        ⟨5, .bulkWait .read 1⟩]
    else [], rf := fun _ _ => none }
example : BulkWaitsFor X .read (0, 1) (0, 5) := by
  refine ⟨5, 1, rfl, ?_⟩
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions,
    bulkAction, X, BulkGroup.run, BulkGroup.step]
example : ¬ BulkWaitsFor X .read (0, 3) (0, 5) := by
  rintro ⟨pc, n, he, ho⟩
  cases he
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions,
    bulkAction, X, BulkGroup.run, BulkGroup.step] at ho
example : ¬ BulkWaitsFor X .read (1, 1) (0, 5) := by
  intro h
  have hn : (1 : Nat) = 0 := h.same_thread
  contradiction

-- A committed output copy still needs full completion, independently of read waits.
example : ¬ AsyncDrained X := by
  intro h
  have hf : AsyncCopy.FinalStage X (0, 1) .fullDone :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨1024, spec, ⟨1, rfl⟩, rfl⟩))))))
  obtain ⟨o, ho, _⟩ := h (0, 1) .fullDone hf
  cases ho

end
end PTX.Tests.TensorStoreThread

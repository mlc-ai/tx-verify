-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Kernel.Statements

-- Loaded so that the boundary traversal below can follow Mathlib's private imports.
import Mathlib.Data.List.Enum
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Kernels.Fp16Gemm8192.Audit.Decode
public import Kernels.Fp16Gemm8192.Audit.PeerCvtaAudit
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Reuse
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Layout
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Layout

/-! The three public production theorems are audited for their exact statements,
standard axioms, and a recursively reviewed specification/assumption/data boundary. -/

namespace PTX.Kernels.Fp16Gemm8192

example {P : Params} {L : Launch} {mem0 : Mem0} :
    Pre P L mem0 →
      Correct kernel [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.pollAgree] L
        mem0 (Post P mem0) :=
  correct

example {P : Params} {L : Launch} {mem0 : Mem0} :
    Pre P L mem0 → ∃ X,
      Consistent L kernel
        [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.pollAgree] mem0 X ∧
        Complete L X :=
  completed_execution

example {P : Params} {L : Launch} {mem0 : Mem0} :
    Pre P L mem0 → ∃ X mf,
      Consistent L kernel
        [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.pollAgree] mem0 X ∧
      Complete L X ∧ IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  realizable_result

end PTX.Kernels.Fp16Gemm8192

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``PTX.Kernels.Fp16Gemm8192.correct,
    ``PTX.Kernels.Fp16Gemm8192.completed_execution,
    ``PTX.Kernels.Fp16Gemm8192.realizable_result,
    ``PTX.Kernels.Fp16Gemm8192.decode_eq,
    ``PTX.Kernels.Fp16Gemm8192.PeerCvtaAudit.production_narrowing_preserves_peer,
    ``PTX.mbarWait_fires_owner,
    ``PTX.Kernels.Fp16Gemm8192.Proof.safe_goal,
    ``PTX.Kernels.Fp16Gemm8192.Proof.progress_goal,
    ``PTX.Kernels.Fp16Gemm8192.Proof.bound_goal,
    ``PTX.Kernels.Fp16Gemm8192.Proof.result_goal,
    ``PTX.PairTmaRing.ring,
    ``PTX.Kernels.Fp16Gemm8192.Proof.InputRing.fault_free,
    ``PTX.PairTmaRing.consumer_observes,
    ``PTX.PairTmaRing.producer_observes,
    ``PTX.Kernels.Fp16Gemm8192.Proof.InputRing.copy_observed,
    ``PTX.PairTmaRing.read_observed,
    ``PTX.Kernels.Fp16Gemm8192.Proof.InputRing.copy_writeLoc,
    ``PTX.Kernels.Fp16Gemm8192.Proof.InputRing.mma_byteLoc,
    ``PTX.Kernels.Fp16Gemm8192.Proof.InputRing.stageByte_inj,
    ``PTX.Kernels.Fp16Gemm8192.Proof.OutputRing.stagingOff_inj] do
    for ax in ← collectAxioms name do
      unless ax ∈ PTX.StatementCheck.standardAxioms do
        throwError "{name} uses unexpected axiom {ax}"
  -- Traverse the actual imported-module graph, including through reviewed Core
  -- modules, so an indirect proof import cannot enter the specification.
  let dataModules : List Name := [`Kernels.Fp16Gemm8192.Spec,
    `Kernels.Fp16Gemm8192.Assumptions, `Kernels.Fp16Gemm8192.Data.Decoded,
    `Kernels.Fp16Gemm8192.Data.TensorMaps]
  let mut pending := dataModules
  let mut seen : List Name := []
  while !pending.isEmpty do
    let moduleName := pending.head!
    pending := pending.tail!
    unless moduleName ∈ seen do
      seen := moduleName :: seen
      -- Mathlib imports these separately packaged libraries. They are not
      -- production program data and remain outside the exact kernel whitelist.
      let library := ["Aesop", "Qq", "ProofWidgets", "ImportGraph",
        "Plausible", "LeanSearchClient", "Cli"].any fun pkg =>
          moduleName.toString == pkg || moduleName.toString.startsWith (pkg ++ ".")
      unless PTX.StatementCheck.reviewed "Fp16Gemm8192" moduleName || library do
        throwError "specification transitively imports unreviewed module {moduleName}"
      if moduleName.toString.startsWith "Kernels." then
        unless moduleName ∈ dataModules do
          throwError "specification imports non-whitelisted program data {moduleName}"
      -- A module that a dependency imports privately is named and checked above but not
      -- loaded, so its declarations cannot reach the specification (as in Tests/Kernel/Statements).
      if let some index := env.getModuleIdx? moduleName then
        for imp in env.header.moduleData[index.toNat]!.imports do
          pending := imp.module :: pending
  logInfo "production public statements, axioms and exact specification data boundary checked"

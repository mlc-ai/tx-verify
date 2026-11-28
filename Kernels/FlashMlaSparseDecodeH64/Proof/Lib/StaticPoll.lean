-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Clc.ClcExecution
public import Lemmas.Execution.ShapeExecution
public import Lemmas.Flow.CommitTarget
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.NotMatrix
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.StoreValid
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Flow.WarpUniform
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticSpinA
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticSpinB

@[expose] public section

/-! # The classes of `Unsafe` the decoded code excludes: guards and polls

No instruction compares a guard or an index between lanes (`noWarpDivergent`), and every poll is
in a canonical spin (`noPollShapeUnsafe`): static scans of the decoded program, each evaluated
once. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-! ### Guards and polls -/

set_option maxRecDepth 100000 in
private theorem noUniformGuards : kernel.noUniformGuards = true := by
  decide +kernel

/-- **ERR-NONUNIFORM-GUARD**: no instruction compares a guard or a branch index between lanes. -/
theorem noWarpDivergent : ¬ WarpDivergent l kernel A X :=
  not_warpDivergent noUniformGuards

set_option maxRecDepth 100000 in
private theorem pollSites : OpPcsFast kernel.code pollOp Flow.mbarWait.toList = true := by
  decide +kernel

/-- The polls of the code (`Flow.mbarWait`). -/
private theorem polls_eq : Flow.mbarWait.toList =
    [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534, 2644, 2677,
      2684] := by
  decide

private theorem waitLoopPcs_append (a b : List Nat) :
    kernel.waitLoopPcs (a ++ b) = (kernel.waitLoopPcs a && kernel.waitLoopPcs b) := by
  simp only [Kernel.waitLoopPcs, List.all_append]

private theorem waitLoops : kernel.waitLoopPcs Flow.mbarWait.toList = true := by
  rw [polls_eq, show [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534,
      2644, 2677, 2684] =
      [264, 272] ++
      [1184, 1931] ++
      [1983, 2012] ++
      [2107, 2205] ++
      [2209, 2234] ++
      [2245, 2446] ++
      [2534, 2644] ++
      [2677, 2684] from rfl]
  simp only [waitLoopPcs_append, waitLoops0, waitLoops1, waitLoops2, waitLoops3, waitLoops4,
    waitLoops5, waitLoops6, waitLoops7, Bool.and_self]

/-- Every mbarrier poll belongs to a canonical spin. -/
theorem poll_canonical (hX : Consistent l kernel A m X) {i : EvId} {site parity : Nat}
    {b : Loc} {ok acquire : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨site, .wait b parity ok acquire scope⟩) :
    ∃ exit, kernel.CanonicalSpin site exit := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      exact Kernel.canonicalSpin_of_waitLoopPcs pollSites waitLoops hc hop
    · push Not at hw
      exact absurd rfl (fires_notWait (eventTmpl_notWait hw) hf b parity ok acquire scope)

/-- **The poll sites**: a poll of a consistent execution is at one of the sixteen `mbarrier`
waits of the code. -/
theorem poll_pcs (hX : Consistent l kernel A m X) {i : EvId} {site parity : Nat}
    {b : Loc} {ok acquire : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨site, .wait b parity ok acquire scope⟩) :
    site ∈ [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534, 2644,
      2677, 2684] := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      have hp : pollOp ins.op = true := by rw [hop]; rfl
      rw [← polls_eq]
      exact OpPcsFast.mem pollSites hc hp
    · push Not at hw
      exact absurd rfl (fires_notWait (eventTmpl_notWait hw) hf b parity ok acquire scope)

/-- **ERR-POLL-SHAPE**: every poll is a canonical spin. -/
theorem noPollShapeUnsafe (hX : Consistent l kernel A m X) : ¬ PollShapeUnsafe kernel X := by
  rintro ⟨i, pc, b, q, ok, acq, sc, he, hn, _⟩
  exact hn (poll_canonical hX he)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

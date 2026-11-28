-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Guard
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Lemmas.Quiet.Step.CpDrainVisible
public import Lemmas.Quiet.Progress.AsyncCp
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Lemmas.Flow.TcStLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WriteBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaLayout
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Foot
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Apart
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Issue
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.CpBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqVisible
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PvVisible
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem

@[expose] public section

/-! # Progress class: the `tcgen05` completions and commits

An open MMA obligation steps (`Sched.mma_steps_cpV`) when every MMA operand byte has a visible
write (`Prog.operandVisible`: the B bytes are the dequantized tile's, `dq_visible`; the PV MMA's A
bytes are the P tile's, `pv_visible`; a QK MMA reads no A byte from shared memory), the copies'
sources are fixed (`Prog.cpSources`: the copy's read keeps the Tensor Memory rule, `cp_readOk`, and
each source byte has its query load, `cp_bytes`), the A operands in Tensor Memory are apart from
the writes (`mma_aApart`), the layouts are injective and the kernel has no shift. An open commit
obligation steps (`Sched.commit_stepsQ`) when the MMAs it tracks have started, and otherwise the
descent goes to an open MMA, which has no pending copy or MMA after the drain. Inputs:
`Top.Inputs` (`mbar`, `initRows`, `bar0`, `dequant`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The MMAs' operand bytes have visible writes.** -/
theorem Prog.operandVisible (hp : Pre P L m) (hIn : Top.Inputs P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) :
    OperandVisible L X := by
  have hT := tmem_rows hp hX hFw
  have hR := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  refine ⟨TmRace.mma_warpUnique hX hT (mmaOne hp hX hFw), ?_⟩
  rintro ⟨g, i⟩ bb sp acc mask ⟨pc, hx⟩ -
  obtain ⟨hg, hon, hv⟩ := TmRace.mma_on hX hT hx
  refine ⟨hv, fun isB idx loc hF => ⟨?_, fun w a bs hw hc _ => wbyte_of_write hX hw hc⟩⟩
  rcases mmaFoot_pv hp hX hFw hg hx hon.1 hF with
    ⟨b0, hl⟩ | ⟨hl, hl8, pc', b', s', acc', mask', hev, hb, hisB⟩
  · exact dq_visible hp hX hFw hR hI hB hN hx hon.1 hF hl
  · simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, -, -, -⟩ := hev
    subst hisB
    exact pv_visible hp hX hFw hR hI hB hx hb hon.1 hF hl hl8

/-- **The copies' sources are fixed** (`CpSourcesT`). -/
theorem Prog.cpSources (hp : Pre P L m) (hIn : Top.Inputs P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) :
    CpSourcesT L Assumptions.all X := by
  have hR := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  rintro ⟨g, i⟩ c hi - hd
  obtain ⟨pc, hcp⟩ := id hi
  exact ⟨cp_readOk hp hX hFw hR hI hB hi hd hcp, fun k => cp_bytes hp hX hFw hR hI hB hi k.isLt⟩

/-- A thread's commits target the same ranks. -/
private theorem Prog.commitPrev (hp : Pre P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ (g j j' pc pc' : Nat) (sp sp' : TcCommit.Spec) (rank : Fin 16) (l : Loc),
      X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → (fun _ => true) pc = true →
      X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ → j < j' →
      TcCommit.target sp' rank = some l → ∃ l', TcCommit.target sp rank = some l' :=
  fun _ _ _ _ _ _ _ _ _ he _ he' _ hit => mma_commitPrev hp hX he he' hit

/-- **An open MMA or commit obligation steps.** -/
theorem Prog.tc (hp : Pre P L m) (hIn : Top.Inputs P L m) :
    Prog.AsyncSteps P L m [.mma, .commit] := by
  intro hs X hmax hFw o ho hob
  have hnu := Sched.safe_noUb (hs.2 X hmax.1)
  have hT := tmem_rows hp hmax.1 hFw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact Sched.mma_steps_cpV wfQuiet_all hmax (Prog.guarded hs hmax.1)
      (Prog.operandVisible hp hIn hmax.1 hFw) (TmRace.mma_aApart hp hmax.1 hT)
      (mmaLayoutInjective hmax.1) (Prog.cpSources hp hIn hmax.1 hFw)
      (fun _ _ ⟨pc, he⟩ => PTX.Flow.no_shift_of_code hmax.1 code_noShift he _ rfl) hob
  · by_cases starts : ∀ x i, AsyncCopy.TracksMma X x i → X.async.mmaStarted x = true
    · exact Sched.commit_stepsQ wfQuiet_all hmax starts (Prog.commitPrev hp hmax.1) hob
    · push Not at starts
      obtain ⟨x, _, tracked, missing⟩ := starts
      obtain ⟨_, _, issue, _⟩ := tracked
      refine .inr ⟨X, .mma, hmax, fun drained => ?_, by simp [Sched.rank]⟩
      exact missing (hmax.1.tma.2.1.2 x (drained x issue))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

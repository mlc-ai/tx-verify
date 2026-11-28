-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Kernel.PlainStep
public import Lemmas.Tmem.PairProtocol
import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotTcData
import Lemmas.Flow.TcDataKind
import Lemmas.Flow.Next

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Tmem.Pair

/-- The positions of the program's `tcgen05.ld`, `tcgen05.st` and their waits: the Softmax
loop's eight and the epilogue's two. -/
def dataPcs : List Nat := [1265,1298,2260,2261,2328,2329,1009,1010,2607,2608]

private theorem hooks : dataPcs.all (fun p => !Assumptions.all.any (·.tcLdWait p) &&
    !Assumptions.all.any (·.tcStWaitLd p)) = true := by decide +kernel

private theorem shapes : dataPcs.all (fun p => (kernel.code[p]?).any (fun ins =>
    tcDataOp ins.op)) = true := by decide +kernel

private theorem only : kernel.code.zipIdx.all
    (fun x => !tcDataOp x.1.op || decide (x.2 ∈ dataPcs)) = true := by decide +kernel

/-- **A data event without undefined behaviour is at a data position, and the other way round.** -/
theorem tcdata_event {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get i = some e) (nu : ∀ f, e.kind ≠ .ub f) :
    isTcData e = decide (e.pc ∈ dataPcs) := by
  obtain ⟨f,bad⟩|⟨t,ins,o,tpc,code,fire⟩ := get_source hX get
  · exact (nu f bad).elim
  cases test : decide (e.pc ∈ dataPcs) with
  | false =>
    cases s : isTcData e with
    | false => rfl
    | true =>
      have op := fires_tcData_op fire s
      have h := List.all_eq_true.mp only (ins,e.pc) (List.mem_zipIdx_iff_getElem?.mpr code)
      simp only [op,Bool.not_true,Bool.false_or] at h
      exact absurd (of_decide_eq_true h) (of_decide_eq_false test)
  | true =>
    have hit := List.all_eq_true.mp shapes e.pc (of_decide_eq_true test)
    rw [code] at hit
    have hk := List.all_eq_true.mp hooks e.pc (of_decide_eq_true test)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    simp only [Option.any_some] at hit
    rcases fires_tcData_of_op fire hit (by rw [tpc]; exact hk.1) (by rw [tpc]; exact hk.2)
      with yes|⟨f,bad⟩
    · exact yes
    · exact (nu f bad).elim

/-- **A warp-collective `tcgen05` event without undefined behaviour is a resource operation or at
a data position.** -/
theorem tcColl_event {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get i = some e) (nu : ∀ f, e.kind ≠ .ub f) :
    isTcColl e = (isTmemOp e || decide (e.pc ∈ dataPcs)) := by
  rw [← tcdata_event hX get nu]
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [isTcColl, isTmemOp, isTcData, Bool.false_or]
  rename_i k
  cases k <;> simp only [Bool.false_or, Bool.true_or]

end PTX.Kernels.InklingRelDecode.Proof.Lib

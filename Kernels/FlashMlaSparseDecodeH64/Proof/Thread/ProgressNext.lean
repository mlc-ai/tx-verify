-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.ProgressDescent
public import Lemmas.Step.Released
public import Lemmas.Snoc.ExtensionSnoc
import Lemmas.Step.Issue
import Lemmas.Kernel.PlainStep

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The roles that are already at their local return or the common terminal state. -/
def ReturnSite : Machine.ThreadD → Prop
  | .done => True
  | .mma d => d.site = .exit
  | .tma d => d.site = .exit
  | .idle s => s = .exit
  | _ => False

/-- The running thread has a sound model beginning at launch. -/
abbrev SoundThreads (P : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, (Machine.code P L g).Sound

private theorem return_code {P : Params} {L : Launch} {g : Nat} {d : Machine.ThreadD}
    (hr : ReturnSite d) :
    kernel.code[(Machine.code P L g).pc d]? = some ⟨none, .ret⟩ := by
  cases d with
  | done => exact Flow.code_exit_0
  | mma d =>
    change d.site = .exit at hr
    change kernel.code[d.site.pc]? = _
    rw [hr]
    exact Flow.code_exit_0
  | tma d =>
    change d.site = .exit at hr
    change kernel.code[d.site.pc]? = _
    rw [hr]
    exact Flow.code_exit_0
  | idle s =>
    change s = .exit at hr
    change kernel.code[s.pc]? = _
    rw [hr]
    exact Flow.code_exit_0
  | _ => cases hr

/-- A defined non-coherent global load template performs the launch-memory read. -/
theorem read_nc_of_load {L : Launch} {g base : Nat} {t : TState} {dest : List Nat}
    (hOk : ∀ f, loadTmpl Assumptions.all L g t .global true 32 dest base 0 ≠ .ub f) :
    ∃ a k, loadTmpl Assumptions.all L g t .global true 32 dest base 0 = .readNC a k := by
  unfold loadTmpl at *
  cases hAddr : effAddr L g t .global base 0 >>= fun loc =>
      elemAcc loc (32 / 8) dest.length t.sub with
  | error f =>
    simp only [hAddr] at hOk
    exact (hOk f rfl).elim
  | ok a =>
    simp only [hAddr] at hOk ⊢
    have hNc : Assumptions.all.any (·.ncLoads t.pc) = true := by
      by_contra hn
      apply hOk .noRule
      simp [hn]
    exact ⟨a, afterLoad t dest, by simp [hNc]⟩

private theorem readonly_wf_snoc {L : Launch} {mem0 : Mem0} {X : Execution}
    {g site : Nat} {a : Acc} (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ asm ∈ Assumptions.all,
      asm.wf L mem0 (X.snoc g ⟨site, .nc a (X.launchBytes mem0 a)⟩ (fun _ => none)) := by
  intro asm hasm
  have hold := hX.asm asm hasm
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hasm
  rcases hasm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact TensorStore.ReadsDrainedBeforeExit.snoc hold (by simp)
    | intro j pc b bytes he hpc
      rw [snoc_get] at he
      split_ifs at he
      · obtain ⟨rfl, rfl⟩ := Kind.nc.inj (congrArg Event.kind (Option.some.inj he))
        refine ⟨by simp [Execution.launchBytes], fun k hk c hc => ?_⟩
        simp [Execution.launchBytes, List.getElem?_range hk, hc]
        rfl
      · exact hold j pc b bytes he hpc
    | exact Assumption.commitPerformedAt_extend (fun _ h => h) hold hX.tcCommit le_snoc
        (Execution.notifiedInOrder_of_eq (sel := Assumptions.commitOrder.commitInOrder) rfl)

/-- A released non-coherent read can take the bytes fixed at launch by the memory model. -/
theorem nc_extension {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {t u : TState}
    {a : Acc} {k : List (Option Byte) → TState}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ PTX.Step.Launched L X g) (hrel : PTX.Step.Released L X g)
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hτ : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u)
    (hout : out kernel Assumptions.all L g u = .ev (.readNC a k)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let bs := X.launchBytes mem0 a
  have hlen : bs.length = a.size := by simp [bs, Execution.launchBytes]
  refine PTX.Step.plain_counted_extension hX hg hne hrel hrun hτ
    (e := ⟨u.pc, .nc a bs⟩) (o := some (k bs)) ⟨_, hout, _, hlen, rfl, rfl⟩
    trivial rfl (by simp) (by simp) (by simp) rfl
    (hX.tmemPairResult.snoc_not_wr nofun) (readonly_wf_snoc hX)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

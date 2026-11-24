-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LseValue
public import Lemmas.Flow.NotTcMma
public import Lemmas.Flow.NotCommit

@[expose] public section

/-!
# The MMAs and their commits are the MMA warp's

The instructions of the program that issue a Tensor Core MMA or commit are exactly the MMA
warp's (`Mma.Site.qk`, `Mma.Site.pv`, the four commit sites), an audit by `decide +kernel` stated
through the site accessors. So an MMA or commit event of an execution fires from a state
`.w (.mma d P)` of a worker thread's machine, and has the shape `EvW.MmShape L g d e` of its site
(the QK and PV issues with their Tensor Memory columns, shared-memory starts and accumulate flags,
the four commits with their targets `s_ready`, `kv_empty`, `o_done`, `o_final`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The positions of the MMA warp's MMA and commit instructions. -/
def mmaPcs : List Nat :=
  [Mma.Site.qkCommit.pc, Mma.Site.pvCommit1.pc, Mma.Site.pvCommit2.pc, Mma.Site.finCommit.pc] ++
    (List.finRange 8).map (fun j => (Mma.Site.qk j).pc) ++
    (List.finRange 8).map (fun j => (Mma.Site.pv j).pc)

/-- Instructions that issue an MMA or a commit. -/
def mmaLikeOp (op : Op) : Bool := tcMmaOp op || commitOp op

/-- **The MMAs and commits of the program are the MMA warp's.** -/
theorem kernel_mma_pcs : OpPcsFast kernel.code mmaLikeOp mmaPcs = true := by
  decide +kernel

theorem dstart_pc_notMma (s : DStart.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals decide +kernel

theorem pro_pc_notMma (s : ProA.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals decide +kernel

theorem sm_pc_notMma (s : Sm.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem epi_pc_notMma (s : Epi.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_notMma (s : Worker.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals decide +kernel

theorem idle_pc_notMma (s : Worker.Idle.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_notMma (s : Loader.Site) : s.pc ∉ mmaPcs := by
  cases s
  all_goals decide +kernel

theorem exit_pc_notMma (s : WComp.ExitSite) : s.pc ∉ mmaPcs := by
  cases s
  all_goals decide +kernel

/-- **A state at an MMA or commit position is an MMA warp state.** -/
theorem mma_state {s : TSt} (h : TSt.pc s ∈ mmaPcs) : ∃ d P, s = .w (.mma d P) := by
  cases s with
  | d s =>
    cases s with
    | dstart d => exact absurd h (dstart_pc_notMma d.site)
    | pro d => exact absurd h (pro_pc_notMma d.site)
    | sm d => exact absurd h (sm_pc_notMma d.site)
    | epi d => exact absurd h (epi_pc_notMma d.site)
  | w s =>
    cases s with
    | worker w => exact absurd h (worker_pc_notMma w.site)
    | idle d => exact absurd h (idle_pc_notMma d.site)
    | loader d _ => exact absurd h (loader_pc_notMma d.site)
    | mma d P => exact ⟨d, P, rfl⟩
    | exit x => exact absurd h (exit_pc_notMma x.site)

/-- **An MMA or commit event is the MMA warp's.** The thread's machine is, before the event, at
a state `.w (.mma d P)`, and the event has the shape of the state's site. -/
theorem mma_event_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : (∃ dst sp acc mask, e.kind = .tc (.mma dst sp acc mask)) ∨
      ∃ sp, e.kind = .tc (.commit sp)) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      EvW.MmShape L g d e := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    rcases hk with ⟨_, _, _, _, h⟩ | ⟨_, h⟩ <;> cases h
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he hub
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : mmaLikeOp ins.op = true := by
    rcases hk with ⟨dst, sp, acc, mask, h⟩ | ⟨sp, h⟩
    · simp [mmaLikeOp, fires_tcMma_op hf h]
    · cases hq : commitOp ins.op
      · exfalso
        exact fires_notCommit (eventTmpl_notCommit (commitOp_ne hq)) hf sp h
      · simp [mmaLikeOp, hq]
  have hpw : TSt.pc s ∈ mmaPcs := OpPcsFast.mem kernel_mma_pcs hc hop
  obtain ⟨d, P, rfl⟩ := mma_state hpw
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  have hsome : ∃ u, o' = some u := by
    cases o' with
    | some u => exact ⟨u, rfl⟩
    | none =>
      exfalso
      obtain ⟨t', -, hf'⟩ := hF
      rcases fires_none_ends hf' with ⟨f, hf''⟩ | hx <;>
        rcases hk with ⟨_, _, _, _, h⟩ | ⟨_, h⟩ <;> simp_all
  obtain ⟨u, rfl⟩ := hsome
  obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
  exact ⟨d, P, hσ, EvW.mma_shape hpre hg (d := d) (P := P) ⟨t', ⟨ha, hi.2⟩, hf'⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

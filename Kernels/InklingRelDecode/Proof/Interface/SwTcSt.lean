-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootClass
public import Kernels.InklingRelDecode.Proof.Thread.SwShape
public import Lemmas.Flow.NotTcSt

@[expose] public section

/-!
# Which instructions store to Tensor Memory

The program has two `tcgen05.st` instructions: the softmax region's store of the probabilities
(`Sm.Site.tmemSt`) and of the rescaled `O` words (`Sm.Site.stO`). `kernel_tcst_pcs` is the audit
(`decide +kernel` through the site accessors); `tcst_state` says that a state at one of those
positions is a softmax-region state at one of the two sites (no other machine has a site there);
`tcst_event_state` says that the thread's state before a `tcgen05.st` event is one.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The positions of the `tcgen05.st` instructions. -/
def tcStPcs : List Nat := [Sm.Site.tmemSt.pc, Sm.Site.stO.pc]

/-- **The `tcgen05.st` instructions of the program are the probabilities' store and the rescale
store.** -/
theorem kernel_tcst_pcs : OpPcsFast kernel.code tcStOp tcStPcs = true := by
  decide +kernel

theorem sm_tcst_site (s : Sm.Site) (h : s.pc ∈ tcStPcs) : s = .tmemSt ∨ s = .stO := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem pro_pc_notTcSt (s : ProA.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals decide +kernel

theorem dstart_pc_notTcSt (s : DStart.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals decide +kernel

theorem epi_pc_notTcSt (s : Epi.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_notTcSt (s : Worker.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals decide +kernel

theorem idle_pc_notTcSt (s : Worker.Idle.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_notTcSt (s : Loader.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals decide +kernel

theorem mma_pc_notTcSt (s : Mma.Site) : s.pc ∉ tcStPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem exit_pc_notTcSt (s : WComp.ExitSite) : s.pc ∉ tcStPcs := by
  cases s
  all_goals decide +kernel

/-- **A worker state is at no `tcgen05.st` position.** -/
theorem worker_state_notTcSt (s : WComp.WSt) : WComp.pc s ∉ tcStPcs := by
  cases s with
  | worker w => exact worker_pc_notTcSt w.site
  | idle d => exact idle_pc_notTcSt d.site
  | loader d _ => exact loader_pc_notTcSt d.site
  | mma d _ => exact mma_pc_notTcSt d.site
  | exit x => exact exit_pc_notTcSt x.site

/-- **A state at a `tcgen05.st` position is the softmax region's probabilities' store or rescale
store.** -/
theorem tcst_state {s : TSt} (h : TSt.pc s ∈ tcStPcs) :
    ∃ d : Sm.D, s = .d (.sm d) ∧ (d.site = .tmemSt ∨ d.site = .stO) := by
  cases s with
  | w s => exact absurd h (worker_state_notTcSt s)
  | d s =>
    cases s with
    | dstart d => exact absurd h (dstart_pc_notTcSt d.site)
    | pro d => exact absurd h (pro_pc_notTcSt d.site)
    | sm d => exact ⟨d, rfl, sm_tcst_site d.site h⟩
    | epi d => exact absurd h (epi_pc_notTcSt d.site)

/-- **The state before a `tcgen05.st` event is a softmax-region state at the probabilities' store
or the rescale store.** -/
theorem tcst_event_state (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (g, k) = some ⟨pc, .tc (.st a vals sh)⟩) {s : TSt}
    (hσ : St Q L X g k = some (some s)) :
    ∃ d : Sm.D, s = .d (.sm d) ∧ (d.site = .tmemSt ∨ d.site = .stO) := by
  have hk : (⟨pc, .tc (.st a vals sh)⟩ : Event).kind = .tc (.st a vals sh) := rfl
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop := fires_tcSt_op hf hk
  have hmem : TSt.pc s ∈ tcStPcs := OpPcsFast.mem kernel_tcst_pcs hc hop
  exact tcst_state hmem

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

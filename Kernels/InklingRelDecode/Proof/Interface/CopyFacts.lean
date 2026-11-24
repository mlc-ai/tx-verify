-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.MmaFacts
public import Lemmas.Flow.NotTensor

@[expose] public section

/-!
# The tensor copies are the prologue's and the loader's

The instructions of the program that issue a tensor copy are exactly the default partition's 12
K/V preload copies (`ProA.ptcSites`) and the loader's eight (`Loader.Site.cp0a` to `cp3b`), an
audit by `decide +kernel` through the site accessors. So a tensor copy event of an execution fires
from a prologue state at one of the 12 sites, with the shape `ProA.shape_ptc` gives (the published
map, one CTA group, no cluster addressing, completing on `kv_ready (i / 4)` of the thread's CTA,
the destination and box origin of the site), or from a loader state `.w (.loader d P)`, with the
shape `EvW.LdShape` (`kvCopySpec`: the map, origin, destination, `kv_ready (i % 3)`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The positions of the tensor copies: the prologue's 12 and the loader's 8. -/
def copyPcs : List Nat :=
  ProA.ptcSites.map (·.pc) ++
    [Loader.Site.cp0a.pc, Loader.Site.cp0b.pc, Loader.Site.cp1a.pc, Loader.Site.cp1b.pc,
      Loader.Site.cp2a.pc, Loader.Site.cp2b.pc, Loader.Site.cp3a.pc, Loader.Site.cp3b.pc]

/-- **The tensor copies of the program are the prologue's and the loader's.** -/
theorem kernel_copy_pcs : OpPcsFast kernel.code tensorOp copyPcs = true := by
  decide +kernel

theorem dstart_pc_notCopy (s : DStart.Site) : s.pc ∉ copyPcs := by
  cases s
  all_goals decide +kernel

theorem pro_pc_copy (s : ProA.Site) (h : s.pc ∈ copyPcs) : s ∈ ProA.ptcSites := by
  revert h
  cases s
  all_goals decide +kernel

theorem sm_pc_notCopy (s : Sm.Site) : s.pc ∉ copyPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem epi_pc_notCopy (s : Epi.Site) : s.pc ∉ copyPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_notCopy (s : Worker.Site) : s.pc ∉ copyPcs := by
  cases s
  all_goals decide +kernel

theorem idle_pc_notCopy (s : Worker.Idle.Site) : s.pc ∉ copyPcs := by
  cases s
  all_goals decide +kernel

theorem mma_pc_notCopy (s : Mma.Site) : s.pc ∉ copyPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem exit_pc_notCopy (s : WComp.ExitSite) : s.pc ∉ copyPcs := by
  cases s
  all_goals decide +kernel

theorem ptc_index : ∀ s ∈ ProA.ptcSites, ∃ i < 12, s = ProA.ptcSite i := by
  decide

/-- **A tensor copy event is the prologue's or the loader's**, the loader's for every counter
(`EvW.LdShapeW`). -/
theorem copy_event_stateW (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : ∃ a sp, e.kind = .tensorIssue a sp) :
    (∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d))) ∧ ∃ i < 12,
      d.site = ProA.ptcSite i ∧ ∃ a s, e = ⟨ProA.evPc d.site, .tensorIssue a s⟩ ∧
        s.clusterAddress = false ∧ s.group = .one ∧
        s.mbar = (EvD.kvReadyOf (i / 4)).loc L (g / L.block) ∧
        s.sharedBase = ⟨.shared, g / L.block, ProA.copyDst L g d.dt i⟩ ∧ s.rows = none ∧
        (∀ ax : Fin (s.outer + 1), s.origin ax =
          (BitVec.ofNat 32 ([ProA.copyX L g d.dt i, ProA.copyY L g d.dt i].getD ax.val 0)).toInt) ∧
        ∃ desc, L.tensorMaps a = some ⟨s.outer, desc⟩ ∧ s.descriptor = desc) ∨
    (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      EvW.LdShapeW Q L g d e) := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    obtain ⟨_, _, h⟩ := hk
    cases h
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he hub
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : tensorOp ins.op = true := by
    cases hq : tensorOp ins.op
    · exfalso
      obtain ⟨a, sp, h⟩ := hk
      exact fires_notTensor (eventTmpl_notTensor hq) hf a sp h
    · rfl
  have hpw : TSt.pc s ∈ copyPcs := OpPcsFast.mem kernel_copy_pcs hc hop
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  have hsome : ∃ u, o' = some u := by
    cases o' with
    | some u => exact ⟨u, rfl⟩
    | none =>
      exfalso
      obtain ⟨t', -, hf'⟩ := hF
      obtain ⟨a, sp, h⟩ := hk
      exact fires_none_notTensor hf' a sp h
  obtain ⟨u, rfl⟩ := hsome
  have hr := treach_stateAt hpre hg hσ
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (by exact worker_pc_notCopy w.site)
    | idle d => exact absurd hpw (idle_pc_notCopy d.site)
    | mma d _ => exact absurd hpw (mma_pc_notCopy d.site)
    | exit x => exact absurd hpw (exit_pc_notCopy x.site)
    | loader d P =>
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      exact .inr ⟨d, P, hσ, EvW.loader_shapeW hpre (hr.2) ⟨t', ⟨ha, hi.2⟩, hf'⟩⟩
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (dstart_pc_notCopy d.site)
    | sm d => exact absurd hpw (sm_pc_notCopy d.site)
    | epi d => exact absurd hpw (epi_pc_notCopy d.site)
    | pro d =>
      obtain ⟨i, hi, hs⟩ := ptc_index _ (pro_pc_copy d.site hpw)
      obtain ⟨a, s, he2, h1, h2, h3, h4, h5, h6, h7⟩ :=
        ProA.shape_ptc (ProA.sharedOk_of_pre hpre) hi (fired_pro hF) hs
      exact .inl ⟨d, hσ, i, hi, hs, a, s, he2, h1, h2, h3, h4, h5, h6, h7⟩


/-- **A tensor copy event is the prologue's or the loader's**, the loader's below `2 ^ 31`
(`LdRng`). -/
theorem copy_event_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hrg : LdRng Q L X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : ∃ a sp, e.kind = .tensorIssue a sp) :
    (∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d))) ∧ ∃ i < 12,
      d.site = ProA.ptcSite i ∧ ∃ a s, e = ⟨ProA.evPc d.site, .tensorIssue a s⟩ ∧
        s.clusterAddress = false ∧ s.group = .one ∧
        s.mbar = (EvD.kvReadyOf (i / 4)).loc L (g / L.block) ∧
        s.sharedBase = ⟨.shared, g / L.block, ProA.copyDst L g d.dt i⟩ ∧ s.rows = none ∧
        (∀ ax : Fin (s.outer + 1), s.origin ax =
          (BitVec.ofNat 32 ([ProA.copyX L g d.dt i, ProA.copyY L g d.dt i].getD ax.val 0)).toInt) ∧
        ∃ desc, L.tensorMaps a = some ⟨s.outer, desc⟩ ∧ s.descriptor = desc) ∨
    (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      EvW.LdShape Q L g d e) := by
  rcases copy_event_stateW hpre hX hS ht hg he hk with h | ⟨d, P, hσ, hsh⟩
  · exact .inl h
  · exact .inr ⟨d, P, hσ, hsh.shape (EvW.sbOk_of_pre hpre) (hrg hg hσ).bndI⟩
end
end PTX.Kernels.InklingRelDecode.Proof.Interface

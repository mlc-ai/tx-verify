-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Lemmas.Flow.TensorStoreOrigin
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The store warp's tensor stores: their origin

Every tensor store is the store warp's (`Facts.store_tma_origin`): the kernel's tensor store
instructions are its four TMA sites (`kernel_store_pcs`), no other role has a site there, and the
event fires at a store state at a TMA site of an item below the count. Its specification is the
store of that half of that stage of that item (`Store.Ev`, `Store.tma_event`).

No store site has an undefined-behaviour template (`Cross.SitesTmplOk_store`): no shape of the
store warp's table is undefined behaviour (`Code.Shape.not_ub`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Only the store warp issues tensor stores -/

/-- The positions of the TMA stores. -/
abbrev tmaPcs : List Nat :=
  [Flow.tensorCopy_10, Flow.tensorCopy_11, Flow.tensorCopy_12, Flow.tensorCopy_13]

theorem kernel_store_pcs : OpPcsFast kernel.code tensorStoreOp tmaPcs = true := by
  decide +kernel

theorem Prologue.site_not_tma (s : Prologue.Site) : s.pc ∉ tmaPcs := by
  cases s <;> site_decide

theorem Loader.site_not_tma (s : Loader.Site) : s.pc ∉ tmaPcs := by
  cases s <;> site_decide

theorem Mma.site_not_tma (s : Mma.Site) : s.pc ∉ tmaPcs := by
  cases s <;> site_decide

theorem Softmax.site_not_tma (s : Softmax.Site) : s.pc ∉ tmaPcs := by
  cases s <;> site_decide

theorem Correction.site_not_tma (s : Correction.Site) : s.pc ∉ tmaPcs := by
  cases s <;> site_decide

theorem Idle.site_not_tma (s : Idle.Site) : s.pc ∉ tmaPcs := by
  cases s <;> site_decide

/-- **The origin of a tensor store**: a thread of warp 13, at a store state at a TMA site of an
item below the count, with the role's counts; the store of its half of its stage of its item. -/
theorem Facts.store_tma_origin (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc a : Nat} {s : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorStore a s⟩) :
    warpOf L g = 13 ∧ ∃ (st hh : Fin 2) (i : Nat),
      Frame.stateAt (code L) X g k = some (some (.inr (.store ⟨.tma st hh, i⟩))) ∧
      Store.Counts L g ⟨.tma st hh, i⟩ ((X.tr g).take k) ∧ i < Work.T L g ∧
      pc = (Store.Site.tma st hh).pc ∧ a = P.oMap ∧ s = oSpec P L g i st hh := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hpc := OpPcsFast.mem kernel_store_pcs hc (fires_tensorStore_op hf rfl)
  have hw : warpOf L g = 13 := by
    rcases d with p | r
    · exact absurd hpc (Prologue.site_not_tma p.site)
    have hw := Cross.role_of_state hpre hX hg hσ
    cases r with
    | idle s => exact absurd hpc (Idle.site_not_tma s.site)
    | loader l => exact absurd hpc (Loader.site_not_tma l.site)
    | mma m => exact absurd hpc (Mma.site_not_tma m.site)
    | softmax s => exact absurd hpc (Softmax.site_not_tma s.site)
    | corr c => exact absurd hpc (Correction.site_not_tma c.site)
    | store d => exact hw
  obtain ⟨⟨site, i⟩, hσ', hJ, hi, hev, hpc'⟩ := Facts.store_ev' hpre hX ht hg hw he nofun nofun
  cases site <;> simp only [Store.Ev, reduceCtorEq, exists_false] at hev
  case tma st hh =>
    simp only [Kind.tensorStore.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨hw, st, hh, i, hσ', hJ, (hi.resolve_left nofun) nofun, hpc', rfl, rfl⟩

/-- **The store warp's part of `Cross.SitesTmplOk`**: at a store state of the composed machine,
the site's instruction has no undefined-behaviour template. -/
theorem Cross.SitesTmplOk_store (hpre : Pre P L mem0) {g : Nat} (d : Store.D) (t : TState)
    (ins : Instr) (hat : (code L g).AtD (.inr (.store d)) t)
    (hi : (code L g).inv (.inr (.store d)))
    (hc : kernel.code[(code L g).pc (.inr (.store d))]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  Code.Shape.not_ub (Store.shape (g := g) hpre) (fun ⟨s, _⟩ e f hev hk => by
    cases s <;> simp_all [Store.Ev]) (d := d) hat hi hc f

end
end PTX.Kernels.FlashAttn4Fwd.Proof

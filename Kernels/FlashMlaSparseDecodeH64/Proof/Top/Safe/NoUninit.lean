-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst

@[expose] public section

/-! # ERR-MBAR-UNINITIALIZED: every mbarrier operand is initialized and published

The safety class of Core's `Unsafe` this file owns (`MbarUninit`), proved from the mbarrier
channel's startup side (`Protocol/Mbar/`) and the inputs `mbar`, `init`, `bar0` of `Top.Inputs`
(`Safe.init_pub`, also used by `Safe.noTma`).

An event `(h, k)` that names the object `l` and does not initialize it is a use of `h`'s role row
(`mbar_use`), so `l` is the object of a family `f` of `h`'s CTA (`use_cta`), and it follows a
barrier-0 event of `h` (`use_after_bar0`). The CTA has a winner `g` of the pc-31 election that
reaches barrier 0 (`InitRows.winner`), which initializes `f`'s object of the CTA before its
barrier-0 event (`won_inits`); barrier 0 publishes that initialization to `(h, k)` in base
causality order (`bar0_pub`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **An mbarrier use is published**: an event that names the object `l` and does not
initialize it has an initialization of `l` (the CTA winner's, before its barrier 0) that happens
before it. -/
theorem Safe.init_pub (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {h k : Nat}
    {ev : Event} {l : Loc} (hget : X.get (h, k) = some ev) (hm : Frame.MbarOf ev l)
    (hni : ∀ n, ev.kind ≠ .mbInit l n) :
    ∃ c f i, l = mbarLoc L c f ∧ X.MbInit i l f.count ∧ baseCausality L X i (h, k) := by
  have hh := Frame.lt_of_get hX hget
  obtain ⟨f, rfl⟩ := use_cta (mbar_use (hIn.mbar hp X hX hFw) hh hget hm)
  have hpos := use_after_bar0 hp hX hFw hget hm hni
  have hlen : k < (X.tr h).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr h)[k]? = some ev from hget)).1
  obtain ⟨g, j, kb, mk, inst, pcb, cnt, mode, hcg, hj, hb, h0j, h0b⟩ :=
    (hIn.initRows hp X hX hFw).winner hh (.inl hlen) hpos
  obtain ⟨i, hikb, pc, hgi⟩ := won_inits hp hX hFw hj rfl hb h0j h0b f
  rw [hcg] at hgi
  exact ⟨_, f, (g, i), rfl, ⟨pc, hgi⟩, bar0_pub hp hX hFw (hIn.bar0 hp X hX hFw)
    ⟨Frame.lt_of_get hX hgi, hh, hcg⟩ (bar0_none hikb h0b) hlen hpos⟩

/-- **ERR-MBAR-UNINITIALIZED**: every mbarrier operand is initialized and published. -/
theorem Safe.noUninit (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ MbarUninit L X := by
  rintro ⟨⟨h, k⟩, l, hu, hni, hbad⟩
  obtain ⟨⟨pce, kd⟩, hget, hm⟩ := Frame.usesMbar_mbarOf hu
  obtain ⟨-, f, i, -, hi, hc⟩ := Safe.init_pub hp hIn hX hFw hget hm
    fun n hn => hni n ⟨pce, hn ▸ hget⟩
  exact hbad ⟨i, f.count, hi, .inl hc⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

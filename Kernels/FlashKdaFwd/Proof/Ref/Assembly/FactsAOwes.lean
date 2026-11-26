-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsABase
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocolLib
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Exports

@[expose] public section

/-!
# Assembly, group A: the shares of the Compute phase and of the Store phase

`FactsABase.lean` proves the three contracts of group A from two structures of facts that the
Compute phase and the Store phase owe (`FactsA.ComputeOwes`, `FactsA.StoreOwes`). This file
proves the two structures from the export files of the two phases:

* `computeOwes` from `Compute/ExportsProtocolLib.lean` (`Compute.Proto.ev_at`: the event at a
  state of the phase is the closed-form event of the state's position, `Compute.Proto.EvAt`;
  a position is the entry or position `n < 268` of a tile `t`, the named barrier being
  position 264) and the phase's ledger (`Compute.led`: `t` named barriers before position 264
  of tile `t`);
* `storeOwes` from `Store/Exports.lean` (`Store.use_ev_store`, `Store.store_wait_left`).

It is a file of its own so that the proofs of the contracts do not depend on the export files
of the two phases.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- An event at a state of the Compute phase that names an mbarrier is one of the two polls or
of the two arrivals of a tile, each on an mbarrier of the thread's block. -/
theorem compute_mbar {g j0 k : Nat} {e : Event} {m : Loc} {s : D}
    (hs : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e m) : ∃ b : Bar, m = b.loc L (g / L.block) := by
  obtain ⟨pos, hR, -⟩ := hI
  have hev := Compute.Proto.ev_at hpre hX hR hs he
  obtain ⟨pc, kd⟩ := e
  cases pos with
  | entry =>
    cases hev
    exact hm.elim
  | tile t n =>
    simp only [Compute.Proto.EvAt] at hev
    split_ifs at hev
    · obtain ⟨ok, h⟩ := hev
      cases h
      exact ⟨.storeEmpty (Compute.stage2 t), hm⟩
    · obtain ⟨ok, h⟩ := hev
      cases h
      exact ⟨.loadFull (Compute.stage3 t), hm⟩
    · cases hev
      exact hm.elim
    · cases hev
      exact hm.elim
    · cases hev
      exact ⟨.storeFull (Compute.stage2 t), hm⟩
    · cases hev
      exact ⟨.loadEmpty (Compute.stage3 t), hm⟩
    · rcases hev with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;>
        (subst h; exact hm.elim)
    · rcases hev with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;>
        (subst h; exact hm.elim)

/-- **The Compute phase's share.** -/
theorem computeOwes : ComputeOwes P L X where
  bar8 := fun {g j0 k pc id cnt mode s} hs hI he h2913 => by
    have hpc : pc = s.site.pc := Frame.event_pc (sounds hpre) hX he hs
    obtain ⟨pos, hR, hl, -⟩ := hI
    have hev := Compute.Proto.ev_at hpre hX hR hs he
    cases pos with
    | entry =>
      cases hev
      omega
    | tile t n =>
      have ht : t < Compute.tilesOf P g := hR.facts.lt
      have h8 : ((X.tr g).take k).countP (Execution.isBarId 8) = t + Compute.ind 265 n :=
        congrArg Compute.Led.bar8 hl
      simp only [Compute.Proto.EvAt] at hev
      split_ifs at hev with h0 h1 h264
      · obtain ⟨ok, h⟩ := hev
        cases h
      · obtain ⟨ok, h⟩ := hev
        cases h
      · cases hev
        rw [h264] at h8
        exact ⟨rfl, rfl, rfl, by rw [h8]; exact ht⟩
      · cases hev
      · cases hev
      · cases hev
      · rcases hev with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
      · rcases hev with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;> cases h
  mbar := fun hs hI he hm => compute_mbar hpre hX hs hI he hm

/-- **The Store phase's share.** -/
theorem storeOwes : StoreOwes P L X where
  mbar := fun hs hI he hm => by
    obtain ⟨b, hb, -⟩ := Store.use_ev_store hpre hX (Frame.lt_of_get hX he) he hs hI hm
    exact ⟨b, hb⟩
  store_wait := fun h0 hin hk0 he hs hI hsj ho =>
    (Store.store_wait_left hpre hX (Frame.lt_of_get hX he) ⟨_, h0, hin⟩ hk0 he hs hI hsj ho).2

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsA

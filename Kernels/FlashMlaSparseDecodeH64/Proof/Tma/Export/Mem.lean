-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Tma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.CoordLoc

@[expose] public section

/-! # The TMA warp's memory accesses

`memRow_tma` (`MemRow.Tma`): from the shape table (`Tma/Ev.lean`, through `tma_at`), case by
site. A coordinate read of quadruple `q`, element `j`, reads the word at the quadruples' base
plus `coordOff q + 4 j`; in a block state the slot word is `W s` with `s < 4` (`LoopOk`), so the
base is the workspace byte `256 s` and the read is the workspace's `221728 + 256 s + 16 q + 4 j`
(`Tma.crd_loc`). `tma_mem_noMbar`: every memory access of the lane is a non-coherent read or ends
below the mbarriers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A memory event is no undefined behaviour. -/
private theorem memEvent_ub {e : Event} (hm : MemRow.MemEvent e) : ∀ f, e.kind ≠ .ub f := by
  rcases hm with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, o, n, h⟩ <;> intro f hf <;>
    rw [h] at hf <;> cases hf

/-- A coordinate read of the table, at a slot below 4, is a read of `TmaRd`. -/
private theorem crd_rd (hp : Pre P L m) {g : Nat} {d : Tma.D} {b j : Nat} (hb : b < 4)
    (hj : j < 4) (hs : d.slot = W b) (q : Fin 16) {e : Event} (hm : MemRow.MemEvent e)
    (h : RdAt L g (Tma.crdB L d) (Tma.coordOff q) 4 j e) :
    ∃ a bs, e.kind = .rd a bs ∧ MemRow.TmaRd L g a := by
  rcases h with ⟨a, bs, hk, hl, hsz⟩ | ⟨f, hf⟩
  · refine ⟨a, bs, hk, b, hb, q.val, q.isLt, j, hj, ?_, hsz⟩
    rw [hl, Tma.crd_loc hp hb hs q]
    simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  · exact absurd hf (memEvent_ub hm f)

/-- **Row `MemRow.Tma`**. -/
theorem memRow_tma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Tma P L X := by
  intro g k e _ he hat hm
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, hR, -, ⟨-, hE⟩, hl, -⟩ := tma_at hp hX hFw he (memEvent_ub hm) hr
  have hc := hR (lane5_take_noUb hX he)
  tma_state d
  cases s with
  | coord0 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, -⟩ := (Tma.core_loop rfl).mp hc
    exact .inr (crd_rd hp (Nat.mod_lt _ (by decide)) (by decide) hslot q hm hE)
  | coord1 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, -⟩ := (Tma.core_loop rfl).mp hc
    exact .inr (crd_rd hp (Nat.mod_lt _ (by decide)) (by decide) hslot q hm hE)
  | coord2 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, -⟩ := (Tma.core_loop rfl).mp hc
    exact .inr (crd_rd hp (Nat.mod_lt _ (by decide)) (by decide) hslot q hm hE)
  | coord3 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, -⟩ := (Tma.core_loop rfl).mp hc
    exact .inr (crd_rd hp (Nat.mod_lt _ (by decide)) (by decide) hslot q hm hE)
  | _ =>
    obtain ⟨pc, kd⟩ := e
    rcases hm with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ <;>
      simp [Tma.EvK, Tma.Poll] at hE ⊢
    all_goals exact absurd rfl (hl _)

/-- **No memory access of the TMA lane reaches the mbarriers**: a non-coherent read, or a shared
read of the lane's CTA ending below them. -/
theorem tma_mem_noMbar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hat : MbarRow.TmaAt L g e.pc) (hm : MemRow.MemEvent e) :
    (∃ a bs, e.kind = .nc a bs) ∨ ∃ a : Acc, (∃ bs, e.kind = .rd a bs) ∧
      a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  rcases memRow_tma hp hX hFw hg he hat hm with h | ⟨a, bs, hk, h⟩
  · exact .inl h
  · exact .inr ⟨a, ⟨bs, hk⟩, MemRow.tmaRd_below h⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreSpec
public import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # The store warp's events by state

The event a store state fires is the event of its site (`Ev`, `shape`): the `setmaxnreg`, a poll
of stage `st`'s staged barrier with the parity of the item index, the tensor store of
the site's half of its stage of the item (`Store.tma_event`), a bulk-group commit, a wait for
the reads of all but `1 - r` groups, an arrival of one unit on stage `st`'s free barrier, and
the exit. One call of `site_shape`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The store warp's phase register holds the parity of the item index. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.Work.phaseW_eq :
    ∀ i, Work.phaseW i = BitVec.ofNat 64 (i % 2)
  | 0 => by decide
  | i + 1 => by
    rw [Work.phaseW, Work.phaseW_eq i]
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [h, show (i + 1) % 2 = 1 by omega]
      decide
    · rw [h, show (i + 1) % 2 = 0 by omega]
      decide

theorem phase_par (i : Nat) : (truncBits 32 (Work.phaseW i)).toNat % 2 = i % 2 := by
  rw [Work.phaseW_eq]
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

/-- The event-shape table of the store warp. -/
def Ev (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .setMaxReg => ∃ inc n inst, e.kind = .setMaxReg inc n inst
  | .wait st => ∃ ok, e.kind = .wait (stagedAt L g st) (d.i % 2) ok true .cta
  | .tma st hh => e.kind = .tensorStore P.oMap (oSpec P L g d.i st hh)
  | .commit _ => e.kind = .bulkCommit
  | .drain r => e.kind = .bulkWait .read (if r = 0 then 1 else 0)
  | .free st => e.kind = .arrive (freeAt L g st) 0 1 true .cta
  | .exit => e.kind = .exit

set_option hygiene false in
/-- The store warp's side conditions: the CTA size, the scope of its polls, and its mbarrier
addresses. -/
macro "store_addr" : tactic => `(tactic| first
  | rw [‹Pre _ _ _›.block]
  | (rw [hat.1]; dsimp only; decide)
  | (apply Store.mbar_at ‹Pre _ _ _›
     case hr =>
       exact (PTX.Flow.regs_of_factsFrom ‹_› (by lit_mem)).trans
         (by simp only [valueOf, table, Prologue.valueOf, Prologue.values, lookupLit,
           Option.getD_some, Option.getD_none]; rfl)
     all_goals decide))

theorem shapeAt_tma {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hp : Pre P L mem0)
    {st hh : Fin 2} {i : Nat} : (code asms L g).ShapeAt (Ev P L g) ⟨.tma st hh, i⟩ :=
  fun hat hi hc hf => Store.tma_event hp ((hi.resolve_left (by simp)) (by simp)) hat.2.2.2.2 hc hf

/-- **The event a store state fires is the event of its site.** -/
theorem shape {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hp : Pre P L mem0) :
    (code asms L g).Shape (Ev P L g) := by
  refine Code.Shape.of_at fun d => ?_
  obtain ⟨s, i⟩ := d
  site_shape s
    except [.tma 0 0 => shapeAt_tma hp, .tma 0 1 => shapeAt_tma hp, .tma 1 0 => shapeAt_tma hp,
      .tma 1 1 => shapeAt_tma hp]
    unfolding [Ev, stagedAt, freeAt, phase_par, Fin.isValue, Fin.val_zero, Fin.val_one,
      Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd]
    reg_vals [valueOf, table, lookupLit]
    addr_by (store_addr)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store

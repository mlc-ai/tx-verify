-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreShape
public import Lemmas.Flow.EventCont

@[expose] public section

/-! # The store warp's polls and arrivals

The store warp's part of `OutputFacts.staged_poll` and `OutputFacts.free_arrive` (the role
cases `Facts.Store.staged_poll`, `Facts.Store.free_arrive`, for a thread of warp 13), from its
run invariant (`Store.Counts`):

* an event of a thread of warp 13 that the prologue does not fire is fired at a store state with
  the role's counts and has the state's shape (`Facts.store_ev`, `Store.Ev`);
* a poll fires at a wait site, on its stage's staged barrier of the thread's CTA, with the parity
  of the item index, which is that of the thread's earlier successful polls of the barrier
  (`Counts.staged`); it acquires;
* an arrival fires at a free site, on its stage's free barrier of the thread's CTA, one release
  arrival without transaction bytes, after one more successful poll of the stage's staged
  barrier than its earlier free arrivals of the stage (`Counts.staged`, `Counts.freed`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A store-warp event**: an event of a thread of warp 13 that the prologue does not fire comes
from a store state with the role's counts and invariant, and has the state's shape. -/
theorem Facts.store_ev (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (hw : warpOf L g = 13) (he : X.get (g, k) = some e) (hpk : ¬ Prologue.ProKind e.kind)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ d, Frame.stateAt (code L) X g k = some (some (.inr (.store d))) ∧
      Store.Counts L g d ((X.tr g).take k) ∧ (d.site = .setMaxReg ∨ Store.Inv L g d) ∧
      Store.Ev P L g d e ∧ e.pc = d.site.pc := by
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he hub
  rcases d with p | r
  · refine absurd (pro_event hpre hX he hσ fun f h => hub e.pc f ?_).proKind hpk
    obtain ⟨pc, k⟩ := e
    simp only at h
    subst h
    rfl
  · have hw' := role_warp_run hpre hg
      (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k r hσ
    cases r with
    | store d => exact ⟨d, hσ, hJ, hi, Store.shape hpre hat hi hc hf, fires_pc hf⟩
    | _ => simp [Role.kind, RoleKind.Warp, hw] at hw'

/-- A store-warp event of a kind the prologue does not fire. -/
theorem Facts.store_ev' (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {kd : Kind} (hg : g < L.threads)
    (hw : warpOf L g = 13) (he : X.get (g, k) = some ⟨pc, kd⟩) (hpk : ¬ Prologue.ProKind kd)
    (hub : ∀ f, kd ≠ .ub f) :
    ∃ d, Frame.stateAt (code L) X g k = some (some (.inr (.store d))) ∧
      Store.Counts L g d ((X.tr g).take k) ∧ (d.site = .setMaxReg ∨ Store.Inv L g d) ∧
      Store.Ev P L g d ⟨pc, kd⟩ ∧ pc = d.site.pc :=
  Facts.store_ev hpre hX ht hg hw he hpk fun _ f h => hub f (Event.mk.inj h).2

/-- The stage barriers of the store warp's counts are the interface's. -/
theorem Store.stagedAt_eq (L : Launch) (g st : Nat) :
    Store.stagedAt L g st = stagedBar L (ctaOf L g) st := by
  simp only [Store.stagedAt, stagedBar, ctaOf, Nat.add_assoc]

theorem Store.freeAt_eq (L : Launch) (g st : Nat) :
    Store.freeAt L g st = freeBar L (ctaOf L g) st := by
  simp only [Store.freeAt, freeBar, ctaOf, Nat.add_assoc]

/-- The positions of the arrivals. -/
theorem kernel_arrive_pcs : OpPcsFast kernel.code arriveOp Flow.mbarArrive.toList = true := by
  decide +kernel

/-- A store state's poll is of its stage's staged barrier, with the parity of its item index. -/
theorem Store.ev_wait {P : Params} {L : Launch} {g : Nat} {d : Store.D} {pc : Nat} {m : Loc}
    {p : Nat} {ok acq : Bool} {sc : MbarScope} (hev : Store.Ev P L g d ⟨pc, .wait m p ok acq sc⟩) :
    ∃ st, d.site = .wait st ∧ m = Store.stagedAt L g st ∧ p = d.i % 2 ∧ acq = true ∧
      sc = .cta := by
  obtain ⟨site, i⟩ := d
  cases site <;> simp only [Store.Ev, reduceCtorEq, exists_false] at hev
  case wait st =>
    obtain ⟨_, hk⟩ := hev
    simp only [Kind.wait.injEq] at hk
    obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hk
    exact ⟨st, rfl, rfl, rfl, rfl, rfl⟩

/-- A store state's arrival is one release unit without bytes on its stage's free barrier. -/
theorem Store.ev_arrive {P : Params} {L : Launch} {g : Nat} {d : Store.D} {pc : Nat} {m : Loc}
    {tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hev : Store.Ev P L g d ⟨pc, .arrive m tx c rel sc⟩) :
    ∃ st, d.site = .free st ∧ m = Store.freeAt L g st ∧ tx = 0 ∧ c = 1 ∧ rel = true ∧
      sc = .cta := by
  obtain ⟨site, i⟩ := d
  cases site <;> simp only [Store.Ev, reduceCtorEq, exists_false] at hev
  case free st =>
    simp only [Kind.arrive.injEq] at hev
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hev
    exact ⟨st, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Store.stagedAt_inj {L : Launch} {g c st : Nat} {st0 : Fin 2}
    (h : stagedBar L c st = Store.stagedAt L g st0) : c = ctaOf L g ∧ st = st0.val := by
  rw [Store.stagedAt_eq] at h
  simp only [stagedBar, Loc.mk.injEq, true_and] at h
  exact ⟨h.1, by omega⟩

theorem Store.freeAt_inj {L : Launch} {g c st : Nat} {st0 : Fin 2}
    (h : freeBar L c st = Store.freeAt L g st0) : c = ctaOf L g ∧ st = st0.val := by
  rw [Store.freeAt_eq] at h
  simp only [freeBar, Loc.mk.injEq, true_and] at h
  exact ⟨h.1, by omega⟩

/-- **The store warp's polls of a staged barrier** (`OutputFacts.staged_poll`, for a thread of
warp 13): of its CTA's barrier, with the parity of its earlier successful polls of it; a poll
acquires. -/
theorem Facts.Store.staged_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g = 13 → st < 2 → X.get (g, i) = some ⟨pc, .wait (stagedBar L c st) p ok acq sc⟩ →
        warpOf L g = 13 ∧ c = ctaOf L g ∧
        p % 2 = okPolls (stagedBar L c st) ((X.tr g).take i) % 2 ∧ (ok = true → acq = true) := by
  intro g i pc p c st ok acq sc hg hw hst he
  obtain ⟨⟨site, n⟩, -, hJ, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
  obtain ⟨st0, rfl, hm, rfl, rfl, -⟩ := Store.ev_wait hev
  obtain ⟨rfl, rfl⟩ := Store.stagedAt_inj hm
  refine ⟨hw, rfl, ?_, fun _ => rfl⟩
  rw [hm, hJ.staged st0]
  simp [Store.done, Store.before]

/-- **The store warp's arrivals on a free barrier** (`OutputFacts.free_arrive`, for a thread of
warp 13): one release arrival without transaction bytes on its CTA's barrier, after one more
successful poll of the stage's staged barrier than its earlier free arrivals of the stage. -/
theorem Facts.Store.free_arrive (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
      warpOf L g = 13 → st < 2 →
      X.get (g, i) = some ⟨pc, .arrive (freeBar L c st) tx cnt rel sc⟩ →
        warpOf L g = 13 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
        arrivals (freeBar L c st) ((X.tr g).take i) + 1 ≤
          okPolls (stagedBar L c st) ((X.tr g).take i) := by
  intro g i pc tx cnt c st rel sc hg hw hst he
  obtain ⟨⟨site, n⟩, -, hJ, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
  obtain ⟨st0, rfl, hm, rfl, rfl, rfl, -⟩ := Store.ev_arrive hev
  obtain ⟨rfl, rfl⟩ := Store.freeAt_inj hm
  refine ⟨hw, rfl, rfl, rfl, rfl, ?_⟩
  rw [hm, ← Store.stagedAt_eq, hJ.staged st0, hJ.freed st0]
  rcases Store.fin2_cases st0 with rfl | rfl <;> simp [Store.done, Store.before, Store.Site.pos]

end
end PTX.Kernels.FlashAttn4Fwd.Proof

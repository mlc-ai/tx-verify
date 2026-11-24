-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Steps
public import Lemmas.Flow.Ledger

/-! # Ledger steps at sites that are not mbarrier operations (no shape needed)

Checked on the tml-fa4 output warp: the load at the `.q0` site (pc 2953, `ld.global.nc`) and the
tensor store at `.store 0 0` (pc 2963, `cp.async.bulk.tensor`) fire neither an arrival nor a
poll, so the warp's arrival and poll ledgers take no step there without the site's shape
(`NotMbarAt`, `Code.fired_notMbar_at`). The poll at `.ready 0` (pc 2958, `mbarrier.try_wait`) is
the negative control: it is a poll. -/

namespace PTX.Tests.MbarFree
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

/-- The `.nc` load at pc 2953 is no mbarrier operation. -/
theorem notMbar_2953 : NotMbarAt kernel 2953 := by
  intro ins hc
  rw [Kernels.TmlFa4Fwd.Flow.code_2953] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨rfl, rfl⟩

/-- The tensor store at pc 2963 is no mbarrier operation. -/
theorem notMbar_2963 : NotMbarAt kernel 2963 := by
  intro ins hc
  rw [Kernels.TmlFa4Fwd.Flow.code_2963] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨rfl, rfl⟩

/-- The poll at pc 2958 is a poll (the negative control of `NotMbarAt`). -/
theorem isPoll_2958 : ¬ NotMbarAt kernel 2958 := by
  intro h
  have hw := (h _ (Kernels.TmlFa4Fwd.Flow.code_2958)).2
  cases hw

/-- The load at a `.q0` site of the output warp: its events are neither arrivals nor polls. -/
example (hp : Pre p L m) (hg : g < L.threads) (d : D) (hd : d.site = .q0) {e : Event}
    {o : Option TState} (mm : Loc) (hf : (code p L g ent).toMachine.Fired (some d) e o) :
    arrivesOn mm e = false ∧ okPoll mm e = false := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hd
  subst hd
  refine (code p L g ent).fired_notMbar_at (fun d => stepAt hp hg d) hf rfl notMbar_2953 mm

/-- The tensor store at a `.store 0 0` site: its events are neither arrivals nor polls. -/
example (hp : Pre p L m) (hg : g < L.threads) (d : D) (hd : d.site = .store 0 0) {e : Event}
    {o : Option TState} (mm : Loc) (hf : (code p L g ent).toMachine.Fired (some d) e o) :
    arrivesOn mm e = false ∧ okPoll mm e = false := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hd
  subst hd
  refine (code p L g ent).fired_notMbar_at (fun d => stepAt hp hg d) hf rfl notMbar_2963 mm

end PTX.Tests.MbarFree

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Prologue
import Kernels.TmlFa4Fwd.Proof.TerminalSite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Startup
open PTX PTX.Proof

private theorem alignedStartup {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e) (hAligned : kernel.isAlignedCtaBar e = true) :
    e = ⟨173, .bar 0 none .sync⟩ := by
  obtain ⟨site, kind⟩ := e
  cases kind <;> try cases hAligned
  rename_i id count mode
  cases count with
  | some _ => cases hAligned
  | none =>
    obtain ⟨_, _, hMode, _, hSite, hId, _⟩ := actualNamedBarrier hp hX he
    have hs := hSite.mp rfl
    subst site
    obtain rfl := hId rfl
    change mode = .sync at hMode
    subst mode
    rfl

/-- The whole-CTA startup synchronization is the first event of its alignment class. -/
theorem alignedRendezvousOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e) (hAligned : kernel.isAlignedCtaBar e = true) :
    ((X.tr i.1).take i.2).countP kernel.isAlignedCtaBar = 0 := by
  obtain rfl := alignedStartup hp hX he hAligned
  apply List.countP_eq_zero.mpr
  intro e hMem
  cases hClass : kernel.isAlignedCtaBar e
  · decide
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hMem
    have hLess := (List.getElem?_eq_some_iff.mp hj).1.trans_le (List.length_take_le _ _)
    rw [List.getElem?_take_of_lt hLess] at hj
    obtain rfl := alignedStartup hp hX (i := (i.1, j)) hj hClass
    have hSame := TmlFa4Fwd.Prologue.commonStartupUnique hX (g := i.1) (i := j) (j := i.2)
      (event_thread_lt hX he) hj he
    omega

/-- Every exited lane has executed the whole-CTA startup synchronization. -/
theorem alignedRendezvousOfExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} (hExit : ∃ e, X.get i = some e ∧ e.kind = .exit) :
    0 < (X.tr i.1).countP kernel.isAlignedCtaBar := by
  obtain ⟨⟨site, kind⟩, he, rfl⟩ := hExit
  have hg := event_thread_lt hX he
  have hPast : 173 < site := by rw [actualExitPc hX he]; decide
  have hStart : ∃ j, X.get (i.1, j) = some ⟨173, .bar 0 none .sync⟩ := by
    obtain ⟨g,index⟩ := i
    by_cases hw : TmlFa4Fwd.Prologue.warpIndex l g = 0
    · obtain ⟨j, _, _, hBar, _, _⟩ :=
        TmlFa4Fwd.Prologue.warp0InitializerPrefix hp hX hg hw he (Nat.le_of_lt hPast)
      exact ⟨j+1,hBar⟩
    · obtain ⟨_, hBar, _⟩ :=
        TmlFa4Fwd.Prologue.nonzeroStartupBar hp hX hg (Nat.pos_of_ne_zero hw) he hPast
      exact ⟨4, hBar⟩
  obtain ⟨j,hj⟩ := hStart
  have hMem := List.mem_of_getElem? hj
  have hClass : kernel.isAlignedCtaBar ⟨173, .bar 0 none .sync⟩ = true := by decide
  by_contra! hZero
  exact (List.countP_eq_zero.mp (Nat.eq_zero_of_le_zero hZero) _ hMem) hClass

end PTX.Kernels.TmlFa4Fwd.Thread.Startup

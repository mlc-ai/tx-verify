-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Lemmas.Flow.TraceInduction
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The parity of the input ring's polls along a thread

A loader polls the empty barrier of slot `s` with the parity after its own successful polls
on it: `(polled + 1) % 2`, which along the thread's events is one more than its successful
poll count. An MMA thread polls the full barrier of slot `s` with the parity of its own
successful polls on it. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Loader

set_option maxHeartbeats 4000000 in
/-- A loader poll on the empty barrier of slot `s` uses the parity after `polled`. -/
theorem poll_parity {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    {l : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : At t l.site.pc (facts L g l)) (hc : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o)
    {s : Fin 4} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : e.kind = .wait (emptyOf L g s) p ok acq sc) : p % 2 = (polled l s + 1) % 2 := by
  obtain ⟨epc, ek⟩ := e
  simp only at he
  subst he
  cases o with
  | none => exact (fires_none_notWait hfire _ _ _ _ _ rfl).elim
  | some u =>
    obtain ⟨site, m, n, q, cp, r, x⟩ := l
    cases hp : site.polls with
    | false =>
      exact (fires_notWait (eventTmpl_notWait (code_notPoll site hp hc)) hfire _ _ _ _ _ rfl).elim
    | true =>
      cases site with
      | wait b =>
        obtain ⟨ok', acq', sc', he⟩ := wait_event hpre b rfl hat hc hfire
        simp only [Event.mk.injEq, Kind.wait.injEq] at he
        obtain ⟨-, hloc, rfl, -⟩ := he
        obtain rfl := emptyLoc_eq.mp hloc
        fin_cases b <;> simp [polled, InputRing.producerParity, InputRing.slotOf]
      | clcWait =>
        obtain ⟨p', ok', acq', sc', -, he⟩ := clcWait_event hpre rfl hat hc hfire
        simp only [Event.mk.injEq, Kind.wait.injEq] at he
        have := congrArg Loc.addr he.2.1
        simp only [emptyOf, InputRing.emptyLoc] at this
        omega
      | drain i =>
        obtain ⟨ok', acq', sc', he⟩ := drain_event hpre i rfl hat hc hfire
        simp only [Event.mk.injEq, Kind.wait.injEq] at he
        obtain ⟨-, hloc, rfl, -⟩ := he
        obtain rfl := emptyLoc_eq.mp hloc
        simp [polled]
      | _ => simp [Site.polls] at hp

end Loader

namespace Mma

set_option maxHeartbeats 4000000 in
/-- An MMA poll on the full barrier of slot `s` uses the parity of `polledFull`. -/
theorem poll_parity {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {m : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hi : Inv m) (hat : At t m.site.pc (facts L g m)) (hc : kernel.code[m.site.pc]? = some ins)
    (hfire : Fires m.site.pc (eventTmpl Prod L g t ins.op) e o)
    {s : Fin 4} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : e.kind = .wait (fullOf L g s) p ok acq sc) : p % 2 = polledFull m s % 2 := by
  have hF := site_event hpre hg hi hat hc hfire
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site with
  | full s0 =>
    simp only [FiresAt] at hF
    obtain ⟨_, _, _, hk⟩ := hF
    rw [hk, Kind.wait.injEq] at he
    obtain ⟨hl, hp, -⟩ := he
    obtain rfl := fullOf_eq.mp hl
    simp [polledFull, past, hp]
  | accWait =>
    simp only [FiresAt] at hF
    obtain ⟨_, _, _, hk⟩ := hF
    rw [hk, Kind.wait.injEq] at he
    have := congrArg Loc.addr he.1
    simp only [accBar, Bar.loc, Bar.off] at this
    have := s.isLt
    omega
  | clcWait =>
    simp only [FiresAt] at hF
    obtain ⟨_, _, _, _, hk⟩ := hF
    rw [hk, Kind.wait.injEq] at he
    have := congrArg Loc.addr he.1
    simp only at this
    have := s.isLt
    omega
  | commit s0 =>
    simp only [FiresAt] at hF
    rw [hF] at he
    cases he
  | accCommit =>
    simp only [FiresAt] at hF
    rw [hF] at he
    cases he
  | _ =>
    simp only [FiresAt] at hF
    exact (hF.1 _ _ _ _ _ he).elim

end Mma

namespace RingPolls

/-- A loader thread's poll on the empty barrier of slot `s`, made from a loader state, uses
the parity after its own successful polls on that barrier. -/
theorem producer_poll_parity {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.loader l))))
    {s : Fin 4} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait (Loader.emptyOf L g s) p ok acq sc) :
    p % 2 = (okPolls (Loader.emptyOf L g s) ((X.tr g).take k) + 1) % 2 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hnd : l.site.done = false := by
    cases hd : l.site.done
    · rfl
    · exfalso
      have hp : l.site.polls = false := by
        revert hd; cases l.site <;> simp [Loader.Site.done, Loader.Site.polls]
      exact fires_notWait (eventTmpl_notWait (Loader.code_notPoll _ hp hc)) hfire _ _ _ _ _ hk
  have hcnt : LoaderTasks.Counts L g l ((X.tr g).take k) := LoaderTasks.run hpre hg htr k _ hσ
  rw [Nat.add_mod, hcnt.parity hnd s, ← Nat.add_mod]
  exact Loader.poll_parity hpre hat hc hfire hk

/-- An MMA thread's poll on the full barrier of slot `s`, made from an MMA state, uses the parity of
its successful polls on that barrier (`Mma.Counts`). -/
theorem consumer_poll_parity {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.mma m))))
    {s : Fin 4} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait (Mma.fullOf L g s) p ok acq sc) :
    p % 2 = okPolls (Mma.fullOf L g s) ((X.tr g).take k) % 2 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, ⟨hi, -⟩, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hnd : m.site.done = false := by
    cases hd : m.site.done
    · rfl
    · exfalso
      have hp : m.site.polls = false := by
        revert hd; cases m.site <;> simp [Mma.Site.done, Mma.Site.polls]
      exact fires_notWait (eventTmpl_notWait (Mma.code_notPoll _ hp hc)) hfire _ _ _ _ _ hk
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  rw [hC.full hnd s]
  exact Mma.poll_parity hpre hg hi hat hc hfire hk

end RingPolls

end
end PTX.Kernels.Fp16Gemm8192.Proof

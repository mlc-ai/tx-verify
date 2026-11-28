-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Lib.WinLane
import Kernels.InklingRelDecode.Proof.Lib.LanePre
import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.Async
import Lemmas.Flow.DataElems
import Lemmas.Flow.ReachFrame

/-! # The epilogue's load and the shuffle before it

The wait for the accumulator load (pc 2608) follows the load (pc 2607) directly, which writes its
words into the registers 1763 to 1826 and keeps the others; the load follows the shuffle of pc
2603 and three local steps that write the registers 1827 to 1830, not 1761. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Lib

variable {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private def ldWin : List (Nat × Nat) := [(2608, 2608)]

private theorem ld_fwd : fwdOk ldWin [] = true := by decide +kernel
private theorem ld_enter : enterOk ldWin 0 = true := by decide +kernel
private theorem ld_zero : inS ldWin 0 = false := by decide +kernel
private theorem ld_events : ∀ q ∈ entryEvents ldWin, q = 2607 ∨ q = 2608 := by decide +kernel
private theorem ev_2608 : evAtB kernel 2608 = true := by decide +kernel

/-- **The wait for the accumulator load comes right after the load**: the state before it is the
state after the load, which wrote the words into the registers 1763 to 1826. -/
public theorem after_ld {X : Execution} {s : TState} (hl : Iface.LaneState L X g s)
    (hpc : s.pc = 2608) :
    ∃ k a vals sh s', X.get (g, k) = some ⟨2607, .tc (.ld a vals sh)⟩ ∧ Iface.LaneState L X g s' ∧
      s'.pc = 2607 ∧ vals.length = 64 ∧ (∀ j, j < 64 → s.regs (1763 + j) = vals[j]?) ∧
      s.regs 1761 = s'.regs 1761 := by
  have hin : inS ldWin s.pc = true := by simp [inS, ldWin, hpc]
  obtain ⟨k, e, t0, hk, hr1, -, hev, hin0, hrt, -⟩ := lane_set ld_fwd ld_enter ld_zero hl hin
  obtain ⟨s', hls, hes⟩ := lane_pre hk hr1
  have hspc := EventFrame.estep_source_pc hes
  have h0 : t0.pc = 2608 := by simp [inS, ldWin] at hin0; omega
  obtain ⟨ins, hc, hnl, hf⟩ := EventFrame.estep_event_source hes
  rcases ld_events e.pc (by simpa [entryEvents] using hev) with h | h
  · have hs' : s'.pc = 2607 := by omega
    rw [hs', Flow.code_2607] at hc
    obtain rfl := (Option.some.inj hc).symm
    obtain ⟨a, vals, hlen, rfl, ht0⟩ := fires_tcLd (fun s => by simp) hf
    have hss : t0 = s := by
      rcases Relation.ReflTransGen.cases_head hrt with h1 | ⟨c1, hc1, -⟩
      · exact h1
      · exact absurd hc1 (no_tau_evAt (by rw [h0]; exact ev_2608))
    subst hss
    rw [hs'] at hk
    have hlen' : vals.length = 64 := by simpa using hlen
    refine ⟨k, a, vals, _, s', hk, hls, hs', hlen', fun j hj => ?_, ?_⟩
    · obtain ⟨v, hv⟩ : ∃ v, vals[j]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [ht0, hv]
      refine setRegs_get _ vals _ j _ v (by decide) ?_ hv
      interval_cases j <;> rfl
    · rw [ht0, setRegs_other _ _ _ _ (by decide)]
      rfl
  · exfalso
    have hs' : s'.pc = 2608 := by omega
    rw [hs', Flow.code_2608] at hc
    obtain rfl := (Option.some.inj hc).symm
    have := Code.fires_tcWaitLd_next hf
    rw [this] at h0
    simp [PTX.next] at h0
    omega

private def shWin : List (Nat × Nat) := [(2604, 2607)]

private theorem sh_fwd : fwdOk shWin [1761] = true := by decide +kernel
private theorem sh_enter : enterOk shWin 0 = true := by decide +kernel
private theorem sh_zero : inS shWin 0 = false := by decide +kernel
private theorem sh_events : ∀ q ∈ entryEvents shWin, q = 2603 ∨ q = 2607 := by decide +kernel
private theorem sh_keep : (match kernel.code[2603]? with
    | some ins => [1761].all (fun r => !(EventFrame.eventWrites ins.op).contains r)
    | none => true) = true := by decide +kernel

/-- **The register 1761 is the one before the shuffle of pc 2603** at the load of pc 2607. -/
public theorem before_ld {X : Execution} {s : TState} (hl : Iface.LaneState L X g s)
    (hpc : s.pc = 2607) :
    ∃ s', Iface.LaneState L X g s' ∧ s'.pc = 2603 ∧ s.regs 1761 = s'.regs 1761 := by
  have hin : inS shWin s.pc = true := by simp [inS, shWin, hpc]
  obtain ⟨k, e, t0, hk, hr1, -, hev, hin0, hrt, hkeep⟩ :=
    lane_set sh_fwd sh_enter sh_zero hl hin
  obtain ⟨s', hls, hes⟩ := lane_pre hk hr1
  have hspc := EventFrame.estep_source_pc hes
  obtain ⟨ins, hc, hnl, hf⟩ := EventFrame.estep_event_source hes
  rcases sh_events e.pc (by simpa [entryEvents] using hev) with h | h
  · have hs' : s'.pc = 2603 := by omega
    refine ⟨s', hls, hs', ?_⟩
    rw [hkeep 1761 (by simp), estep_keeps hes ins hc 1761]
    have := sh_keep
    rw [← hs'] at this
    rw [hc] at this
    simpa using List.all_eq_true.mp this 1761 (by simp)
  · exfalso
    have hs' : s'.pc = 2607 := by omega
    rw [hs', Flow.code_2607] at hc
    obtain rfl := (Option.some.inj hc).symm
    obtain ⟨a, vals, hlen, rfl, ht0⟩ := fires_tcLd (fun s => by simp) hf
    rw [ht0, (setRegs_skel _ _ _).1] at hin0
    simp [inS, shWin, PTX.next, hs'] at hin0
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

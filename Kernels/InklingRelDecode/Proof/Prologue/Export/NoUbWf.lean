-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Wf
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Common.Export.PshRecv
import Kernels.InklingRelDecode.Proof.Prologue.Export.BlockAddress
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryHalf

@[expose] public section

/-! # The events of a lane are well-formed for the strict prologue

The payloads of the loads and shuffles of the prologue that `Strict.Wf` assumes: the request words,
the block-table words, the query halves and the broadcast word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control Strict

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem ld_site_eq (s : Site) (i : Fin 3) (h : s.pc = (Site.ld i).pc) : s = .ld i := by
  cases s with
  | ld j =>
    have : j = i := by revert h; revert i j; decide +revert
    exact congrArg Site.ld this
  | _ => exfalso; revert h; revert i; decide +revert

private theorem ld_range : ∀ i : Fin 3, 27 < (Site.ld i).pc ∧ (Site.ld i).pc < 574 := by
  decide +kernel

private theorem lb_pcs : ∀ (b : Fin 3) (h : Fin 2), (Site.lb b h).pc = 197 ∨ (Site.lb b h).pc = 220
    ∨ (Site.lb b h).pc = 241 ∨ (Site.lb b h).pc = 262 ∨ (Site.lb b h).pc = 283 ∨
    (Site.lb b h).pc = 304 := by decide +kernel

private theorem psh_pcs : ∀ b : Fin 3, (Site.psh b).pc ∈ [202, 244, 286] := by decide +kernel

/-- **The events of a lane are well-formed**: a non-faulting event at a load or broadcast site of
the prologue carries the word the strict steps read. -/
theorem wf_event {ev : Event} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g < L.threads) (he : X.get (g, k) = some ev)
    (clean : ∀ f, ev.kind ≠ .ub f) : Wf Q L g ev := by
  obtain ⟨pc, kd⟩ := ev
  refine ⟨fun i hpc a bs hk => ?_, fun b h hpc a bs hk => ?_, fun j hpc a bs hk => ?_,
    fun b hpc m' a b' c recv ok hk => ?_⟩
  · change pc = (Site.ld i).pc at hpc
    change kd = _ at hk
    subst hk
    have rng := ld_range i
    obtain ⟨w, d, t, ins, u, ht, -, pce, hc, fire, -, -⟩ := prologue_event hp hX hf he clean
      (by change 27 < pc; omega) (by change pc < 574; omega)
    have hs := ld_site_eq d.site i (pce.symm.trans hpc)
    change pc = d.site.pc at pce
    subst pce
    exact request_value hp hX hg i hs ht hc he fire
  · change pc = (Site.lb b h).pc at hpc
    change kd = _ at hk
    subst hk
    obtain ⟨s, -, hs, -⟩ := block_page hp hX hf he (by rw [hpc]; exact lb_pcs b h)
    exact ⟨_, hs⟩
  · change pc = (Site.ldq j).pc at hpc
    change kd = _ at hk
    subst hk
    exact ⟨_, query_half hp hX hf he hpc, rfl⟩
  · change pc = (Site.psh b).pc at hpc
    change kd = _ at hk
    subst hk
    have site : pc ∈ [202, 244, 286] := hpc ▸ psh_pcs b
    obtain ⟨recv', ok', hev⟩ := Export.psh_event hp hX he clean (by simpa using site)
    have hk := congrArg Event.kind hev
    simp only [Kind.shfl.injEq] at hk
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨_, Export.psh_recv hp hX hf he site⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

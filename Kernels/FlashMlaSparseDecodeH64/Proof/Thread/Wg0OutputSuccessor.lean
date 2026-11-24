-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Lemmas.Flow.Final
import Lemmas.Flow.RoleTemplates

@[expose] public section

/-! # The actual wait following an epilogue tile load -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem fires_outputWait {g : Nat} (hpre : Pre P L mem0) {d : D} {j : Fin 4}
    {t : TState} {e : Event} {ins : Instr} {u : Option TState} (hd : d.site = .oWait j)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e u) :
    e.kind = .tc .waitLd := by
  have hCode : kernel.code[(Site.oWait j).pc]? = some ⟨none, .tcWaitLd⟩ := by
    fin_cases j
    · exact Flow.code_1202
    · exact Flow.code_1362
    · exact Flow.code_1520
    · exact Flow.code_1677
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  have hTmpl : eventTmpl Assumptions.all L g t .tcWaitLd = .tc .waitLd (PTX.next t) :=
    tc_waitLd (g := g) (by rw [hpre.block])
  rw [hTmpl] at hf
  exact congrArg Event.kind hf.1

/-- In a complete execution, the instruction after the actual tile load is its load wait. -/
theorem output_wait_of_complete_load {g i : Nat} {d : D} {tile : Fin 4}
    {e : Event} {words : List Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hComplete : Complete L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oLoad tile) (hKind : e.kind = .tc (.ld (64 * tile.val) words .s32x32b)) :
    ∃ tag, X.get (g, i + 1) = some ⟨tag, .tc .waitLd⟩ ∧
      Frame.stateAt (Machine.code P L) X g (i + 1) =
        some (some (.wg0 { loadOutput L g d tile words with site := .oWait tile })) := by
  have hg := Frame.lt_of_get hX he
  have hwg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  obtain ⟨last, ex, hex, hExit, _⟩ :=
    Wg0OutputVisits.completeDone hX hComplete (fun k hk => (hs k hk).machine) ht hg hwg
  obtain ⟨_, hRun⟩ := hX.thr g hg
  have hLast : last + 1 = (X.tr g).length := Run.end_last hRun hex (.inr hExit)
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hDifferent : i ≠ last := by
    intro h
    subst last
    have heq := congrArg Event.kind (Option.some.inj (he.symm.trans hex))
    rw [hKind, hExit] at heq
    cases heq
  have hiNext : i + 1 < (X.tr g).length := by omega
  let d' : D := { loadOutput L g d tile words with site := .oWait tile }
  have hd' : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 d')) := by
    rw [Frame.stateAt_succ he, hd, Option.bind_some]
    change Machine.next P L g (.wg0 d) e = some (some (.wg0 d'))
    simp only [Machine.next, Wg0.next, nextSite, hsite, hKind, d']
  obtain ⟨w, hw⟩ : ∃ w, X.get (g, i + 1) = some w := ⟨_, List.getElem?_eq_getElem hiNext⟩
  obtain ⟨_, _, _, _, _, hCode, hFired⟩ := Frame.fired_site hs hX hw hd'
  have hWaitKind := fires_outputWait hpre (d := d') (j := tile) rfl hCode hFired
  obtain ⟨tag, kind⟩ := w
  change kind = _ at hWaitKind
  rw [hWaitKind] at hw
  exact ⟨tag, hw, hd'⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

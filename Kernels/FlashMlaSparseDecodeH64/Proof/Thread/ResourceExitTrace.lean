-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits

public section

/-! # Warp zero deallocates the CTA's Tensor Memory before returning -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}

private theorem event_before_done {k : Nat} {d : Wg0.D}
    (hi : i ≤ (X.tr g).length) (hk : k ≤ i)
    (hdone : Frame.stateAt (Machine.code P L) X g i = some (some .done))
    (hs : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ∃ e, k < i ∧ X.get (g, k) = some e ∧ Machine.next P L g (.wg0 d) e ≠ none := by
  have hki : k < i := by
    by_contra hlt
    obtain rfl : k = i := by omega
    rw [hdone] at hs
    cases hs
  have hkl : k < (X.tr g).length := by omega
  let e := (X.tr g)[k]
  have he : X.get (g, k) = some e := List.getElem?_eq_getElem hkl
  refine ⟨e, hki, he, ?_⟩
  intro hn
  have hstop : Frame.stateAt (Machine.code P L) X g (k + 1) = none := by
    rw [Frame.stateAt_succ he, hs]
    exact hn
  rw [Frame.stateAt_none_mono hstop (by omega)] at hdone
  cases hdone

set_option maxRecDepth 4096 in
/-- The terminal state of warp zero has an earlier 512-column deallocation. -/
theorem dealloc_before_done (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hg : g < L.threads) (hw : warpOf L g = 0) (hi : i ≤ (X.tr g).length)
    (hdone : Frame.stateAt (Machine.code P L) X g i = some (some .done)) :
    ∃ j < i, ∃ tag, X.get (g, j) = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ := by
  have hwg : wgOf L g = 0 := by
    unfold warpOf at hw
    unfold wgOf
    omega
  obtain ⟨c, hc, _, _, d, _, _, _, _, hbar, hsite⟩ :=
    Wg0OutputVisits.commitBeforeDone hX hg hs hwg hdone
  obtain ⟨bar, hb, hget, hn⟩ := event_before_done hi (by omega : c + 1 ≤ i) hdone hbar
  have hkind : ∃ id count op, bar.kind = .bar id count op := by
    cases k : bar.kind <;> simp [Machine.next, Wg0.next, Wg0.nextSite, hsite, k, hw] at hn
    exact ⟨_, _, _, rfl⟩
  obtain ⟨id, count, op, hkind⟩ := hkind
  let d' : Wg0.D := { d with site := .exit }
  have hd : Frame.stateAt (Machine.code P L) X g (c + 1 + 1) = some (some (.wg0 d')) := by
    rw [Frame.stateAt_succ hget, hbar]
    change Machine.next P L g (.wg0 d) bar = some (some (.wg0 d'))
    simp [Machine.next, Wg0.next, Wg0.nextSite, d', hsite, hkind, hw]
  obtain ⟨f, hf, hgetf, _⟩ := event_before_done hi (by omega : c + 1 + 1 ≤ i) hdone hd
  obtain ⟨o, t, ⟨hat, _⟩, hfire⟩ := (hs.produces (hX.thr g hg)).fired_at hgetf hd
  change (Wg0.code P L g).AtD d' t at hat
  change Fires t.pc (match kernel.code[Flow.tmemDealloc_0]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) f o at hfire
  rw [Flow.code_tmemDealloc_0] at hfire
  change Fires t.pc (eventTmpl Wg0.asms L g t (.tcDealloc .one (.reg 2427) (.reg 2428)))
    f o at hfire
  rw [Wg0.event_exit hpre hat rfl] at hfire
  exact ⟨c + 1 + 1, hf, t.pc, hgetf.trans (congrArg some hfire.1)⟩

/-- The final return of a tracked warp-zero lane has an earlier 512-column deallocation. -/
theorem dealloc_before_exit {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hw : warpOf L g = 0)
    (he : X.get (g, i) = some e) (hk : e.kind = .exit) :
    ∃ j < i, ∃ tag, X.get (g, j) = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ := by
  have hwg : wgOf L g = 0 := by
    unfold warpOf at hw
    unfold wgOf
    omega
  exact dealloc_before_done hpre hX hs (Frame.lt_of_get hX he) hw (PTX.len_of_get he).le
    (Wg0OutputVisits.doneAtExit hX hs ht hwg he hk)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents

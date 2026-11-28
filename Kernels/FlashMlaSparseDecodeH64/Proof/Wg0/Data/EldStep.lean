-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Stage

@[expose] public section

/-! # Data steps whose reach reads the control facts

The row guard (pc 1161) and the row-sum test's stretch (pc 1197) need control registers, which the
data facts do not state: these two kinds of steps hand the `Reach` the control facts of the state
(`Control.vF`, taken from the state's control facts), after the data facts.

* `ds_ld1x`: a one-register shared load whose successor depends on the control state;
* `ds_nxc`: an event that continues at the next instruction. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The control facts at `q` from those of the state, when their registers are live at its pc. -/
theorem hold_ctl {d : D} {s : Site} {t : TState} (hs : d.c.site = s)
    (hat : (code P L g w).AtD d t) (q : Nat)
    (hsub : ∀ r ∈ Control.ctlLive q, r ∈ Control.ctlLive s.pc) :
    Holds t.regs (Control.vF P L g w q d.c) := by
  obtain ⟨-, -, -, -, hAll⟩ := hat
  have h0 := ((holds_append _ _ _).mp hAll).1
  change Holds t.regs (factsFrom (Control.ctlLive d.c.site.pc) _) at h0
  rw [hs] at h0
  exact holds_factsFrom_mono h0 hsub

/-- `Holds` of three lists, reordered. -/
theorem holds_rot {R : Nat → Option Value} {A B C : List (Nat × Value)}
    (h : Holds R (A ++ (B ++ C))) : Holds R (C ++ (A ++ B)) := by
  obtain ⟨ha, hbc⟩ := (holds_append _ _ _).mp h
  obtain ⟨hb, hc⟩ := (holds_append _ _ _).mp hbc
  exact (holds_append _ _ _).mpr ⟨hc, (holds_append _ _ _).mpr ⟨ha, hb⟩⟩

/-- **A one-register shared load**, the successor's facts given by the control step. -/
theorem ds_ld1x {d : D} {s : Site} {a : MemAccess} {r : Nat} (hs : d.c.site = s)
    (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (hx : a.ext = .same) (hl : (Op.mem a).isLocal = false)
    (hr : a.regs = [r]) (he : Control.elems s = 1) (q : Nat)
    (hsub : ∀ r' ∈ Control.ctlLive q, r' ∈ Control.ctlLive s.pc)
    (hrc : r ∉ Control.ctlLive q) (hst : isStart s = true → wF (scX L) s d.b = [])
    (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ∉ [r])
    (hR : ∀ x bs c', Control.succ P L g w d.c ⟨s.pc, .rd x bs⟩ = some (some c') →
      succOk d.c c' = true → Reach kernel Assumptions.all L g (s.pc + 1)
        ((wF (scX L) s d.b ++ [r].zip [loadVal bs]) ++ Control.vF P L g w q d.c)
        (wF (scX L) c'.site (record d.c ⟨s.pc, .rd x bs⟩ d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.loadE (C' := code P L g w) (dF := dF L)
    (Q := fun v d' => ∃ x bs c', loadVal bs = v ∧ d' = dataNext L d c' ⟨s.pc, .rd x bs⟩ ∧
      Control.succ P L g w d.c ⟨s.pc, .rd x bs⟩ = some (some c'))
    (by rw [pc_eq hs]; exact hc) hk hnc hx hl ?_ ?_ ?_
  · intro hm; rw [hr] at hm; simp at hm
  · intro _ x bs d' v hn hv
    obtain ⟨c', hc', rfl⟩ := next_ctl hn
    rw [pc_eq hs] at hc'
    exact ⟨x, bs, c', loadVal_ok hv, by rw [pc_eq hs], hc'⟩
  · intro hi v d' t ⟨x, bs, c', hv, hd, hc'⟩ hat
    subst hd hv
    have h0 := el0 hs hi he
    obtain ⟨-, -, hat3, -, -⟩ := id hat
    have hacc : t.acc = [] := hat3.trans (by simp [Control.D.acc, h0])
    rw [hacc]
    refine fin_reach (hs ▸ hna) (fun _ => rfl) (fun h1 => ?_) (fun _ h2 => hR x bs c' hc' h2)
    rw [hr]
    obtain ⟨hp, -, -, hf, hF⟩ := at_site hs hat h0 (hs ▸ h1) hst
    have hC := hold_ctl hs hat q hsub
    obtain ⟨hp', hs', ha', hf', hF'⟩ :=
      at_load (acc := []) ⟨hp, rfl, rfl, hf, hF⟩ (List.nodup_singleton r) hoff
    refine ⟨hp', hs', ha', hf', (holds_append _ _ _).mpr ⟨hF', ?_⟩⟩
    refine holds_setRegs_off hC fun q' hq' => ?_
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hq'
    simp only [List.mem_singleton]
    rintro rfl
    exact hrc hr0

/-- **An event that continues at the next instruction**, its reach given the control facts. -/
theorem ds_nxc {d : D} {s s' : Site} {op : Op} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, op⟩)
    (hu : ∀ t e u, Fires s.pc (eventTmpl Assumptions.all L g t op) e (some u) →
      u = PTX.next t)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (q : Nat)
    (hsub : ∀ r' ∈ Control.ctlLive q, r' ∈ Control.ctlLive s.pc)
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1)
      (wF (scX L) s d.b ++ Control.vF P L g w q d.c)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.next (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by rw [pc_eq hs]; exact hu) ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next]; omega, hsb, ha, hf,
    (holds_append _ _ _).mpr ⟨hF, hold_ctl (t := t) hs hat q hsub⟩⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds
public import Lemmas.Flow.DataStepEKinds

@[expose] public section

/-! # The strict data steps of warpgroup 0, by kind

`dsS_<kind>`: the strict twin (`DataStepE`, no dead alternative) of `Kinds.ds_<kind>`, with
`ReachS` for `Reach`, for one event `e`. A load's step is for an event whose bytes rebuild
(`EvRdOk e`, `EvNcOk e`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **A site off the chain**: every successor has no data facts. -/
theorem dsS_off {d : D} {e : Event} (hna : d.c.site ≠ .arrS) (h : ∀ c', succOk d.c c' = false) :
    DataStepE (code P L g w) (dF L) d e := by
  intro t u d' ins _ _ _ _ hn _ _ _
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  rw [dF_next_off hna (by rw [h c']; simp)]
  trivial

/-- The successor's facts at a stopping state, from a `ReachS` of the next site's facts. -/
theorem fin_reachS {d : D} {c' : Control.D} {e : Event} {s' : Site} {p : Nat}
    {F : List (Nat × Value)} {u : TState} (hna : d.c.site ≠ .arrS)
    (hsucc : succOk d.c c' = true → wcls c'.site = wcls s')
    (hu : (isStart d.c.site || d.ok) = true → At u p F)
    (hR : (isStart d.c.site || d.ok) = true → succOk d.c c' = true →
      ReachS kernel Assumptions.all L g p F (wF (scX L) s' (record d.c e d.b))) :
    ∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs (dF L (dataNext L d c' e)) := by
  cases h12 : (isStart d.c.site || d.ok) && succOk d.c c' with
  | false =>
    intro _ _ _
    rw [dF_next_off hna h12]; trivial
  | true =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    exact fun t' hr hs => dF_next_on hna h1 hsucc _ (hR h1 h2 u (hu h1) t' hr hs)

/-- **A Tensor Memory load.** -/
theorem dsS_tc {d : D} {e : Event} {s s' : Site} {ds : List Nat} {ta : Nat} (hs : d.c.site = s)
    (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .tcLd ds ta .s32x32b none⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hnd : ds.Nodup)
    (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ∉ ds)
    (hR : ∀ a vals, vals.length = ds.length → ReachS kernel Assumptions.all L g (s.pc + 1)
      (wF (scX L) s d.b ++ ds.zip vals)
      (wF (scX L) s' (record d.c ⟨s.pc, .tc (.ld a vals .s32x32b)⟩ d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.tcLoad (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by intro _ h; cases h) (noLdWait _) ?_
  intro hi a vals d' t hn hl hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  rw [pc_eq hs]
  exact fin_reachS (hs ▸ hna) (hsucc c')
    (fun h1 => at_tcLoad (at_site hs hat (el0 hs hi he) (hs ▸ h1) hst) hnd hoff)
    (fun _ _ => hR a vals hl)

/-- **A one-source store.** -/
theorem dsS_st {d : D} {e : Event} {s s' : Site} {a : MemAccess} (hs : d.c.site = s)
    (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (h1s : a.srcs.length = 1) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hR : ∀ e, ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.store (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) hk h1s ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reachS (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only; omega, rfl, ha, hf, hF⟩

/-- **A store of several elements** (`n` sources, one per event): before the last element the
site and its facts stay; after it the successor's facts follow from a `Reach`. -/
theorem dsS_stE {d : D} {e : Event} {s s' : Site} {a : MemAccess} {n : Nat} (hs : d.c.site = s)
    (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hk : a.kind = .store) (hn : a.srcs.length = n)
    (hacc : Control.D.acc d.c = [])
    (hsame : ∀ c', d.c.el + 1 < n → succOk d.c c' = true → wcls c'.site = wcls s)
    (hrec : ∀ e, record d.c e d.b = d.b) (hst : isStart s = false)
    (hsucc : ∀ c', ¬ d.c.el + 1 < n → succOk d.c c' = true → wcls c'.site = wcls s')
    (hR : ¬ d.c.el + 1 < n → ∀ e c', succOk d.c c' = true →
      ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
        (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.storeE (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) hl hk
    ?_ ?_
  · intro hm e d' hn' R hR'
    obtain ⟨c', -, rfl⟩ := next_ctl hn'
    exact dF_mid_keep (hs ▸ hna) hs hst (hsame c' (by rw [hn] at hm; exact hm)) (hrec e) R
      ((holds_append _ _ _).mp hR').2
  · intro hi hm e d' t hn' hat
    obtain ⟨c', -, rfl⟩ := next_ctl hn'
    have hm' : ¬ d.c.el + 1 < n := by rw [hn] at hm; exact hm
    refine fin_reachS (hs ▸ hna) (hsucc c' hm') (fun h1 => ?_) (fun _ h2 => hR hm' e c' h2)
    obtain ⟨hp, hsb, ha, hf, hF⟩ := hat
    have hok : d.ok = true := by rw [hs, hst, Bool.false_or] at h1; exact h1
    have hd := ((holds_append _ _ _).mp hF).2
    unfold dF at hd; rw [hok, hs] at hd
    exact ⟨by show t.pc + 1 = _; rw [hp, pc_eq hs], rfl, ha.trans hacc, hf, hd⟩

/-- **An event that continues at the next instruction.** -/
theorem dsS_nx {d : D} {e : Event} {s s' : Site} {op : Op} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, op⟩)
    (hu : ∀ t e u, Fires s.pc (eventTmpl Assumptions.all L g t op) e (some u) →
      u = PTX.next t)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hR : ∀ e, ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.next (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by rw [pc_eq hs]; exact hu) ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reachS (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next]; omega, hsb, ha, hf, hF⟩

/-- **A Tensor Memory store**: the registers are unchanged and the thread continues at the next
instruction. -/
theorem dsS_tcSt {d : D} {e : Event} {s s' : Site} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hs : d.c.site = s) (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .tcSt ta ss sh⟩)
    (hw : Assumptions.all.any (·.tcStWaitLd s.pc) = false) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hR : ∀ e, ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.tcSt (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by rw [pc_eq hs]; exact hw) ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reachS (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next]; omega, hsb, ha, hf, hF⟩

/-- **A scalar `.nc` load** into a register the facts do not name. -/
theorem dsS_nc {d : D} {e : Event} {s s' : Site} {a : MemAccess} {r base wd : Nat} {sp : Space}
    (hwf : EvNcOk e) (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base wd) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ r)
    (hR : ∀ e, ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.loadNc (C' := code P L g w) (dF := dF L) hwf
    (by rw [pc_eq hs]; exact hc) hru hloc
    hb hk hsem hnc hr (fun hi => el0 hs hi he) (fun hi => by simp [Control.D.acc, el0 hs hi he])
    ?_
  intro hi x bs v d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reachS (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR _)
  obtain ⟨hp, -, -, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨show t.pc + 1 = _ by rw [hp], rfl, rfl, hf, holds_update hF hoff⟩

/-- **An `mbarrier` wait** into a predicate register the facts do not name. -/
theorem dsS_wait {d : D} {e : Event} {s s' : Site} {p base : Nat} {off : Int} {par : Opnd}
    {acq : Bool}
    {sc : MbarScope} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .mbarWait p base off par acq sc⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ p)
    (hR : ∀ e, ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.wait (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) ?_
  intro hi m q ok sc' d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reachS (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR _)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next, setReg]; omega, hsb, ha, hf, holds_update hF hoff⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

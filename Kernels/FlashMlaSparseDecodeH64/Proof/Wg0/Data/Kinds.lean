-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
public import Lemmas.Flow.DataTcLoad
public import Lemmas.Flow.DataElems
public import Lemmas.Flow.DataStoreVote
public import Lemmas.Flow.DataTcSt
public import Lemmas.Flow.IssueNext
public import Lemmas.Flow.ReachSegU
public import Lemmas.Flow.DataLoadNcV

@[expose] public section

/-! # The kinds of data steps of warpgroup 0

Each data step of `Data.code` is one of these generic lemmas, applied to the site's `Reach`
(`Gen/DataSites.lean`, generated) in `Gen/DataSteps.lean`:

* `ds_off`: a site off the block's chain (every successor has no data facts);
* `ds_tc`: a Tensor Memory load (the score loads);
* `ds_ld1`: a one-register shared load (the valid-mask word);
* `ds_ld2`: a two-element shared load (the peer elements): before the second element the
  successor is the same site with the same facts;
* `ds_st`: a one-source store (the packed peer stores);
* `ds_vote`: the rescale vote (`vote.any`), whose result is recorded (`Blk.vt`);
* `ds_stE`: a store of several elements (the P stores);
* `ds_tcSt`: a Tensor Memory store (the rescaled chunk's);
* `ds_nx`: an event that continues at the next instruction (`tcgen05.wait::ld`,
  `tcgen05.fence::before_thread_sync`, `bar.sync`).

A step to the site the chain expects (`succOk`) gives the next site's facts from the site's facts
and the values the event delivered (`dF_next_on`); any other step leaves the chain (`dF_next_off`).
At the first site of the chain (`isStart`) the facts before the event are empty. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- A followed step is a control step and the data after it. -/
theorem next_ctl {d d' : D} {e : Event} (h : (code P L g w).next d e = some (some d')) :
    ∃ c', Control.succ P L g w d.c e = some (some c') ∧ d' = dataNext L d c' e := by
  change (Control.succ P L g w d.c e).map _ = _ at h
  cases hc : Control.succ P L g w d.c e with
  | none => rw [hc] at h; cases h
  | some o =>
    rw [hc] at h
    cases o with
    | none => cases h
    | some c' => cases h; exact ⟨c', rfl, rfl⟩

theorem dataNext_eq {d : D} {c' : Control.D} {e : Event} (hna : d.c.site ≠ .arrS) :
    dataNext L d c' e =
      { c := c', b := record d.c e d.b, hist := d.hist,
        ok := (isStart d.c.site || d.ok) && succOk d.c c' } := by
  unfold dataNext
  split
  · exact absurd ‹_› hna
  · rfl

/-- A step off the chain: no data facts. -/
theorem dF_next_off {d : D} {c' : Control.D} {e : Event} (hna : d.c.site ≠ .arrS)
    (h : ((isStart d.c.site || d.ok) && succOk d.c c') = false) :
    dF L (dataNext L d c' e) = [] := by
  rw [dataNext_eq hna]; unfold dF; dsimp only; rw [h]; rfl

/-- A step on the chain: the next site's facts. -/
theorem dF_next_on {d : D} {c' : Control.D} {e : Event} {s' : Site} (hna : d.c.site ≠ .arrS)
    (h1 : (isStart d.c.site || d.ok) = true) (hsucc : succOk d.c c' = true → wcls c'.site = wcls s')
    (R : Nat → Option Value) (h : Holds R (wF (scX L) s' (record d.c e d.b))) :
    Holds R (dF L (dataNext L d c' e)) := by
  rw [dataNext_eq hna]; unfold dF; dsimp only
  cases hc : succOk d.c c' with
  | false => simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]; trivial
  | true => rw [h1]; show Holds R (wFc (scX L) (wcls c'.site) _); rw [hsucc hc]; exact h

/-- A step before the last element of a vector access keeps the site's facts. -/
theorem dF_mid_keep {d : D} {c' : Control.D} {e : Event} {s : Site} (hna : d.c.site ≠ .arrS)
    (hs : d.c.site = s) (hst : isStart s = false)
    (hsame : succOk d.c c' = true → wcls c'.site = wcls s) (hb : record d.c e d.b = d.b)
    (R : Nat → Option Value) (hR : Holds R (dF L d)) : Holds R (dF L (dataNext L d c' e)) := by
  cases hok : d.ok with
  | false => rw [dF_next_off hna (by rw [hs, hst, hok]; rfl)]; trivial
  | true =>
    refine dF_next_on (s' := s) hna (by rw [hok, Bool.or_true]) hsame R ?_
    rw [hb]; unfold dF at hR; rw [hok, hs] at hR; exact hR

/-- **A site off the chain**: every successor has no data facts. -/
theorem ds_off {d : D} (hna : d.c.site ≠ .arrS) (h : ∀ c', succOk d.c c' = false) :
    DataStep (code P L g w) (dF L) d := by
  intro t e u d' ins _ _ _ _ hn
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine .inl fun _ _ _ => ?_
  rw [dF_next_off hna (by rw [h c']; simp)]
  trivial

/-- The successor's facts at a stopping state, from a `Reach` of the next site's facts. -/
theorem fin_reach {d : D} {c' : Control.D} {e : Event} {s' : Site} {p : Nat}
    {F : List (Nat × Value)} {u : TState} (hna : d.c.site ≠ .arrS)
    (hsucc : succOk d.c c' = true → wcls c'.site = wcls s')
    (hu : (isStart d.c.site || d.ok) = true → At u p F)
    (hR : (isStart d.c.site || d.ok) = true → succOk d.c c' = true →
      Reach kernel Assumptions.all L g p F (wF (scX L) s' (record d.c e d.b))) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs (dF L (dataNext L d c' e))) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  cases h12 : (isStart d.c.site || d.ok) && succOk d.c c' with
  | false =>
    refine .inl fun _ _ _ => ?_
    rw [dF_next_off hna h12]; trivial
  | true =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    exact (hR h1 h2 u (hu h1)).imp_left fun h t' hr hs => dF_next_on hna h1 hsucc _ (h t' hr hs)

/-- The site's facts at a concrete state of it on the chain. -/
theorem at_site {d : D} {s : Site} {t : TState} (hs : d.c.site = s)
    (hat : (code P L g w).AtD d t) (hel : d.c.el = 0) (h1 : (isStart s || d.ok) = true)
    (hst : isStart s = true → wF (scX L) s d.b = []) : At t s.pc (wF (scX L) s d.b) := by
  obtain ⟨hp, hsb, ha, hf, hF⟩ := hat
  refine ⟨hp.trans (by show d.c.site.pc = _; rw [hs]), hsb.trans hel,
    ha.trans (by simp [Control.D.acc, hel]), hf, ?_⟩
  have hd := ((holds_append _ _ _).mp hF).2
  cases hok : d.ok with
  | true => unfold dF at hd; rw [hok, hs] at hd; exact hd
  | false => rw [hok, Bool.or_false] at h1; rw [hst h1]; trivial

theorem el0 {d : D} {s : Site} (hs : d.c.site = s) (hi : (code P L g w).inv d)
    (he : Control.elems s = 1) : d.c.el = 0 := by
  have : d.c.el < Control.elems d.c.site := hi
  rw [hs, he] at this; omega

theorem pc_eq {d : D} {s : Site} (hs : d.c.site = s) : (code P L g w).pc d = s.pc := by
  show d.c.site.pc = _; rw [hs]

theorem loadVal_ok {bs : List (Option Byte)} {v : Value} (h : rebuild 3 bs = .ok v) :
    loadVal bs = v := by
  simp [loadVal, h, Except.toOption]

/-- The state after the last element of a load into `ds`. -/
theorem at_load {t : TState} {p : Nat} {F : List (Nat × Value)} {ds : List Nat}
    {acc : List Value} {v : Value} (ht : At { t with sub := 0, acc := [] } p F)
    (hnd : ds.Nodup) (hoff : ∀ q ∈ F, q.1 ∉ ds) :
    At { setRegs t ds (acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } (p + 1)
      (F ++ ds.zip (acc ++ [v])) := by
  obtain ⟨hp, -, -, hf, hF⟩ := ht
  obtain ⟨-, -, -, hskF⟩ := setRegs_skel t ds (acc ++ [v])
  exact ⟨by simp only at hp ⊢; omega, rfl, rfl, hskF.trans hf, (holds_append _ _ _).mpr
    ⟨holds_setRegs_off hF hoff, holds_setRegs_zip t ds _ hnd⟩⟩

/-- The sites of the block's chain (the sources of its steps). -/
def onChain : Site → Bool
  | .smr | .sink | .lenA | .lenB | .bwait | .arrL | .bar0 | .wv | .wq | .tcfa => true
  | .sld _ _ | .sldw | .tcfb | .vm | .pst _ | .bar1 | .pld _ | .mst | .bar2 | .arrV | .mld => true
  | .vote | .ost _ | .rsf | .rld _ | .rldw _ | .rst _ | .rstw _ | .rsfb | .fpx | .arrS => true
  | .ebar0 | .est | .ebar1 | .eld | .lse | .wsv | .efa => true
  | .old _ | .oldw _ | .ost2 _ _ | .ofpx _ | .obar _ | .oel _ | .otma _ => true
  | _ => false

theorem succOk_off {c c' : Control.D} (h : onChain c.site = false) : succOk c c' = false := by
  unfold succOk; split <;> simp_all [onChain]

/-- A successor in a list of sites of one class has the class's facts. -/
theorem cls_mem {s s' : Site} {l : List Site} (h : decide (s ∈ l) = true)
    (hl : l.all (fun x => decide (wcls x = wcls s')) = true) : wcls s = wcls s' :=
  of_decide_eq_true (List.all_eq_true.mp hl s (of_decide_eq_true h))

/-- Facts on registers other than `r`, by their keys. -/
theorem hne_of {F : List (Nat × Value)} {r : Nat}
    (h : (F.map Prod.fst).all (fun k => k != r) = true) : ∀ q ∈ F, q.1 ≠ r := by
  intro q hq hd
  have := List.all_eq_true.mp h q.1 (List.mem_map_of_mem hq)
  simp_all

/-- Facts on registers outside `ds`, by their keys. -/
theorem hoff_of {F : List (Nat × Value)} {ds : List Nat}
    (h : (F.map Prod.fst).all (fun k => !ds.contains k) = true) : ∀ q ∈ F, q.1 ∉ ds := by
  intro q hq hd
  have := List.all_eq_true.mp h q.1 (List.mem_map_of_mem hq)
  simp_all

/-- **A Tensor Memory load.** -/
theorem ds_tc {d : D} {s s' : Site} {ds : List Nat} {ta : Nat} (hs : d.c.site = s)
    (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .tcLd ds ta .s32x32b none⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hnd : ds.Nodup)
    (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ∉ ds)
    (hR : ∀ a vals, vals.length = ds.length → Reach kernel Assumptions.all L g (s.pc + 1)
      (wF (scX L) s d.b ++ ds.zip vals)
      (wF (scX L) s' (record d.c ⟨s.pc, .tc (.ld a vals .s32x32b)⟩ d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.tcLoad (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by intro _ h; cases h) (noLdWait _) ?_
  intro hi a vals d' t hn hl hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  rw [pc_eq hs]
  exact fin_reach (hs ▸ hna) (hsucc c')
    (fun h1 => at_tcLoad (at_site hs hat (el0 hs hi he) (hs ▸ h1) hst) hnd hoff)
    (fun _ _ => hR a vals hl)

/-- **A one-register load.** -/
theorem ds_ld1 {d : D} {s s' : Site} {a : MemAccess} {r : Nat} (hs : d.c.site = s)
    (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (hx : a.ext = .same) (hl : (Op.mem a).isLocal = false)
    (hr : a.regs = [r]) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ∉ [r])
    (hR : ∀ x bs, Reach kernel Assumptions.all L g (s.pc + 1)
      (wF (scX L) s d.b ++ [r].zip [loadVal bs])
      (wF (scX L) s' (record d.c ⟨s.pc, .rd x bs⟩ d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.loadE (C' := code P L g w) (dF := dF L)
    (Q := fun v d' => ∃ x bs c', loadVal bs = v ∧
      d' = dataNext L d c' ⟨s.pc, .rd x bs⟩)
    (by rw [pc_eq hs]; exact hc) hk hnc hx hl ?_ ?_ ?_
  · intro hm; rw [hr] at hm; simp at hm
  · intro _ x bs d' v hn hv
    obtain ⟨c', -, rfl⟩ := next_ctl hn
    exact ⟨x, bs, c', loadVal_ok hv, by rw [pc_eq hs]⟩
  · intro hi v d' t ⟨x, bs, c', hv, hd⟩ hat
    subst hd hv
    have h0 := el0 hs hi he
    have hacc : t.acc = [] := hat.2.2.1.trans (by simp [Control.D.acc, h0])
    rw [hacc]
    refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR x bs)
    rw [hr]
    obtain ⟨hp, -, -, hf, hF⟩ := at_site hs hat h0 (hs ▸ h1) hst
    exact at_load (acc := []) ⟨hp, rfl, rfl, hf, hF⟩ (List.nodup_singleton r) hoff

/-- At the second element of a pair load the first element is read. -/
theorem pld_last {d : D} {k : Fin 8} {t : TState} {x : Acc} {bs : List (Option Byte)}
    (hs : d.c.site = .pld k) (hne0 : d.c.el ≠ 0) (hi : (code P L g w).inv d)
    (hat : (code P L g w).AtD d t) :
    d.c.el = 1 ∧ t.acc = [d.c.a0] ∧ record d.c ⟨(Site.pld k).pc, .rd x bs⟩ d.b =
      { d.b with pw := fun j => if j = k.val then (d.c.a0, loadVal bs) else d.b.pw j } := by
  have hel : d.c.el = 1 := by
    have h2 : d.c.el < Control.elems d.c.site := hi
    rw [hs] at h2
    change d.c.el < 2 at h2
    omega
  refine ⟨hel, hat.2.2.1.trans (by simp [Control.D.acc, hel, hs]), ?_⟩
  unfold record; rw [hs]; simp [hel]

/-- The facts after the second element of a pair load into `r0 r1`. -/
theorem pld_last_at {d : D} {k : Fin 8} {t : TState} {r0 r1 : Nat} {v : Value}
    (hs : d.c.site = .pld k) (hat : (code P L g w).AtD d t)
    (hok : d.ok = true) (hne : r0 ≠ r1) (hoff : ∀ q ∈ wF (scX L) (.pld k) d.b, q.1 ∉ [r0, r1]) :
    At { setRegs t [r0, r1] ([d.c.a0] ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }
      ((Site.pld k).pc + 1) (wF (scX L) (.pld k) d.b ++ [r0, r1].zip ([d.c.a0] ++ [v])) := by
  obtain ⟨hp, -, -, hf, hF⟩ := hat
  have hd := ((holds_append _ _ _).mp hF).2
  unfold dF at hd; rw [hok, hs] at hd
  exact at_load (acc := [d.c.a0]) ⟨by rw [hp, pc_eq hs], rfl, rfl, hf, hd⟩ (by simp [hne]) hoff

/-- A step before the second element of a pair load keeps the facts. -/
theorem pld_mid {d : D} {k : Fin 8} {e : Event} {c' : Control.D} (hs : d.c.site = .pld k)
    (hm : d.c.el + 1 < 2) (R : Nat → Option Value) (hR : Holds R ((code P L g w).facts d)) :
    Holds R (dF L (dataNext L d c' e)) := by
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hst : isStart d.c.site = false := by rw [hs]; rfl
  have hel : d.c.el = 0 := by omega
  have hb : record d.c e d.b = d.b := by
    unfold record; rw [hs]; split <;> simp_all
  exact dF_mid_keep hna hs (by rw [← hs]; exact hst) (fun h => congrArg wcls
    (by simpa [succOk, hs, hel] using h)) hb R ((holds_append _ _ _).mp hR).2

/-- **A two-element load** (`elems = 2`): the first element keeps the site and its facts. -/
theorem ds_ld2 {d : D} {k : Fin 8} {s' : Site} {a : MemAccess} {r0 r1 : Nat}
    (hs : d.c.site = .pld k) (hc : kernel.code[(Site.pld k).pc]? = some ⟨none, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (hx : a.ext = .same)
    (hl : (Op.mem a).isLocal = false) (hr : a.regs = [r0, r1]) (hne : r0 ≠ r1)
    (hsucc : ∀ c', d.c.el ≠ 0 → succOk d.c c' = true → wcls c'.site = wcls s')
    (hoff : ∀ q ∈ wF (scX L) (.pld k) d.b, q.1 ∉ [r0, r1])
    (hR : ∀ bs, d.ok = true → Reach kernel Assumptions.all L g ((Site.pld k).pc + 1)
      (wF (scX L) (.pld k) d.b ++ [r0, r1].zip ([d.c.a0] ++ [loadVal bs]))
      (wF (scX L) s'
        { d.b with pw := fun j => if j = k.val then (d.c.a0, loadVal bs) else d.b.pw j })) :
    DataStep (code P L g w) (dF L) d := by
  refine @DataStep.loadE kernel Assumptions.all L g (code P L g w) (dF L) d a
    (fun v d' => d.c.el ≠ 0 ∧
      ∃ x bs c', loadVal bs = v ∧ d' = dataNext L d c' ⟨(Site.pld k).pc, .rd x bs⟩)
    (by rw [pc_eq hs]; exact hc) hk hnc hx hl ?_ ?_ ?_
  all_goals have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  all_goals have hst : isStart d.c.site = false := by rw [hs]; rfl
  · intro hm e d' hn R hR'
    obtain ⟨c', -, rfl⟩ := next_ctl hn
    exact pld_mid hs (by rw [hr] at hm; exact hm) R hR'
  · intro hm x bs d' v hn hv
    obtain ⟨c', -, rfl⟩ := next_ctl hn
    have : ¬ d.c.el + 1 < 2 := by rw [hr] at hm; exact hm
    exact ⟨by omega, x, bs, c', loadVal_ok hv, by rw [pc_eq hs]⟩
  · intro hi v d' t ⟨hne0, x, bs, c', hv, hd⟩ hat
    subst hd hv
    obtain ⟨hel, hacc, hrec⟩ := pld_last (x := x) (bs := bs) hs hne0 hi hat
    rw [hacc]
    refine fin_reach hna (hsucc c' (by omega)) (fun h1 => ?_) (fun h1 _ => hrec ▸ hR bs ?_)
    · have hok : d.ok = true := by rw [hst, Bool.false_or] at h1; exact h1
      rw [hr]; exact pld_last_at hs hat hok hne hoff
    · rw [hst, Bool.false_or] at h1; exact h1

/-- **A one-source store.** -/
theorem ds_st {d : D} {s s' : Site} {a : MemAccess} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (h1s : a.srcs.length = 1) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.store (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) hk h1s ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only; omega, rfl, ha, hf, hF⟩

/-- **A `vote.any`**: the successor's facts follow from the site's facts and the result. -/
theorem ds_vote {d : D} {s s' : Site} {ty dv pr neg mask} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? =
      some ⟨none, .warp ⟨.vote .any neg, ty, [some dv], [.reg pr], some mask⟩⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ dv)
    (hR : ∀ m p r, Reach kernel Assumptions.all L g (s.pc + 1)
      ((dv, .pred r) :: wF (scX L) s d.b)
      (wF (scX L) s' (record d.c ⟨s.pc, .voteMode .any m p r⟩ d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.voteAny (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) ?_
  intro hi m p r d' t hn hat
  rw [pc_eq hs] at hn
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR m p r)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next, setReg]; omega, hsb, ha, hf,
    by simp [PTX.next, setReg], holds_update hF hoff⟩

/-- **A store of several elements** (`n` sources, one per event): before the last element the
site and its facts stay; after it the successor's facts follow from a `Reach`. -/
theorem ds_stE {d : D} {s s' : Site} {a : MemAccess} {n : Nat} (hs : d.c.site = s)
    (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩)
    (hl : (Op.mem a).isLocal = false) (hk : a.kind = .store) (hn : a.srcs.length = n)
    (hacc : Control.D.acc d.c = [])
    (hsame : ∀ c', d.c.el + 1 < n → succOk d.c c' = true → wcls c'.site = wcls s)
    (hrec : ∀ e, record d.c e d.b = d.b) (hst : isStart s = false)
    (hsucc : ∀ c', ¬ d.c.el + 1 < n → succOk d.c c' = true → wcls c'.site = wcls s')
    (hR : ¬ d.c.el + 1 < n → ∀ e c', succOk d.c c' = true →
      Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
        (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.storeE (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) hl hk
    ?_ ?_
  · intro hm e d' hn' R hR'
    obtain ⟨c', -, rfl⟩ := next_ctl hn'
    exact dF_mid_keep (hs ▸ hna) hs hst (hsame c' (by rw [hn] at hm; exact hm)) (hrec e) R
      ((holds_append _ _ _).mp hR').2
  · intro hi hm e d' t hn' hat
    obtain ⟨c', -, rfl⟩ := next_ctl hn'
    have hm' : ¬ d.c.el + 1 < n := by rw [hn] at hm; exact hm
    refine fin_reach (hs ▸ hna) (hsucc c' hm') (fun h1 => ?_) (fun _ h2 => hR hm' e c' h2)
    obtain ⟨hp, hsb, ha, hf, hF⟩ := hat
    have hok : d.ok = true := by rw [hs, hst, Bool.false_or] at h1; exact h1
    have hd := ((holds_append _ _ _).mp hF).2
    unfold dF at hd; rw [hok, hs] at hd
    exact ⟨by show t.pc + 1 = _; rw [hp, pc_eq hs], rfl, ha.trans hacc, hf, hd⟩

/-- **An event that continues at the next instruction.** -/
theorem ds_nx {d : D} {s s' : Site} {op : Op} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, op⟩)
    (hu : ∀ t e u, Fires s.pc (eventTmpl Assumptions.all L g t op) e (some u) →
      u = PTX.next t)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.next (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by rw [pc_eq hs]; exact hu) ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next]; omega, hsb, ha, hf, hF⟩

/-- **A Tensor Memory store**: the registers are unchanged and the thread continues at the next
instruction. -/
theorem ds_tcSt {d : D} {s s' : Site} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hs : d.c.site = s) (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .tcSt ta ss sh⟩)
    (hw : Assumptions.all.any (·.tcStWaitLd s.pc) = false) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.tcSt (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc)
    (by rw [pc_eq hs]; exact hw) ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR e)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next]; omega, hsb, ha, hf, hF⟩

/-- **A scalar `.nc` load** into a register the facts do not name. -/
theorem ds_nc {d : D} {s s' : Site} {a : MemAccess} {r base wd : Nat} {sp : Space}
    (hs : d.c.site = s) (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base wd) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ r)
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.loadNc (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) hru hloc
    hb hk hsem hnc hr (fun hi => el0 hs hi he) (fun hi => by simp [Control.D.acc, el0 hs hi he])
    ?_
  intro hi x bs v d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR _)
  obtain ⟨hp, -, -, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨show t.pc + 1 = _ by rw [hp], rfl, rfl, hf, holds_update hF hoff⟩

/-- **A scalar `.nc` load whose word the facts after it state** (the sink word). -/
theorem ds_ncv {d : D} {s s' : Site} {a : MemAccess} {r base wd : Nat} {sp : Space}
    (hs : d.c.site = s) (hna : s ≠ .arrS) (hc : kernel.code[s.pc]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base wd) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (he : Control.elems s = 1)
    (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ r)
    (hR : ∀ x bs, Reach kernel Assumptions.all L g (s.pc + 1)
      (wF (scX L) s d.b ++ [r].zip [loadVal bs])
      (wF (scX L) s' (record d.c ⟨s.pc, .nc x bs⟩ d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.loadNcV (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) hru
    hloc hb hk hsem hnc hr (fun hi => el0 hs hi he)
    (fun hi => by simp [Control.D.acc, el0 hs hi he]) ?_
  intro hi x bs v hv d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR x bs)
  obtain ⟨hp, -, -, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  rw [loadVal_ok hv]
  exact ⟨show t.pc + 1 = _ by rw [hp], rfl, rfl, hf,
    (holds_append _ _ _).mpr ⟨holds_update hF hoff, Function.update_self .., trivial⟩⟩

/-- **An `mbarrier` wait** into a predicate register the facts do not name. -/
theorem ds_wait {d : D} {s s' : Site} {p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .mbarWait p base off par acq sc⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = []) (hoff : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ p)
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.wait (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) ?_
  intro hi m q ok sc' d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR _)
  obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next, setReg]; omega, hsb, ha, hf, holds_update hF hoff⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

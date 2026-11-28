-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Entry
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Proof.Iface.EntryEnv
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.SafeA
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
public import Lemmas.Kernel.StrictQPRunEnd
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Safe
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Live
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Lib.RegionEpi
import Lemmas.Kernel.PostEvent
import Lemmas.Flow.Determinism
import Lemmas.Flow.ReachFrame
import Lemmas.Flow.SegQFQt
import Lemmas.Flow.MemTmpl
import Lemmas.Flow.UbStop
import Kernels.InklingRelDecode.Flow.Code.Part008

@[expose] public section

/-! # No undefined behaviour in the softmax of a data lane

The first undefined-behaviour event of a data lane at a pc from 574 to 2564, after the barrier at
573: the strict window starts at the first softmax state, whose invariant is the entry typing of
the prologue (`hE`), and runs to the event. The undefined behaviour at the first softmax event
itself is the one of the setmaxreg at 574, which has none. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The launch facts of the softmax's events. -/
theorem softLaunch (hp : Pre Q L m) : Strict.SoftLaunch L :=
  ⟨by rw [hp.block], hp.sharedAlignment, by
    have := hp.sharedRange
    unfold sharedBytes at this
    omega⟩

/-- **The run of a lane split at an event**: the state before it, after it, and the prefix runs. -/
theorem run_split {o : Option TState} (hr : Run kernel Assumptions.all L g {} (X.tr g) o) {j : Nat}
    {e : Event} (he : X.get (g, j) = some e) (hlen : j + 1 < (X.tr g).length) :
    ∃ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 ∧
      EStep kernel Assumptions.all L g t1 e (some u) ∧
      Run kernel Assumptions.all L g {} ((X.tr g).take (j + 1)) (some u) := by
  have hsplit : (X.tr g).take (j + 1) ++ (X.tr g).drop (j + 1) = X.tr g := List.take_append_drop _ _
  rw [← hsplit] at hr
  obtain ⟨o1, h1⟩ := Run.prefix hr
  have hj : (X.tr g)[j]? = some e := he
  have htk : (X.tr g).take (j + 1) = (X.tr g).take j ++ [e] := by
    rw [List.take_add_one, hj]; rfl
  rw [htk] at h1 hr
  obtain ⟨u0, s, hr0, hs, hes⟩ := Run.unsnoc _ e h1
  cases o1 with
  | none =>
    have := Run.ended h1 hr
    have h2 : (X.tr g).drop (j + 1) ≠ [] := by
      intro h; have := List.length_drop (i := j + 1) (l := X.tr g); simp [h] at this; omega
    exact absurd this h2
  | some u => exact ⟨u0, s, u, hr0, hs, hes, by rw [htk]; exact h1⟩

/-- The event after the barrier is fired at the state after it (no local step at 574). -/
theorem next_step {o : Option TState} (hr : Run kernel Assumptions.all L g {} (X.tr g) o) {j : Nat}
    {u : TState} (hru : Run kernel Assumptions.all L g {} ((X.tr g).take (j + 1)) (some u))
    {e1 : Event} (he1 : X.get (g, j + 1) = some e1) (h574 : u.pc = 574) :
    ∃ o1, EStep kernel Assumptions.all L g u e1 o1 := by
  have hsplit : (X.tr g).take (j + 2) ++ (X.tr g).drop (j + 2) = X.tr g := List.take_append_drop _ _
  rw [← hsplit] at hr
  obtain ⟨o2, h2⟩ := Run.prefix hr
  have hj : (X.tr g)[j + 1]? = some e1 := he1
  have htk : (X.tr g).take (j + 2) = (X.tr g).take (j + 1) ++ [e1] := by
    rw [show j + 2 = j + 1 + 1 by rfl, List.take_add_one, hj]; rfl
  rw [htk] at h2
  obtain ⟨u1, s, hr1, hs, hes⟩ := Run.unsnoc _ e1 h2
  obtain rfl := Option.some.inj (Run.det hr1 hru)
  rcases Relation.ReflTransGen.cases_head hs with h | ⟨v, hv, -⟩
  · subst h; exact ⟨o2, hes⟩
  · exact absurd hv (Flow.Code.no_tau_evAt (by rw [h574]; decide +kernel))

theorem code_574 : ∃ ins, kernel.code[574]? = some ins ∧ ins.guard = none ∧
    ins.op.isLocal = false :=
  ⟨_, Flow.code_574, rfl, by decide +kernel⟩

/-- **No setmaxreg at 574 is undefined behaviour**: the event after the barrier at 573. -/
theorem no_ub_574 (hp : Pre Q L m) {u : TState} (hpc : u.pc = 574) (hfl : u.fault = none)
    {e1 : Event} {o1 : Option TState} (hes : EStep kernel Assumptions.all L g u e1 o1) (f : Fault)
    (hk : e1.kind = .ub f) : False := by
  obtain ⟨ins, hc574, hgd, hl⟩ := code_574
  have hc : kernel.code[u.pc]? = some ins := by rw [hpc]; exact hc574
  obtain ⟨m', ho, hf⟩ := hes
  rw [out_event hfl hc (by simp [guardHolds, hgd]; rfl) hl] at ho
  cases ho
  have := fires_ub hf hk
  have hplain : Strict.plainShape u.pc = true := by
    rw [hpc]; exact Strict.plain_sites 574 (by decide)
  exact Strict.safe_plain_s (softLaunch hp) hc hplain f this

/-- The fact of the lane's own states: from the value facts. -/
theorem lane_p (hv : Iface.LateValues L X) (lane : g % L.block < 128) :
    ∀ t, Frame.LaneAt kernel Assumptions.all L X g t →
      TauAll kernel Assumptions.all L g (LateR' L g) t := by
  rintro t ⟨k, t0, hr, ht⟩ v hvt
  have h : Frame.LaneAt kernel Assumptions.all L X g v := ⟨k, t0, hr, ht.trans hvt⟩
  exact ⟨⟨hv.noDecline g v lane h, hv.pack g v lane h⟩, hv.half g v lane h, hv.rcp g v lane h,
    hv.exp2 g v lane h⟩

/-- **The window of the softmax ends in a state and a stop state with the invariant**: the events
after the barrier at 573 and before `i` are those of the window (below the epilogue, well formed),
and the event `i` is any event of the lane. -/
theorem soft_window (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hv : Iface.LateValues L X)
    (lane : g % L.block < 128)
    {j i : Nat} {e5 ei : Event} (hji : j + 1 < i) (he5 : X.get (g, j) = some e5)
    (hei : X.get (g, i) = some ei)
    (hpcw : ∀ i' ev, j < i' → i' < i → X.get (g, i') = some ev → ev.pc < 2565)
    (hE : ∀ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 →
      EStep kernel Assumptions.all L g t1 e5 (some u) →
      u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u)
    (hLW : ∀ i' ev, j < i' → i' < i → X.get (g, i') = some ev → Strict.LWf ev) :
    ∃ σ, Frame.stateAt (lateThread Q L) X g i = some (some σ) ∧ OkS σ ∧
      ∃ t0 t1 o', Run kernel Assumptions.all L g {} ((X.tr g).take i) (some t0) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 ∧
        (lateThread Q L g).Good (some σ) t1 ∧ QTF lateQt t1 ∧
        EStep kernel Assumptions.all L g t1 ei o' := by
  have hg := Frame.lt_of_get hX hei
  have nu := Frame.noUbBefore_of_get hX hei
  have hlenk : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hei).1
  obtain ⟨o, hr⟩ := hX.thr g hg
  obtain ⟨t0, t1, u, hrun, htau, hes, hru⟩ := run_split hr he5 (by omega)
  obtain ⟨hu574, hufl, hty⟩ := hE t0 t1 u hrun htau hes
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, j + 1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem (l := X.tr g) (i := j + 1) (by omega)⟩
  obtain ⟨o1, hes1⟩ := next_step hr hru he1 hu574
  have hnu1 : Frame.NoUbBefore X g (j + 1) := fun i hi => nu i (by omega)
  have clean1 : ∀ f, e1.kind ≠ .ub f := fun f => nu (j + 1) (by omega) e1 he1 f
  have h574 : e1.pc = 574 := by rw [EventFrame.estep_source_pc hes1]; exact hu574
  obtain ⟨w, ent, s, n, h0, hok⟩ := entry_state hp hX hf base he1 clean1 hnu1 h574
  have hC : ∀ g < L.threads, (lateThread Q L g).SoundU := fun g hg => lateThread_sound hp hg
  have hW : ∀ i', j + 1 ≤ i' → i' < i → ∀ ej, X.get (g, i') = some ej → WfS ej :=
    fun i' hi1 hi2 ej hej => ⟨hLW i' ej (by omega) hi2 hej, hpcw i' ej (by omega) hi2 hej⟩
  have hQ0 : ∀ t t1', Frame.LanePos kernel Assumptions.all L X g t ((X.tr g).drop (j + 1)) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1' →
      (lateThread Q L g).Good (some (softSt w ent s n)) t1' → QTF lateQt t1' := by
    rintro t t1' ⟨k', t0', hr', hes', hl0⟩ hl hgd
    have hk' : k' = j + 1 := by
      have := congrArg List.length hes'
      simp only [List.length_drop] at this
      omega
    subst hk'
    obtain rfl := Option.some.inj (Run.det hr' hru)
    have no_tau : ∀ {a b : TState}, a.pc = 574 → Relation.ReflTransGen
        (Tau kernel Assumptions.all L g) a b → a = b := by
      intro a b ha hab
      rcases Relation.ReflTransGen.cases_head hab with h | ⟨v, hv, -⟩
      · exact h
      · exact absurd hv (Flow.Code.no_tau_evAt (by rw [ha]; decide +kernel))
    obtain rfl := no_tau hu574 hl0
    obtain rfl := no_tau hu574 hl
    have hin : QIn (lateQt 574) Iface.entryEnv := Or.inr (by decide +kernel)
    have := typedF_of_qin hin hty
    simpa [QTF, hu574] using this
  have hmk : i = j + 1 + (i - j - 2 + 1) := by omega
  have key := Frame.strictQPRun_end (C := lateThread Q L)
    (J := fun g σ => guardedTable Q L g (lateErase Q L g σ)) (Q := QTF lateQt)
    (P := TauAll kernel Assumptions.all L g (LateR' L g)) (Wf := WfS) (Ok := OkS) hC hX
    (fun k => lateFollowed hf hg k) (lane_p hv lane)
    (fun d e hd => winS_step (Strict.ScaleOk.of_pre hp) d e hd)
    (fun d e d' hd _ _ hn => winS_next hd hn) (k0 := j + 1) (m := i - j - 2) h0
    ⟨w, ent, n, hok, Or.inl ⟨s, rfl⟩⟩ hQ0 (e := ei) (by rw [← hmk]; exact hei)
    (fun i' hi1 hi2 => hW i' hi1 (by omega)) ?live
  · rw [← hmk] at key
    exact key
  · intro i' d v hi1 hi2 hok' hv hd hJ nui hn
    exfalso
    have hu : ∀ f, v.kind ≠ .ub f := fun f => nui i' (by omega) v hv f
    obtain ⟨t, ins, o', hat, hinv, hc, hfi⟩ := Frame.fired_siteU hC hX hv hd hu
    obtain ⟨w', ent', n', hentok, ⟨s', rfl⟩ | ⟨z, rfl⟩⟩ := hok'
    · have hsite : s'.c.site ≠ .epilogue := by
        intro h
        have := hinv.2
        simp [epiExit, h] at this
      have hs' : Data.succ ent' L g s' v = none := by
        rcases h : Data.succ ent' L g s' v with _ | _ | c
        · rfl
        · simp [lateThread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, lateFrag,
            lateDataD, lateSoftD, Data.code, h] at hn
        · simp [lateThread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, lateFrag,
            lateDataD, lateSoftD, Data.code, h] at hn
      exact Strict.live_soft hsite hc hfi hu hs'
    · have h1 := EventFrame.fires_source_pc hfi
      have h2 : (lateThread Q L g).pc (epiSt w' ent' z n') = z.site.pc := rfl
      have := (Epilogue.Site.pc_range z.site).1
      have h3 := hpcw i' v (by omega) (by omega) hv
      omega

/-- **A data lane has no undefined behaviour at a softmax pc after the barrier at 573.** -/
theorem noUb_soft_core (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hv : Iface.LateValues L X)
    (lane : g % L.block < 128)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32))
    {j k pc : Nat} {e5 : Event} {f : Fault} (hjk : j < k) (he5 : X.get (g, j) = some e5)
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hpc : pc < 2565)
    (hE : ∀ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 →
      EStep kernel Assumptions.all L g t1 e5 (some u) →
      u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u)
    (hLW : ∀ i ev, j < i → i < k → X.get (g, i) = some ev → Strict.LWf ev) : False := by
  have hg := Frame.lt_of_get hX he
  have nu := Frame.noUbBefore_of_get hX he
  have hlenk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨o, hr⟩ := hX.thr g hg
  by_cases hk1 : k = j + 1
  · subst hk1
    obtain ⟨t0, t1, u, hrun, htau, hes, hru⟩ := run_split hr he5 (by omega)
    obtain ⟨hu574, hufl, -⟩ := hE t0 t1 u hrun htau hes
    obtain ⟨o1, hes1⟩ := next_step hr hru he hu574
    exact no_ub_574 hp hu574 hufl hes1 f rfl
  have hpcw : ∀ i' ev, j < i' → i' < k → X.get (g, i') = some ev → ev.pc < 2565 := by
    intro i' ev hi1 hi2 hev
    by_contra hge
    have := Run.pc_ge_later (Lib.loClosed_epi (L := L)) hr (j := i') (i := k) hi2
      (e := ev) (e' := ⟨pc, .ub f⟩) hev (by omega) he
    change 2565 ≤ pc at this
    omega
  obtain ⟨σ, hs, hok', t0, t1, o', -, -, hgd, hq, hes⟩ :=
    soft_window hp hX hf base hv lane (by omega) he5 he hpcw hE hLW
  have hC : ∀ g < L.threads, (lateThread Q L g).SoundU := fun g hg => lateThread_sound hp hg
  obtain ⟨ins, hc, hfire⟩ := Code.fired_of_good (hC g hg) hgd hes
  have hu := fires_ub hfire (rfl : (⟨pc, .ub f⟩ : Event).kind = .ub f)
  have hpcσ := EventFrame.fires_source_pc hfire
  obtain ⟨w', ent', n', hentok, ⟨s', rfl⟩ | ⟨z, rfl⟩⟩ := hok'
  · have hsite : s'.c.site ≠ .epilogue := by
      intro h
      have := hgd.2.2
      simp [epiExit, h] at this
    have hx : (s'.c.site = .ldS ∨ s'.c.site = .ldO ∨ s'.c.site = .stO ∨
        s'.c.site = .tmemSt) → Strict.Names L g s'.c.held.base := by
      intro hsite4
      have hheld : Softmax.held s'.c.site = true := by
        rcases hsite4 with h | h | h | h <;> rw [h] <;> decide
      have hst : Frame.stateAt (thread Q L) X g k =
          some (some (softState w' ent' s'.c n')) :=
        Frame.stateAt_map_some lateThread_stepMap hs
      have := shfl_held hp hX hlenk.le hst nu hheld
      exact ⟨_, hnames _ 1261 _ (Or.inl rfl) this, rfl⟩
    exact Strict.safe_soft (softLaunch hp) hentok.1 hentok.2.1 hgd.1 hq hsite hx hc f hu
  · exfalso
    have h1 : (lateThread Q L g).pc (epiSt w' ent' z n') = z.site.pc := rfl
    have := (Epilogue.Site.pc_range z.site).1
    change pc = _ at hpcσ
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft

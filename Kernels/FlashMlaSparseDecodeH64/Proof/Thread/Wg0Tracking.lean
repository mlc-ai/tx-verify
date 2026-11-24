-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0EntryTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Lemmas.Flow.Final

@[expose] public section

/-! # Tracking the softmax score-load prefix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The score-load states between a successful QK acquire and the validity-mask read. -/
def BeforeMaskRead : Site → Prop
  | .fenceLoad | .scoreLoad .. | .scoreWait | .fenceBefore => True
  | _ => False

/-- The score-load prefix follows every event. The role's arm invariant excludes the
score-load dismissal branch, independently of the words returned by the load. -/
theorem next_beforeMaskRead {d : D} {e : Event} (hi : Inv P L g d)
    (hb : BeforeMaskRead d.site) :
    Wg0.next P L g d e = none ∨
      ∃ d', Wg0.next P L g d e = some (some d') ∧
        d'.block = d.block ∧ (BeforeMaskRead d'.site ∨ d'.site = .maskRead) := by
  cases hd : d.site <;> simp only [BeforeMaskRead, hd] at hb
  case fenceLoad =>
    cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq, true_or]
    case tc k =>
      cases k <;> simp [BeforeMaskRead]
  case scoreLoad a k =>
    obtain ⟨j, hj⟩ := hi.armSite ⟨a, k, hd⟩
    have ha : a.val = arm L g :=
      congrArg Fin.val (Site.scoreLoad.inj (hd.symm.trans hj)).1
    cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq, true_or]
    case tc kind =>
      cases kind <;> try exact .inl rfl
      case ld _ words _ =>
        let loaded := loadScores d (a.val == k.val) words
        have hloaded : loaded.block = d.block := by
          unfold loaded loadScores
          split <;> rfl
        have hafter : BeforeMaskRead (afterScoreSite a k) := by
          unfold afterScoreSite
          split <;> trivial
        refine .inr ⟨{ loaded with site := afterScoreSite a k }, ?_, hloaded, .inl hafter⟩
        simp only [ha, ↓reduceIte, loaded]
  case scoreWait =>
    cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq, true_or]
    case tc k =>
      cases k <;> simp [BeforeMaskRead]
  case fenceBefore =>
    cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq, true_or]
    case tc k =>
      cases k <;> simp [BeforeMaskRead]

/-- The composed machine follows an actual event at a score-load state. -/
theorem composed_beforeMaskRead_next {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    {i : Nat} {d : D} {e : Event} (he : X.get (g, i) = some e)
    (ht : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hb : BeforeMaskRead d.site) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.block = d.block ∧ (BeforeMaskRead d'.site ∨ d'.site = .maskRead) := by
  obtain ⟨_, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he ht
  have hi : Inv P L g d := (Exists.choose_spec hf).1.2
  rcases next_beforeMaskRead (e := e) hi hb with hn | ⟨d', hn, hblk, hsite⟩
  · exact .inl (by simp [Machine.next, hn])
  · exact .inr ⟨d', by simp [Machine.next, hn], hblk, hsite⟩

private theorem role_fired_site {d : D} {e : Event} {u : TState}
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    ∃ t ins, (Wg0.code P L g).AtD d t ∧ Inv P L g d ∧
      kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) := by
  have hf' : (Wg0.code P L g).toMachine.Fired (some d) e (some u) := hf
  obtain ⟨t, ht, hFire⟩ := hf'
  change (Wg0.code P L g).AtD d t ∧ Inv P L g d at ht
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at hFire
  obtain ⟨ins, hc, -, -⟩ := site_event P L g d
  rw [ht.1.1, hc] at hFire
  exact ⟨t, ins, ht.1, ht.2, hc, hFire⟩

variable {mem0 : Mem0}

/-- The actual mask read obtains its word from the shared index ring. -/
theorem composed_mask_footprint (hpre : Pre P L mem0) {d : D} {e : Event} {o : Option TState}
    (hd : d.site = .maskRead) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hr : ∃ a bs, e.kind = .rd a bs) :
    ∃ a bs, e.kind = .rd a bs ∧ a.size = 4 ∧ half L g < 2 ∧
      a.loc = shLoc L g (maskBase + maskStride * (d.block % 4) + 4 * half L g) := by
  cases o with
  | none =>
    obtain ⟨t, _, hf⟩ := hf
    obtain ⟨a, bs, hr⟩ := hr
    rcases fires_none_ends hf with ⟨f, h⟩ | h <;> rw [hr] at h <;> cases h
  | some u =>
    obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
    obtain ⟨a, bs, he, hl, hz, _⟩ := fires_maskRead hpre hd hat hi hc hFire
    rw [hd] at hl
    exact ⟨a, bs, he, hz, halfLt hi.warpLt, (Option.some.inj hl).symm⟩

/-- The validity-mask check only needs a rebuilt 32-bit word and the loaded scores' packed
representation. The fired site itself supplies the matching address and four-byte footprint. -/
theorem composed_mask_next (hpre : Pre P L mem0) {d : D} {e : Event} {u : TState}
    (hd : d.site = .maskRead) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u))
    (hScores : exchangeReady d = true)
    (hMask : ∀ a bs, e.kind = .rd a bs → ∃ w, rebuild 3 bs = .ok (.bits 32 w)) :
    ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
      d'.site = .exchStore 0 ∧ d'.block = d.block := by
  obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
  obtain ⟨a, bytes, he, ha, hsize, -⟩ := fires_maskRead hpre hd hat hi hc hFire
  obtain ⟨w, hw⟩ := hMask a bytes he
  refine ⟨{ d with site := .exchStore 0, maskWord := w }, ?_, rfl, rfl⟩
  rw [hd] at ha
  have hn : Wg0.next P L g d e = some (some { d with site := .exchStore 0, maskWord := w }) := by
    simp [Wg0.next, nextSite, hd, he, ha, hsize, Site.elemBytes, hw, hScores]
  simp only [Machine.next, hn]

/-- A firing peer-exchange store advances to the next store or the pair barrier. -/
theorem composed_exchange_next (hpre : Pre P L mem0) {d : D} {e : Event} {u : TState} {j : Fin 8}
    (hd : d.site = .exchStore j) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧ d'.block = d.block ∧
      ((∃ k : Fin 8, k.val = j.val + 1 ∧ d'.site = .exchStore k) ∨ d'.site = .pairBar) := by
  obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
  obtain ⟨a, he, ha, hsize, -⟩ := fires_exchangeStore hpre j hd hat hi hc hFire
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  rw [hd, hsub] at ha
  by_cases hj : j.val + 1 < 8
  · let k : Fin 8 := ⟨j.val + 1, hj⟩
    let d' : D := { d with site := .exchStore k, sub := 0 }
    have hn : Wg0.next P L g d e = some (some d') := by
      simp [Wg0.next, nextSite, hd, he, writeStep, ha, hsize, hj, hsub, Site.elemBytes,
        Site.elems, d', k]
    exact ⟨d', by simp only [Machine.next, hn], rfl, .inl ⟨k, rfl, rfl⟩⟩
  · let d' : D := { d with site := .pairBar, sub := 0 }
    have hn : Wg0.next P L g d e = some (some d') := by
      simp [Wg0.next, nextSite, hd, he, writeStep, ha, hsize, hj, hsub, Site.elemBytes,
        Site.elems, d']
    exact ⟨d', by simp only [Machine.next, hn], rfl, .inr rfl⟩

/-- A firing that ends the concrete thread leaves no unfollowed live WG0 state. -/
theorem composed_ending_next {d : D} {e : Event}
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e none) :
    Machine.next P L g (.wg0 d) e = none := by
  obtain ⟨_, _, h⟩ := hf
  rcases fires_none_ends h with ⟨f, hk⟩ | hk <;>
    cases hd : d.site <;> simp [Machine.next, Wg0.next, nextSite, writeStep, waitStep, hd, hk]

/-- Sites whose successor does not validate a payload or a memory access. -/
def ControlSite : Site → Prop
  | .bulkWait | .lastStore | .wg0Sync | .maskReady | .qkDone | .fenceLoad | .scoreWait
  | .fenceBefore | .pairBar | .wg0Sync2 | .validFree | .rescaleLoad _ | .rescaleStore _
  | .rescaleWaitSt _ | .rescaleFenceB | .soFence | .soReady | .lseBar | .lseBar2 | .svDone
  | .fenceEpilogue | .oLoad _ | .stageFence _ | .epiBar _ | .elect _ | .tmaStore _ | .commit
  | .everyone | .exit => True
  | _ => False

set_option maxHeartbeats 1300000 in
/-- At a control site, any rejected event leaves the role dead. It cannot dismiss a live
thread. The composed machine follows the successful terminal transitions to `done`. -/
theorem control_ne_dismiss {d : D} {e : Event} (hc : ControlSite d.site) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hrole : Wg0.next P L g d e ≠ some none ∨
      d.site = .exit ∨ d.site = .everyone := by
    cases hd : d.site <;> simp only [ControlSite, hd, reduceCtorEq, or_false,
      or_true] at hc ⊢
    all_goals simp only [Wg0.next, nextSite, hd, waitStep]
    all_goals repeat' split
    all_goals intro h; cases h
  simp only [Machine.next]
  split
  · intro h
    cases h
  · rename_i hn
    rcases hrole with h | h
    · exact (h hn).elim
    · rw [ite_eq_left h]
      intro he
      cases he
  · intro h
    cases h

/-- The shared row-maximum write cannot dismiss the thread. -/
theorem composed_rowMax_next (hpre : Pre P L mem0) {d : D} {e : Event} {u : TState}
    (hd : d.site = .rowMax) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    Machine.next P L g (.wg0 d) e =
      some (some (.wg0 { d with site := .wg0Sync2, sub := 0 })) := by
  obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
  obtain ⟨a, he, ha, hz, -⟩ := fires_rowMax hpre hd hat hi hc hFire
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  simp [Machine.next, Wg0.next, nextSite, writeStep, hd, he, ha, hz, hsub, siteLoc,
    Site.elemBytes, Site.elems]

/-- A firing probability store advances using its event's exact vector-element footprint. -/
theorem composed_probabilityStore_ne_dismiss (hpre : Pre P L mem0) {d : D} {e : Event} {u : TState}
    {k : Fin 4} (hd : d.site = .pStore k)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
  obtain ⟨a, v, stored, -, -, he, ha, hz, -⟩ := fires_pStore hpre hd hat hi hc hFire
  rw [hd] at ha
  obtain ⟨d', hn⟩ : ∃ d', Wg0.next P L g d e = some (some d') := by
    by_cases hk : k.val + 1 < 4 <;> by_cases hs : d.sub + 1 < 4 <;>
      simp [Wg0.next, nextSite, writeStep, hd, he, ha, hz, Site.elemBytes, Site.elems, hk, hs]
  rw [Machine.next, hn]
  intro h
  cases h

/-- The global LSE write advances to the final PV wait. -/
theorem composed_lseStore_next (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {e : Event}
    {u : TState} (hd : d.site = .lseStore)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    Machine.next P L g (.wg0 d) e =
      some (some (.wg0 { d with site := .svDone, sub := 0 })) := by
  obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
  obtain ⟨a, he, ha, hz, -⟩ := fires_lseStore hpre (Wg1Mma.eOf_lt_b hpre)
    (Wg1Mma.queryOf_lt hpre hg) hd hat hi hc hFire
  simp [Machine.next, Wg0.next, nextSite, hd, he, ha, hz]

/-- The shared half-sum write advances to the second LSE barrier. -/
theorem composed_halfSumStore_next (hpre : Pre P L mem0) {d : D} {e : Event} {u : TState}
    (hd : d.site = .lseStore0) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    Machine.next P L g (.wg0 d) e =
      some (some (.wg0 { d with site := .lseBar2, sub := 0 })) := by
  obtain ⟨t, ins, hat, hi, hc, hFire⟩ := role_fired_site hf
  obtain ⟨a, he, ha, hz, -⟩ := fires_lseStore0 hpre hd hat hi hc hFire
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  simp [Machine.next, Wg0.next, nextSite, writeStep, hd, he, ha, hz, hsub, siteLoc,
    Site.elemBytes, Site.elems]

/-- A firing epilogue staging store advances using its decoded vector-element footprint. -/
theorem composed_stageStore_ne_dismiss (hpre : Pre P L mem0) (hg : g < L.threads) {d : D}
    {e : Event} {u : TState} {j : Fin 4} {k : Fin 8} (hd : d.site = .oStage j k)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hf' : (Wg0.code P L g).toMachine.Fired (some d) e (some u) := hf
  obtain ⟨a, he, ha, hz⟩ := fired_stageOutput hpre hg hd hf'
  obtain ⟨d', hn⟩ : ∃ d', Wg0.next P L g d e = some (some d') := by
    by_cases hk : k.val + 1 < 8 <;> by_cases hs : d.sub + 1 < 4 <;>
      simp [Wg0.next, nextSite, writeStep, hd, he, ha, hz, siteLoc,
        Site.elemBytes, Site.elems, hk, hs]
  rw [Machine.next, hn]
  intro heq
  cases heq

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

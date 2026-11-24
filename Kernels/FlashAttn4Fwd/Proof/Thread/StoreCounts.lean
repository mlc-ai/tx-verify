-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreBase
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Events
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # The store warp's counts along its run

The store warp keeps one invariant along its run, `Counts`: after the items before the
current one (`done`: the current index, or every item at the exit), and the sites of the
current item already passed (`before`), its successful polls of each stage's staged barrier,
its arrivals on each stage's free barrier, its TMA stores, its bulk commits and its bulk waits
are exactly counted: per item one poll and one arrival per stage, four stores, two commits and
two waits. At the arrival freeing stage `st` its last event is the bulk wait that leaves at most
`1 - st` groups reading shared memory. `counts_step` proves that every event fired at a store
state keeps `Counts`: the role's part of `Code.run_inv`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Stage `st`'s staged barrier (`+256 + 8 st`, polled) and free barrier (`+272 + 8 st`,
arrived on) in the thread's CTA. -/
def stagedAt (L : Launch) (g st : Nat) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + 256 + 8 * st⟩
def freeAt (L : Launch) (g st : Nat) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + 272 + 8 * st⟩

/-- Whether an event is a TMA store, a bulk commit, a bulk wait. -/
def isStore (e : Event) : Bool := match e.kind with | .tensorStore _ _ => true | _ => false
def isCommit (e : Event) : Bool := match e.kind with | .bulkCommit => true | _ => false
def isBulkWait (e : Event) : Bool := match e.kind with | .bulkWait _ _ => true | _ => false

/-- The position of a site in an item. -/
def Site.pos : Site → Nat
  | .setMaxReg => 0 | .wait 0 => 0 | .tma 0 0 => 1 | .tma 0 1 => 2 | .commit 0 => 3
  | .wait 1 => 4 | .tma 1 0 => 5 | .tma 1 1 => 6 | .commit 1 => 7 | .drain 0 => 8
  | .free 0 => 9 | .drain 1 => 10 | .free 1 => 11 | .exit => 0

/-- The items whose events are all done: the current index, or every item at the exit. -/
def done (L : Launch) (g : Nat) (d : D) : Nat := if d.site = .exit then Work.T L g else d.i

/-- Whether the event of site `s` of the current item is done at `d`. -/
def before (s : Site) (d : D) : Nat := if s.pos < d.site.pos then 1 else 0

/-- The store warp's counts at state `d` after the events `es`. -/
structure Counts (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  staged : ∀ st : Fin 2, okPolls (stagedAt L g st) es = done L g d + before (.wait st) d
  freed : ∀ st : Fin 2, arrivals (freeAt L g st) es = done L g d + before (.free st) d
  stores : es.countP isStore = 4 * done L g d + (before (.tma 0 0) d + before (.tma 0 1) d +
    before (.tma 1 0) d + before (.tma 1 1) d)
  commits : es.countP isCommit = 2 * done L g d + (before (.commit 0) d + before (.commit 1) d)
  waits : es.countP isBulkWait = 2 * done L g d + (before (.drain 0) d + before (.drain 1) d)
  lastWait : ∀ st : Fin 2, d.site = .free st →
    ∃ pc, es.getLast? = some ⟨pc, .bulkWait .read (if st = 0 then 1 else 0)⟩
  /-- The role starts at item 0. -/
  start : d.site = .setMaxReg → d.i = 0
  /-- The TMA stores at each store site: one per item. -/
  tmas : ∀ st hh : Fin 2, es.countP (fun e => e.pc == (Site.tma st hh).pc && isStore e) =
    done L g d + before (.tma st hh) d

/-- At the role's start, before any of its events. -/
theorem Counts.init {L : Launch} {g : Nat} {es : List Event}
    (h0 : ∀ e ∈ es, ∀ m, okPoll m e = false ∧ arrivesOn m e = false ∧
      isStore e = false ∧
      isCommit e = false ∧ isBulkWait e = false) :
    Counts L g ⟨.setMaxReg, 0⟩ es := by
  have hc : ∀ (p : Event → Bool), (∀ e ∈ es, p e = false) → es.countP p = 0 := fun p hp =>
    List.countP_eq_zero.mpr fun e he => by simp [hp e he]
  refine ⟨fun st => ?_, fun st => ?_, ?_, ?_, ?_, fun st h => (by cases h), fun _ => rfl,
    fun st hh => ?_⟩
  · simp [okPolls, hc _ fun e he => (h0 e he _).1, done, before, Site.pos]
  · simp [arrivals, hc _ fun e he => (h0 e he _).2.1, done, before, Site.pos]
  · simp [hc _ fun e he => (h0 e he (stagedAt L g 0)).2.2.1, done, before, Site.pos]
  · simp [hc _ fun e he => (h0 e he (stagedAt L g 0)).2.2.2.1, done, before, Site.pos]
  · simp [hc _ fun e he => (h0 e he (stagedAt L g 0)).2.2.2.2, done, before, Site.pos]
  · rw [hc _ fun e he => by simp [(h0 e he (stagedAt L g 0)).2.2.1]]
    rcases fin2_cases st with rfl | rfl <;> rcases fin2_cases hh with rfl | rfl <;>
      simp [done, before, Site.pos]

/-- An arrival with a state destination is on the object its address evaluates to. -/
theorem arrive_state_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {rel : Bool} {sc : MbarScope}
    {state : Option Nat} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    (hm : mbarLoc L g t base off = .ok m)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count false rel sc state)) e o) :
    ∀ m' tx' c' rel' sc', e.kind = .arrive m' tx' c' rel' sc' → m' = m := by
  intro m' tx' c' rel' sc' hk
  simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, bind, Except.bind, pure,
    Except.pure] at hf
  cases hb : readBits L g t 32 tx with
  | error f =>
    simp only [hb, ofExec, widenMbarScope, ite_self, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok bytes =>
    cases hn : readBits L g t 32 count with
    | error f =>
      simp only [hb, hn, ofExec, widenMbarScope, ite_self, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok n =>
      simp only [hb, hn, ofExec] at hf
      cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
      · rw [hf.1] at hk
        cases hk
        rfl

/-- An event of an instruction that is neither an mbarrier operation nor a bulk-group
operation moves no count. -/
theorem quiet_store {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hop : objectOp op = false) (hs : tensorStoreOp op = false) (hc : bulkCommitOp op = false)
    (hw : bulkWaitOp op = false) (m : Loc) :
    okPoll m e = false ∧ arrivesOn m e = false ∧ isStore e = false ∧ isCommit e = false ∧
      isBulkWait e = false := by
  obtain ⟨h1, h2, -⟩ := quiet hop hf m
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · unfold isStore; split
    · rename_i a sp hk; exact absurd (fires_tensorStore_op hf hk) (by simp [hs])
    · rfl
  · unfold isCommit; split
    · rename_i hk; exact absurd (fires_bulkCommit_op hf hk) (by simp [hc])
    · rfl
  · unfold isBulkWait; split
    · rename_i md r hk; exact absurd (fires_bulkWait_op hf hk) (by simp [hw])
    · rfl

/-- A register's value at a store state. -/
theorem reg_of {L : Launch} {g : Nat} {d : D} {t : TState} {r : Nat}
    (h : At t d.site.pc (facts L g d)) (hr : r ∈ Flow.live d.site.pc) :
    t.regs r = some (valueOf L g d r) :=
  holds_mem h.2.2.2.2 (mem_factsFrom hr)

theorem mbar_at {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState} {r k : Nat}
    (hpre : Pre P L mem0) (hk : k < 512) (h8 : k % 8 = 0)
    (hr : t.regs r = some (Prologue.sb L k)) :
    mbarLoc L g t r 0 = .ok ⟨.shared, g / L.block, L.sharedBase + k⟩ := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hb
  exact mbarLoc_b32 hr (by omega) (by omega)

/-- The event of a bulk wait is the wait. -/
theorem bulkWait_event {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {mode : BulkGroup.WaitMode} {n pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.bulkWait mode n)) e o) :
    e = ⟨pc, .bulkWait mode n⟩ := by
  simp only [eventTmpl, tensorStoreTmpl, Fires] at hf
  exact hf.1


/-- Close the fields of `Counts` after one event: each count of `pre ++ [e]` is its count of
`pre` (from `hs hfr hst hcm hw`) plus the event's indicator (from the given facts). -/
syntax "counts_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| counts_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      refine ⟨fun st => ?_, fun st => ?_, ?_, ?_, ?_, fun st hst' => ?_, fun h0' => ?_,
        fun st hh => ?_⟩
      · rw [okPolls_snoc, hs st]
        rcases fin2_cases st with rfl | rfl <;>
          simp [done, before, Site.pos, $extra,*] <;> omega
      · rw [arrivals_snoc, hfr st]
        rcases fin2_cases st with rfl | rfl <;>
          simp [done, before, Site.pos, $extra,*] <;> omega
      · rw [List.countP_append, List.countP_singleton, hst]
        simp [done, before, Site.pos, $extra,*] <;> omega
      · rw [List.countP_append, List.countP_singleton, hcm]
        simp [done, before, Site.pos, $extra,*] <;> omega
      · rw [List.countP_append, List.countP_singleton, hw]
        simp [done, before, Site.pos, $extra,*] <;> omega
      · first
          | (rcases fin2_cases st with rfl | rfl <;> simp_all [Site.pos])
          | (simp_all [Site.pos]; done)
      · first | (simp_all; done) | (cases h0')
      · rw [List.countP_append, List.countP_singleton, htm st hh, hpc]
        rcases fin2_cases st with rfl | rfl <;> rcases fin2_cases hh with rfl | rfl <;>
          simp [done, before, Site.pos, Site.pc, $extra,*] <;> omega))

/-- The indicators of a poll of `m` with outcome `ok`. -/
theorem ind_wait {e : Event} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m p ok acq sc) :
    (∀ m', okPoll m' e = (ok && decide (m = m'))) ∧ (∀ m', arrivesOn m' e = false) ∧
      isStore e = false ∧ isCommit e = false ∧ isBulkWait e = false := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  refine ⟨fun m' => okPoll_wait rfl, fun m' => arrivesOn_notArrive (by simp), rfl, rfl, rfl⟩

/-- The indicators of an arrival on `m`. -/
theorem ind_arrive {e : Event} {m : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive m tx c rel sc) :
    (∀ m', okPoll m' e = false) ∧ (∀ m', arrivesOn m' e = decide (m = m')) ∧
      isStore e = false ∧ isCommit e = false ∧ isBulkWait e = false := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact ⟨fun m' => okPoll_notWait (by simp), fun m' => arrivesOn_arrive rfl, rfl, rfl, rfl⟩

/-- The indicators of an event that is no poll and no arrival. -/
theorem ind_other {e : Event} (hw : ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc)
    (ha : ∀ l tx c rel sc, e.kind ≠ .arrive l tx c rel sc) :
    (∀ m', okPoll m' e = false) ∧ (∀ m', arrivesOn m' e = false) :=
  ⟨fun _ => okPoll_notWait hw, fun _ => arrivesOn_notArrive ha⟩

set_option maxHeartbeats 4000000 in
/-- Every event fired at a store state keeps `Counts`. -/
theorem counts_step {A : List Assumption} {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) {d d' : D} {pre : List Event} {e : Event} {t : TState} {ins : Instr}
    {o : Option TState} (hJ : Counts L g d pre) (hi : d.site = .setMaxReg ∨ Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl A L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    Counts L g d' (pre ++ [e]) := by
  have hpc : e.pc = d.site.pc := EventFrame.fires_source_pc hf
  obtain ⟨site, i⟩ := d
  obtain ⟨hs, hfr, hst, hcm, hw, hl, h0, htm⟩ := hJ
  cases site with
  | setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_3)
    have hq := quiet_store hf rfl rfl rfl rfl
    obtain rfl : i = 0 := h0 rfl
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hs0 := hs 0
    simp only [done, before, Site.pos] at hs0
    split_ifs with hT
    · refine ⟨fun st => ?_, fun st => ?_, ?_, ?_, ?_, fun st h => (by cases h),
        fun h => (by cases h), fun st hh => ?_⟩
      all_goals simp only [okPolls_snoc, arrivals_snoc, List.countP_append,
        List.countP_singleton, (hq _).1, (hq _).2.1, (hq (stagedAt L g 0)).2.2.1,
        (hq (stagedAt L g 0)).2.2.2.1, (hq (stagedAt L g 0)).2.2.2.2, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero]
      · rw [hs st]; rcases fin2_cases st with rfl | rfl <;> simp [done, before, Site.pos]
      · rw [hfr st]; rcases fin2_cases st with rfl | rfl <;> simp [done, before, Site.pos]
      · rw [hst]; simp [done, before, Site.pos]
      · rw [hcm]; simp [done, before, Site.pos]
      · rw [hw]; simp [done, before, Site.pos]
      · simp only [Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Nat.add_zero, htm st hh]
        rcases fin2_cases st with rfl | rfl <;> rcases fin2_cases hh with rfl | rfl <;>
          simp [done, before, Site.pos]
    · have hT0 : Work.T L g = 0 := by omega
      refine ⟨fun st => ?_, fun st => ?_, ?_, ?_, ?_, fun st h => (by cases h),
        fun h => (by cases h), fun st hh => ?_⟩
      all_goals simp only [okPolls_snoc, arrivals_snoc, List.countP_append,
        List.countP_singleton, (hq _).1, (hq _).2.1, (hq (stagedAt L g 0)).2.2.1,
        (hq (stagedAt L g 0)).2.2.2.1, (hq (stagedAt L g 0)).2.2.2.2, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero]
      · rw [hs st]; rcases fin2_cases st with rfl | rfl <;> simp [done, before, Site.pos, hT0]
      · rw [hfr st]; rcases fin2_cases st with rfl | rfl <;> simp [done, before, Site.pos, hT0]
      · rw [hst]; simp [done, before, Site.pos, hT0]
      · rw [hcm]; simp [done, before, Site.pos, hT0]
      · rw [hw]; simp [done, before, Site.pos, hT0]
      · simp only [Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Nat.add_zero, htm st hh]
        rcases fin2_cases st with rfl | rfl <;> rcases fin2_cases hh with rfl | rfl <;>
          simp [done, before, Site.pos, hT0]
  | wait st0 =>
    simp only [next] at hn
    split at hn
    · rename_i m p ok acq sc hk
      have hloc : m = stagedAt L g st0 := by
        rcases fin2_cases st0 with rfl | rfl
        · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_28)
          have hr := reg_of (r := 970) h (by table_decide)
          have hm := mbar_at (g := g) hpre (k := 256) (by omega) (by omega)
            (by simpa only [valueOf, table, Prologue.valueOf, Prologue.values,
              PTX.Flow.lookupLit, Option.getD_some, Option.getD_none] using hr)
          exact (fires_wait_loc hm hf _ _ _ _ _ hk).trans (by simp [stagedAt])
        · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_29)
          have hr := reg_of (r := 971) h (by table_decide)
          have hm := mbar_at (g := g) hpre (k := 264) (by omega) (by omega)
            (by simpa only [valueOf, table, Prologue.valueOf, Prologue.values,
              PTX.Flow.lookupLit, Option.getD_some, Option.getD_none] using hr)
          exact (fires_wait_loc hm hf _ _ _ _ _ hk).trans (by simp [stagedAt])
      subst hloc
      obtain ⟨hP, hA, hS, hC, hW⟩ := ind_wait hk
      simp only [Option.some.injEq] at hn
      subst hn
      cases ok <;> rcases fin2_cases st0 with rfl | rfl <;>
        counts_close [hP, hA, hS, hC, hW, stagedAt]
    · simp at hn
  | tma st0 hh =>
    simp only [next] at hn
    split at hn
    · rename_i a sp hk
      obtain ⟨hP, hA⟩ := ind_other (e := e) (by simp [hk]) (by simp [hk])
      have hS : isStore e = true := by simp [isStore, hk]
      have hC : isCommit e = false := by simp [isCommit, hk]
      have hW : isBulkWait e = false := by simp [isBulkWait, hk]
      simp only [Option.some.injEq] at hn
      subst hn
      rcases fin2_cases st0 with rfl | rfl <;> rcases fin2_cases hh with rfl | rfl <;>
        counts_close [hP, hA, hS, hC, hW]
    · simp at hn
  | commit st0 =>
    simp only [next] at hn
    split at hn
    · rename_i hk
      obtain ⟨hP, hA⟩ := ind_other (e := e) (by simp [hk]) (by simp [hk])
      have hS : isStore e = false := by simp [isStore, hk]
      have hC : isCommit e = true := by simp [isCommit, hk]
      have hW : isBulkWait e = false := by simp [isBulkWait, hk]
      simp only [Option.some.injEq] at hn
      subst hn
      rcases fin2_cases st0 with rfl | rfl <;> counts_close [hP, hA, hS, hC, hW]
    · simp at hn
  | drain r =>
    simp only [next] at hn
    split at hn
    · rename_i md k hk
      obtain ⟨hP, hA⟩ := ind_other (e := e) (by simp [hk]) (by simp [hk])
      have hS : isStore e = false := by simp [isStore, hk]
      have hC : isCommit e = false := by simp [isCommit, hk]
      have hW : isBulkWait e = true := by simp [isBulkWait, hk]
      simp only [Option.some.injEq] at hn
      subst hn
      rcases fin2_cases r with rfl | rfl
      · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkWait_0)
        obtain rfl := bulkWait_event hf
        counts_close [hP, hA, hS, hC, hW]
      · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkWait_1)
        obtain rfl := bulkWait_event hf
        counts_close [hP, hA, hS, hC, hW]
    · simp at hn
  | free st0 =>
    simp only [next] at hn
    split at hn
    · rename_i m tx c rel sc hk
      have hloc : m = freeAt L g st0 := by
        rcases fin2_cases st0 with rfl | rfl
        · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
          have hr := reg_of (r := 3251) h (by table_decide)
          have hm := mbar_at (g := g) hpre (k := 272) (by omega) (by omega)
            (by simpa only [valueOf, table, Prologue.valueOf, Prologue.values,
              PTX.Flow.lookupLit, Option.getD_some, Option.getD_none] using hr)
          exact (arrive_state_loc hm hf _ _ _ _ _ hk).trans (by simp [freeAt])
        · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
          have hr := reg_of (r := 401) h (by table_decide)
          have hm := mbar_at (g := g) hpre (k := 280) (by omega) (by omega)
            (by simpa only [valueOf, table, Prologue.valueOf, Prologue.values,
              PTX.Flow.lookupLit, Option.getD_some, Option.getD_none] using hr)
          exact (arrive_state_loc hm hf _ _ _ _ _ hk).trans (by simp [freeAt])
      subst hloc
      obtain ⟨hP, hA, hS, hC, hW⟩ := ind_arrive hk
      simp only [Option.some.injEq] at hn
      subst hn
      rcases fin2_cases st0 with rfl | rfl
      · counts_close [hP, hA, hS, hC, hW, freeAt]
      · have hiT : i < Work.T L g := (hi.resolve_left (by simp)) (by simp)
        simp only [show ¬ (1 : Fin 2) = 0 by decide, ↓reduceIte]
        unfold itemEnd
        dsimp only
        split_ifs with hT
        · counts_close [hP, hA, hS, hC, hW, freeAt]
        · have hT' : Work.T L g = i + 1 := by omega
          counts_close [hP, hA, hS, hC, hW, freeAt, hT']
    · simp at hn
  | exit => simp [next] at hn

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store

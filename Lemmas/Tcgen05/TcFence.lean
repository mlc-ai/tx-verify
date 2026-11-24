-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Order.GuardOrder
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.Order.OrderWaits

@[expose] public section

/-! # tcgen05 orders (DEP-TC-FENCE)

Every tcgen05 order of `Tc/` (completion, pipelines, fenced chains, EXT-TCACQUIRE) is a path
of `TcStep` edges: causality (`hb`), a morally strong mbarrier arrival observed by a wait
(`MbarExec`), or an MMA whose commit a wait observes (`CommitObserved`). With
guarded synchronization these paths have no cycle (`tcStep_acyclic`): a cycle without an
observation is a causality cycle, and one through an observation makes the observing wait
enable its own observed arrival. Frame lemmas transport the orders between executions that
agree on the old events. -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

theorem MbarExec.events {x w : EvId} (h : MbarExec L X x w) :
    x.2 < (X.tr x.1).length ∧ w.2 < (X.tr w.1).length := by
  obtain ⟨m, tx, count, rel, rs, acq, ws, ⟨pcx, hx⟩, ⟨⟨pc, par, hw⟩, -⟩, -⟩ := h
  exact ⟨len_of_get hx, len_of_get hw⟩

theorem TcMma.AfterSync.events {s b : EvId} (h : TcMma.AfterSync L X s b) :
    s.2 < (X.tr s.1).length ∧ b.2 < (X.tr b.1).length := by
  obtain ⟨f, hf, -, hp⟩ := h
  exact ⟨(baseCausality_events hf).1, hp.2.2.1⟩

theorem ExecOrder.events {a b : EvId} (h : ExecOrder L X a b) :
    a.2 < (X.tr a.1).length ∧ b.2 < (X.tr b.1).length := by
  rcases h with h | ⟨x, w, hp, -, h⟩
  · exact h.events
  · refine ⟨?_, h.events.2⟩
    have := hp.2.1
    have := hp.2.2.1
    rw [hp.1]; omega

theorem ExecOrder.of_baseCausality {a f b : EvId} (h : baseCausality L X a f) (hf : X.FenceAfter f)
    (hp : po X f b) :
    ExecOrder L X a b := .inl ⟨f, h, hf, hp⟩

theorem ExecOrder.of_obs {a x w f b : EvId} (hx : po X a x) (h : MbarExec L X x w)
    (hw : baseCausality L X w f) (hf : X.FenceAfter f) (hp : po X f b) : ExecOrder L X a b :=
  .inr ⟨x, w, hx, h, f, hw, hf, hp⟩

end

namespace TcMma

section
variable {L : Launch} {X : Execution}

/-! ## Every tcgen05 order is a path of `TcStep` edges -/

/-- Causality, a morally strong mbarrier observation, or an MMA's observed commit. -/
def TcStep (L : Launch) (X : Execution) (a b : EvId) : Prop :=
  baseCausality L X a b ∨ MbarExec L X a b ∨ CommitObserved L X a b

theorem AfterSync.tcStep {s b : EvId} (h : AfterSync L X s b) :
    Relation.TransGen (TcStep L X) s b := by
  obtain ⟨f, hf, -, hp⟩ := h
  exact .tail (.single (.inl hf)) (.inl (.single (.inl hp)))

theorem ExecOrder.tcStep {a b : EvId} (h : ExecOrder L X a b) :
    Relation.TransGen (TcStep L X) a b := by
  rcases h with h | ⟨x, w, hp, hx, h⟩
  · exact h.tcStep
  · exact .head (.inl (.single (.inl hp))) (.head (.inr (.inl hx)) h.tcStep)

theorem FenceOrder.tcStep {a b : EvId} (h : FenceOrder L X a b) :
    Relation.TransGen (TcStep L X) a b := by
  obtain ⟨fb, hp, -, ha⟩ := h
  exact .head (.inl (.single (.inl hp))) (ExecOrder.tcStep ha)

theorem TcBefore.tcStep {a b : EvId} (h : TcBefore L X a b) :
    Relation.TransGen (TcStep L X) a b :=
  h.elim (fun h => .single (.inl h)) FenceOrder.tcStep

theorem DoneBefore.tcStep {a e : EvId} (h : DoneBefore L X a e) :
    Relation.TransGen (TcStep L X) a e := by
  rcases h with ⟨w, ws, ho, hsc, hw⟩ | ⟨w, ho, hw⟩
  · exact .head (.inr (.inr ⟨true, ws, ho, hsc⟩)) (.single (.inl hw))
  · exact .head (.inr (.inr ho)) hw.tcStep

theorem WaitBefore.tcStep {k : TcKind} {a e : EvId} (h : WaitBefore L X k a e) :
    Relation.TransGen (TcStep L X) a e := by
  obtain ⟨w, ⟨pc, hw⟩, h1, h2, hb⟩ := h
  exact .head (.inl (.single (.inl (po_of_not_access h1.symm h2 (len_of_get hw)
    (by simp [hw, Event.acc]))))) hb.tcStep

/-- A completion of an access (a load, a store, an MMA or a copy) is a tcgen05 order path. -/
theorem CompletedBefore.tcStep {a e : EvId} (h : CompletedBefore L X a e)
    (hk : (∃ x v sh, X.TLd a x v sh) ∨ (∃ x v sh, X.TSt a x v sh) ∨ X.TcAsync a) :
    Relation.TransGen (TcStep L X) a e := by
  rcases hk with hk | hk | hk
  · exact (h.1 hk).tcStep
  · exact (h.2.1 hk).tcStep
  · exact (h.2.2 hk).tcStep

/-- An MMA has completed by its commit-observed completion. -/
theorem CompletedBefore.of_mma {e f : EvId} {d : Nat} {s : OperandSpec} {a : Bool}
    {m : List Nat} (hi : X.MmaIssue e d s a m) (h : DoneBefore L X e f) :
    CompletedBefore L X e f := by
  obtain ⟨pc, hp⟩ := hi
  refine ⟨fun ⟨_, _, _, pc', hp'⟩ => ?_, fun ⟨_, _, _, pc', hp'⟩ => ?_, fun _ => h⟩ <;>
    (rw [hp] at hp'; cases hp')

theorem StoreDoneBefore.tcStep {a e : EvId} (h : StoreDoneBefore L X a e) :
    Relation.TransGen (TcStep L X) a e := by
  obtain ⟨-, h | ⟨-, h, -⟩ | ⟨-, h, -⟩⟩ := h
  · exact h.tcStep
  · exact h.tcStep
  · exact h.tcStep

theorem Pipelined.tcBefore {p q : PipeAccess} {a b : EvId} (h : Pipelined L X p a q b) :
    TcBefore L X a b := by
  cases p <;> cases q <;> simp only [Pipelined] at h <;> exact h.2.1

theorem Before.tcStep {a b : EvId} (h : Before L X a b) : Relation.TransGen (TcStep L X) a b :=
  h.elim DoneBefore.tcStep (fun h => h.tcBefore.tcStep)

theorem WriteBefore.tcStep {a b : EvId} (h : WriteBefore L X a b) :
    Relation.TransGen (TcStep L X) a b := by
  rcases h with h | h | h
  · exact h.tcStep
  · exact h.tcStep
  · exact h.tcBefore.tcStep

/-! ## `TcStep` paths have no cycle under guarded synchronization -/

/-- The successful wait an observation edge ends at. -/
def ObsStep (L : Launch) (X : Execution) (a b : EvId) : Prop :=
  MbarExec L X a b ∨ CommitObserved L X a b

theorem ObsStep.wait {a b : EvId} (h : ObsStep L X a b) :
    ∃ pc m q acq sc, X.get b = some ⟨pc, .wait m q true acq sc⟩ := by
  rcases h with ⟨m, -, -, -, -, acq, sc, -, ⟨⟨pc, q, hw⟩, -⟩, -⟩ |
      ⟨acq, sc, ⟨-, m, -, ⟨pc, q, hw⟩, -⟩, -⟩
  · exact ⟨pc, m, q, acq, sc, hw⟩
  · exact ⟨pc, m, q, acq, sc, hw⟩

theorem not_arrive_of_wait {w : EvId} {pc : Nat} {m : Loc} {q : Nat} {acq : Bool}
    {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m q true acq sc⟩) :
    ∀ m tx count rel sc, ¬ X.Arrive w m tx count rel sc := by
  rintro m' tx count rel sc' ⟨pc', h⟩
  rw [hw] at h
  cases h

/-- A path that is causality, or passes through an observation edge. -/
theorem path_split {a b : EvId} (h : Relation.TransGen (TcStep L X) a b) :
    baseCausality L X a b ∨ ∃ x w, Relation.ReflTransGen (TcStep L X) a x ∧ ObsStep L X x w ∧
      Relation.ReflTransGen (TcStep L X) w b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact .inl h
    · exact .inr ⟨_, _, .refl, h, .refl⟩
  | tail hab h ih =>
    rcases ih with ih | ⟨x, w, h1, h2, h3⟩
    · rcases h with h | h
      · exact .inl (ih.trans h)
      · exact .inr ⟨_, _, (Relation.TransGen.single (.inl ih)).to_reflTransGen, h, .refl⟩
    · exact .inr ⟨x, w, h1, h2, h3.tail h⟩

/-- A successful wait that observed a present counter update of its phase is witnessed by that
update: the observation is a need of the wait (`pollNeeds`, `MbarObserved`). -/
theorem witness_of_waitObserves {b : EvId} {m : Loc} {acq : Bool} {ws : MbarScope}
    {x : AsyncCopy.Ref} (hx : X.RefPresent x) (hu : AsyncCopy.WaitObserves X x b m acq ws)
    (hupd : ∀ r ∈ X.objects m, r.id = x → CounterUpdate r.action) : Witness L X x b := by
  obtain ⟨pcb, par, hwb⟩ := hu.1
  obtain ⟨i, _, r, _, _, hri, hrid, -, -, -, -, -, -, -, -⟩ := hu.2
  have hmo : MbarObserved X r.id (.thread b) :=
    ⟨hrid.symm ▸ hx, b, m, acq, ws, rfl, hrid.symm ▸ hu, fun r' hr' hid =>
      hupd r' hr' (hid.trans hrid)⟩
  have hmem : Need.node (· = r.id) ∈ pollNeeds X b m :=
    List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hri, by
      simp only [needsIf, hmo, ite_true]
      exact List.mem_singleton.mpr rfl⟩
  refine ⟨(· = r.id), ?_, hx, hrid.symm⟩
  rw [show Needs L X b = pollNeeds X b m by simp only [Needs, hwb, KindNeeds, ite_true]]
  exact hmem

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- `a` follows a guard reached by a dependency path from the return of `w`. -/
def Reached (L : Launch) (K : Kernel) (X : Execution) (w a : EvId) : Prop :=
  ∃ g, Relation.ReflTransGen (DepStep L K X) (.thread w, true) (.thread g, true) ∧
    GuardSource K X g ∧
    (TraceBefore X g a ∨ (g = a ∧ ∀ m tx count rel sc, ¬ X.Arrive a m tx count rel sc))

theorem Reached.baseCausality (hg : SyncGuarded L K X) (ho : AsyncCopy.ObjectsOk X)
    (hX : Consistent L K A mem0 X) {w a b : EvId}
    (hI : Reached L K X w a) (h : _root_.PTX.baseCausality L X a b) : Reached L K X w b := by
  have key : ∀ {c}, Reached L K X w c → ∀ {d}, (po X c d ∨ CtaBarSync L X c d ∨
      MSync L X c d ∨ ClusterSync L X c d ∨ WarpBarSync L X c d ∨ synchronizesWith L X c d ∨
      FenceSync L X c d) → Reached L K X w d := by
    rintro c ⟨g, h1, h2, h3⟩ d hcd
    obtain ⟨g', h1', h2', h3'⟩ := guard_step hg ho hX.guardOk
      ⟨g, h1, h2, h3.imp_right fun ⟨he, hna⟩ =>
        ⟨he, fun m tx count sc => hna m tx count true sc⟩⟩ hcd
    exact ⟨g', h1', h2', .inl h3'⟩
  induction h with
  | single h => exact key hI h
  | tail _ h ih => exact key ih h

/-- An observation edge after a guard: the observing wait is reached by a dependency path. The
arrival (or the commit's notification) is a witness of the wait's return, so the path is the
guard, the witness edge and, for a commit, the issue of its notification. -/
theorem Reached.obs (ho : AsyncCopy.ObjectsOk X) {w a b : EvId}
    (hI : Reached L K X w a) (h : ObsStep L X a b) :
    Relation.TransGen (DepStep L K X) (.thread w, true) (.thread b, true) := by
  obtain ⟨g, hwg, hgs, hga⟩ := hI
  have later : ∀ {c : EvId}, a.1 = c.1 → a.2 < c.2 → c.2 < (X.tr c.1).length →
      TraceBefore X g c := by
    intro c h1 h2 h3
    rcases hga with hga | ⟨rfl, -⟩
    · exact ⟨hga.1.trans h1, hga.2.1.trans h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  rcases h with ⟨m, tx, count, rel, rs, acq, ws, harr, hu, -⟩ |
      ⟨acq, ws, ⟨n, m, ⟨c, s, rank, rfl, ht, hc, -, hrank⟩, hu⟩, -⟩
  · obtain ⟨pcx, hx⟩ := harr
    have hga' : TraceBefore X g a := by
      rcases hga with hga | ⟨-, hna⟩
      · exact hga
      · exact (hna m tx count rel rs ⟨pcx, hx⟩).elim
    exact ((Relation.TransGen.tail' hwg (hgs.guard hga')).tail
      (DepStep.of_witness L (witness_of_waitObserves ⟨_, hx⟩ hu
        fun _ hr' hid => arrive_counter ho hx hr' hid)))
  · obtain ⟨pcc, hcget⟩ := hc
    have hpres : X.RefPresent (.thread c) := ⟨_, hcget⟩
    have hwit : Witness L X (.async c (.tcNotify rank)) b :=
      witness_of_waitObserves (x := .async c (.tcNotify rank)) hrank hu
        fun _ hr' hid => async_counter ho hr' hid
    exact ((Relation.TransGen.tail' hwg
      (hgs.guard (later ht.1 ht.2.1 (len_of_get hcget)))).tail
      (DepStep.issue (p := .tcNotify rank) hpres hrank (fun _ h => by cases h)
        (fun h => by cases h) (fun h => by cases h) (fun h => by cases h))).tail
      (DepStep.of_witness L hwit)

theorem Reached.obs_reached (hg : SyncGuarded L K X) (ho : AsyncCopy.ObjectsOk X)
    {w a b : EvId} (hI : Reached L K X w a) (h : ObsStep L X a b) : Reached L K X w b := by
  obtain ⟨pc, m, q, acq, sc, hw⟩ := h.wait
  exact ⟨b, (hI.obs ho h).to_reflTransGen, hg.wait hw, .inr ⟨rfl, not_arrive_of_wait hw⟩⟩

theorem Reached.path (hg : SyncGuarded L K X) (ho : AsyncCopy.ObjectsOk X)
    (hX : Consistent L K A mem0 X) {w a b : EvId}
    (hI : Reached L K X w a) (h : Relation.ReflTransGen (TcStep L X) a b) :
    Reached L K X w b := by
  induction h with
  | refl => exact hI
  | tail _ h ih =>
    rcases h with h | h
    · exact ih.baseCausality hg ho hX h
    · exact ih.obs_reached hg ho h

/-- **tcgen05 orders have no cycle** in a consistent execution with guarded synchronization. -/
theorem tcStep_acyclic {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (a : EvId) : ¬ Relation.TransGen (TcStep L X) a a := by
  intro h
  rcases path_split h with h | ⟨x, w, h1, h2, h3⟩
  · exact baseCausality_irrefl hX.object.cause h
  · have ho := hX.effectValidity.tma.2.2.1
    obtain ⟨pc, m, q, acq, sc, hw⟩ := h2.wait
    have hI : Reached L K X w w :=
      ⟨w, .refl, hg.wait hw, .inr ⟨rfl, not_arrive_of_wait hw⟩⟩
    exact (DepStepAcyclic.of_dependency hX.dependency) (.thread w, true)
      ((hI.path hg ho hX (h3.trans h1)).obs ho h2)

/-- The wait of an execution ordering's observation is not causally before the ordering's
start: in a consistent execution an ordering through its one observation (EXT-TC-EXEC-ORDER)
never closes a cycle. Restated: the observation axiom `ObservationCausal` covers synchronizing
observations (`SyncObserved`, a release counter update observed by an acquire wait), so this
records the ordering's observation as such rather than existentially (`MbarExec`). -/
theorem ExecOrder.obs_not_back {mem0 : Mem0} (hX : Consistent L K A mem0 X) {s x w : EvId}
    (hp : po X s x) {m : Loc} {tx count : Nat} {rs ws : MbarScope}
    (harr : X.Arrive x m tx count true rs)
    (hu : AsyncCopy.WaitObserves X (.thread x) w m true ws) (hsc : ScopesMeet L rs x.1 ws w.1) :
    ¬ baseCausality L X w s := by
  intro hws
  obtain ⟨pcx, hx⟩ := harr
  obtain ⟨pc, q, hw⟩ := hu.1
  have ho := hX.effectValidity.tma.2.2.1
  have hmo : MbarObserved X (.thread x) (.thread w) :=
    ⟨⟨_, hx⟩, w, m, true, ws, rfl, hu, fun r hr hid => arrive_counter ho hx hr hid⟩
  have hso : SyncObserved L X (.thread x) (.thread w) :=
    .inl ⟨hmo, w, m, pc, q, ws, rs, x.1, rfl, hw,
      (.inl ⟨x, m, tx, count, rfl, rfl, ⟨pcx, hx⟩⟩), hsc⟩
  exact hX.observation _ _ hso
    (.single (.inr (.inl ⟨rfl, rfl, w, x, rfl, rfl, hws.tail (.inl hp)⟩)))

/-- Two tcgen05 orders between the same events in both directions form a cycle. -/
theorem tcStep_asymm {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    {a b : EvId} (h1 : Relation.TransGen (TcStep L X) a b)
    (h2 : Relation.TransGen (TcStep L X) b a) : False :=
  tcStep_acyclic hX hg a (h1.trans h2)

/-- An observed completion names a delivered commit tracking the MMA. -/
theorem DoneBefore.tracked {i e : EvId} (h : DoneBefore L X i e) :
    ∃ commit rank, AsyncCopy.TracksMma X i commit ∧ rank ∈ X.tcNotified commit := by
  rcases h with ⟨w, ws, ho, -, -⟩ | ⟨w, ⟨acq, ws, ho, -⟩, -⟩
  · obtain ⟨c, s, rank, m, ht, -, -, hn, -⟩ := ho.mma
    exact ⟨c, rank, ht, hn⟩
  · obtain ⟨c, s, rank, m, ht, -, -, hn, -⟩ := ho.mma
    exact ⟨c, rank, ht, hn⟩

/-- An observed completion implies the MMA completed. -/
theorem DoneBefore.done {i e : EvId} (h : DoneBefore L X i e) (hm : AsyncCopy.CommitOk X) :
    X.async.mmaDone i = true := by
  obtain ⟨c, rank, ht, hn⟩ := h.tracked
  exact (hm c rank hn).2 i ht

theorem TcStep.events {a b : EvId} (h : TcStep L X a b) :
    a.2 < (X.tr a.1).length ∧ b.2 < (X.tr b.1).length := by
  rcases h with h | h | ⟨acq, ws, ⟨n, m, ⟨c, s, rank, rfl, ⟨h1, h2, -, -⟩, ⟨pcc, hc⟩, -⟩,
      ⟨⟨pc, q, hw⟩, -⟩⟩, -⟩
  · exact baseCausality_events h
  · exact h.events
  · have := len_of_get hc
    exact ⟨by rw [h1]; omega, len_of_get hw⟩

theorem tcStep_path_events {a b : EvId} (h : Relation.TransGen (TcStep L X) a b) :
    a.2 < (X.tr a.1).length ∧ b.2 < (X.tr b.1).length := by
  induction h with
  | single h => exact h.events
  | tail _ h ih => exact ⟨ih.1, h.events.2⟩

end

section
variable {L : Launch} {X : Execution}

/-- Within one thread an acyclic tcgen05 order follows program order. -/
theorem tcStep_same_thread (hac : ∀ n, ¬ Relation.TransGen (TcStep L X) n n) {a b : EvId}
    (h : Relation.TransGen (TcStep L X) a b) (ht : a.1 = b.1)
    (hna : (X.get b).bind Event.acc = none) : a.2 < b.2 := by
  by_contra hle
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
  · have hb := (tcStep_path_events h).1
    exact hac _ (h.tail (.inl (.single (.inl (po_of_source_not_access ht.symm hlt hb hna)))))
  · have : a = b := Prod.ext ht heq.symm
    subst this
    exact hac _ h

end

/-! ## Frames: executions that agree on old events -/

section Frame
variable {L : Launch} {X Y : Execution}

theorem le_get_old (hle : X.le Y) {e : EvId} (he : e.2 < (X.tr e.1).length) :
    Y.get e = X.get e := by
  obtain ⟨suffix, hs⟩ := hle.1 e.1
  unfold Execution.get
  rw [← hs, List.getElem?_append_left he]

theorem le_po_old (hle : X.le Y) {a b : EvId} (hb : b.2 < (X.tr b.1).length) :
    po Y a b ↔ po X a b := by
  have hlen := (hle.1 b.1).length_le
  exact po_congr hb (by omega) (fun x hx => le_get_old hle hx)

theorem po_lt_left {Z : Execution} {a b : EvId} (h : po Z a b) (hb : b.2 < (X.tr b.1).length) :
    a.2 < (X.tr a.1).length := by
  have := h.2.1
  rw [h.1]; omega

theorem afterSync_events {s b : EvId} (ha : AfterSync L X s b) : s.2 < (X.tr s.1).length :=
  ha.events.1

theorem execOrder_events {s b : EvId} (ha : ExecOrder L X s b) : s.2 < (X.tr s.1).length :=
  ha.events.1

/-- The new tcgen05 evidence an extension may add about old events: none. -/
structure TcFrame (L : Launch) (X Y : Execution) : Prop where
  le : X.le Y
  hb : ∀ {x f : EvId}, f.2 < (X.tr f.1).length → (baseCausality L Y x f ↔ baseCausality L X x f)
  mbarExec : ∀ {x f : EvId}, f.2 < (X.tr f.1).length → (MbarExec L Y x f ↔ MbarExec L X x f)
  observed : ∀ {x w : EvId} {acq : Bool} {ws : MbarScope}, w.2 < (X.tr w.1).length →
    (AsyncCopy.AsyncObserved Y x .mmaDone w acq ws ↔ AsyncCopy.AsyncObserved X x .mmaDone w acq ws)

namespace TcFrame
variable (h : TcFrame L X Y)
include h

theorem commit {x w : EvId} (hw : w.2 < (X.tr w.1).length) :
    CommitObserved L Y x w ↔ CommitObserved L X x w := by
  unfold CommitObserved
  simp only [h.observed hw]

theorem afterSync {s b : EvId} (hb : b.2 < (X.tr b.1).length) :
    AfterSync L Y s b ↔ AfterSync L X s b := by
  constructor
  · rintro ⟨f, he, ⟨pc, hf⟩, hp⟩
    have hfo := po_lt_left hp hb
    exact ⟨f, (h.hb hfo).mp he, ⟨pc, (le_get_old h.le hfo).symm.trans hf⟩,
      (le_po_old h.le hb).mp hp⟩
  · rintro ⟨f, he, ⟨pc, hf⟩, hp⟩
    have hfo := po_lt_left hp hb
    exact ⟨f, (h.hb hfo).mpr he, ⟨pc, (le_get_old h.le hfo).trans hf⟩,
      (le_po_old h.le hb).mpr hp⟩

theorem execOrder {s b : EvId} (hb : b.2 < (X.tr b.1).length) :
    ExecOrder L Y s b ↔ ExecOrder L X s b := by
  constructor
  · rintro (ha | ⟨x, w, hp, hx, ha⟩)
    · exact .inl ((h.afterSync hb).mp ha)
    · have ha' := (h.afterSync hb).mp ha
      have hx' := (h.mbarExec (afterSync_events ha')).mp hx
      exact .inr ⟨x, w, (le_po_old h.le hx'.events.1).mp hp, hx', ha'⟩
  · rintro (ha | ⟨x, w, hp, hx, ha⟩)
    · exact .inl ((h.afterSync hb).mpr ha)
    · exact .inr ⟨x, w, (le_po_old h.le hx.events.1).mpr hp,
        (h.mbarExec (afterSync_events ha)).mpr hx, (h.afterSync hb).mpr ha⟩

theorem fenceOrder {a b : EvId} (hb : b.2 < (X.tr b.1).length) :
    FenceOrder L Y a b ↔ FenceOrder L X a b := by
  constructor
  · rintro ⟨fb, hp, ⟨pc, hf⟩, ha⟩
    have ha' := (h.execOrder hb).mp ha
    have hfo := execOrder_events ha'
    exact ⟨fb, (le_po_old h.le hfo).mp hp, ⟨pc, (le_get_old h.le hfo).symm.trans hf⟩, ha'⟩
  · rintro ⟨fb, hp, ⟨pc, hf⟩, ha⟩
    have hfo := execOrder_events ha
    exact ⟨fb, (le_po_old h.le hfo).mpr hp, ⟨pc, (le_get_old h.le hfo).trans hf⟩,
      (h.execOrder hb).mpr ha⟩

theorem tcBefore {a b : EvId} (hb : b.2 < (X.tr b.1).length) :
    TcBefore L Y a b ↔ TcBefore L X a b :=
  or_congr (h.hb hb) (h.fenceOrder hb)

theorem doneBefore {i e : EvId} (he : e.2 < (X.tr e.1).length) :
    DoneBefore L Y i e ↔ DoneBefore L X i e := by
  constructor
  · rintro (⟨w, ws, ho, hsc, hw⟩ | ⟨w, ho, hw⟩)
    · have hw' := (h.hb he).mp hw
      exact .inl ⟨w, ws, (h.observed (baseCausality_events hw').1).mp ho, hsc, hw'⟩
    · have hw' := (h.afterSync he).mp hw
      exact .inr ⟨w, (h.commit (afterSync_events hw')).mp ho, hw'⟩
  · rintro (⟨w, ws, ho, hsc, hw⟩ | ⟨w, ho, hw⟩)
    · exact .inl ⟨w, ws, (h.observed (baseCausality_events hw).1).mpr ho, hsc, (h.hb he).mpr hw⟩
    · exact .inr ⟨w, (h.commit (afterSync_events hw)).mpr ho, (h.afterSync he).mpr hw⟩

theorem waitBefore {k : TcKind} {x e : EvId} (he : e.2 < (X.tr e.1).length) :
    WaitBefore L Y k x e ↔ WaitBefore L X k x e := by
  constructor
  · rintro ⟨w, ⟨pc, hw⟩, h1, h2, hb⟩
    have hb' := (h.tcBefore he).mp hb
    have hwo := (tcStep_path_events hb'.tcStep).1
    exact ⟨w, ⟨pc, (le_get_old h.le hwo).symm.trans hw⟩, h1, h2, hb'⟩
  · rintro ⟨w, ⟨pc, hw⟩, h1, h2, hb⟩
    have hwo := (tcStep_path_events hb.tcStep).1
    exact ⟨w, ⟨pc, (le_get_old h.le hwo).trans hw⟩, h1, h2, (h.tcBefore he).mpr hb⟩

end TcFrame

/-- Executions with the same events, causality and mbarrier observations have the same
fenced orders. -/
theorem tcBefore_congr (hget : ∀ i, Y.get i = X.get i) (hhb : ∀ i j, baseCausality L Y i j ↔
    baseCausality L X i j)
    (hme : ∀ i j, MbarExec L Y i j ↔ MbarExec L X i j) (a b : EvId) :
    (AfterSync L Y a b ↔ AfterSync L X a b) ∧ (TcBefore L Y a b ↔ TcBefore L X a b) := by
  have htr : ∀ g, Y.tr g = X.tr g := fun g => List.ext_getElem? fun i => hget (g, i)
  have hpo : ∀ a b, po Y a b ↔ po X a b := by
    intro a b
    simp only [_root_.PTX.po, htr, SameAccess, hget]
  have haf : ∀ a b, AfterSync L Y a b ↔ AfterSync L X a b := by
    intro a b
    simp only [AfterSync, hhb, Execution.FenceAfter, hget, hpo]
  have hex : ∀ a b, ExecOrder L Y a b ↔ ExecOrder L X a b := by
    intro a b
    simp only [ExecOrder, haf, hme, hpo]
  refine ⟨haf a b, ?_⟩
  simp only [TcBefore, FenceOrder, hhb, hex, Execution.FenceBefore, hget, hpo]

/-- Executions with the same events, order and observations have the same tcgen05 orders. -/
structure TcSame (L : Launch) (X Y : Execution) : Prop where
  get : ∀ i, Y.get i = X.get i
  hb : ∀ i j, baseCausality L Y i j ↔ baseCausality L X i j
  mbarExec : ∀ i j, MbarExec L Y i j ↔ MbarExec L X i j
  observed : ∀ i j acq ws,
    AsyncCopy.AsyncObserved Y i .mmaDone j acq ws ↔ AsyncCopy.AsyncObserved X i .mmaDone j acq ws

namespace TcSame
variable (h : TcSame L X Y)
include h

theorem afterSync (a b : EvId) : AfterSync L Y a b ↔ AfterSync L X a b :=
  (tcBefore_congr h.get h.hb h.mbarExec a b).1

theorem tcBefore (a b : EvId) : TcBefore L Y a b ↔ TcBefore L X a b :=
  (tcBefore_congr h.get h.hb h.mbarExec a b).2

theorem commit (a b : EvId) : CommitObserved L Y a b ↔ CommitObserved L X a b := by
  simp only [CommitObserved, h.observed]

theorem doneBefore (a b : EvId) : DoneBefore L Y a b ↔ DoneBefore L X a b := by
  simp only [DoneBefore, h.observed, h.hb, h.commit, h.afterSync]

end TcSame

/-- A record appended for an operation other than the wait cannot change its observations. -/
theorem appendObject_mbarExec_iff {m : Loc} {r : MBarrier.Record AsyncCopy.Ref} {x w : EvId}
    (hnw : r.id ≠ .thread w) :
    MbarExec L (X.appendObject m r) x w ↔ MbarExec L X x w := by
  unfold MbarExec
  simp only [appendObject_waitObserves_iff hnw]
  rfl

end Frame


end TcMma

end
end PTX

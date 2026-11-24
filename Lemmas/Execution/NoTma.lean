-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Async.AsyncCopy
public import Lemmas.Isa.Tmpl

@[expose] public section

/-!
# Kernels without mbarrier or bulk-copy instructions

If no instruction of a kernel is an mbarrier or bulk-copy instruction (`Kernel.NoTma`),
no possible execution has such an event (`noTma_of_consistent`). Then the rules for them
are vacuous: no mbarrier synchronization, no copy writes, `TmaOk` holds and `TmaUnsafe`
does not, and every event counts toward the size.
-/

namespace PTX

def Op.isTma (op : Op) : Bool := match op with
  | .mem a => match a.sem with
    | .acquire | .release | .acqRel => true
    | _ => false
  | .warp w => match w.kind with
    | .shfl _ => false
    | _ => true
  | .barSync .. | .barSyncN .. | .ret | .exit | .trap => false
  | _ => !op.isLocal

/-- An event kind outside the memory consistency model: a thread's read or write without strong
semantics, a non-coherent read, a CTA barrier arrival, a shuffle, an atomic read-modify-write, a
read of the changing special registers, an exit or undefined behaviour. -/
def Kind.isTma : Kind → Bool
  | .rd a _ => a.acquire
  | .wr a _ => a.release
  | .nc .. | .bar _ _ .sync | .shfl .. | .rmw .. | .sreg .. | .exit | .ub .. => false
  | _ => true

/-- A template outside the memory consistency model, as for `Kind.isTma`. -/
def Tmpl.isTma : Tmpl → Bool
  | .read a _ => a.acquire
  | .write a _ _ => a.release
  | .readNC .. | .bar _ _ _ .sync | .shfl .. | .rmw .. | .sreg .. | .exit | .ub .. => false
  | _ => true

/-- No instruction of `K` is an mbarrier, bulk-copy or `tcgen05` instruction; checked by
`rfl`. -/
def Kernel.NoTma (K : Kernel) : Prop := K.code.all (fun ins => !ins.op.isTma) = true

/-- No event of `X` is an mbarrier or bulk-copy event. -/
def Execution.NoTma (X : Execution) : Prop :=
  ∀ v pc k, X.get v = some ⟨pc, k⟩ → k.isTma = false

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem loadTmpl_noTma {t : TState} {sp : Space} {nc : Bool} {w : Nat} {ds : List Nat}
    {base : Nat} {off : Int} : (loadTmpl A L g t sp nc w ds base off).isTma = false := by
  unfold loadTmpl
  cases he : effAddr L g t sp base off with
  | error f => rfl
  | ok loc =>
    simp only [bind, Except.bind, elemAcc]
    by_cases hal : w / 8 = 0 ∨ loc.addr % (w / 8 * ds.length) ≠ 0
    · rw [ite_eq_left hal]; rfl
    · rw [ite_eq_right hal]
      simp only [pure, Except.pure]
      split
      · split <;> rfl
      · rfl

theorem storeTmpl_noTma {t : TState} {sp : Space} {w : Nat} {base : Nat} {off : Int}
    {srcs : List Opnd} : (storeTmpl L g t sp w base off srcs).isTma = false := by
  unfold storeTmpl
  cases he : effAddr L g t sp base off with
  | error f => rfl
  | ok loc =>
    simp only [bind, Except.bind, elemAcc]
    by_cases hal : w / 8 = 0 ∨ loc.addr % (w / 8 * srcs.length) ≠ 0
    · rw [ite_eq_left hal]; rfl
    · rw [ite_eq_right hal]
      simp only [pure, Except.pure]
      split
      · rfl
      · split
        · rfl
        · rfl

theorem barTmpl_noTma {t : TState} {a : Opnd} {c : Option Opnd} :
    (barTmpl L g t a c).isTma = false := by
  unfold barTmpl
  repeat' first
    | rfl
    | split

theorem shflTmpl_noTma {t : TState} {mode : ShflMode} {d : Nat} {p : Option Nat}
    {a b c mask : Opnd} : (shflTmpl L g t mode d p a b c mask).isTma = false := by
  unfold shflTmpl; split
  · split
    · split <;> rfl
    · rfl
  all_goals rfl

/-- The footprint `accessAcc` computes for an access without `.acquire`, `.release` or
`.acq_rel` semantics carries neither an `.acquire` nor a `.release` flag. -/
theorem accessAcc_noTma {t : TState} {a : MemAccess} {acc : Acc}
    (hs : a.sem = .weak ∨ a.sem = .relaxed ∨ a.sem = .volatile)
    (h : accessAcc L g t a = .ok acc) : acc.acquire = false ∧ acc.release = false := by
  obtain ⟨acc0, he, h1, h2, _⟩ := accessAcc_semAcc h
  rw [← he]
  rcases hs with hs | hs | hs <;> simp [MemAccess.semAcc, hs, h1, h2]

/-- An access without strong semantics: its memory template is outside the consistency model. -/
theorem accessTmpl_noTma {t : TState} {a : MemAccess}
    (h : (match a.sem with | .acquire | .release | .acqRel => true | _ => false) = false) :
    (accessTmpl A L g t a).isTma = false := by
  have hs : a.sem = .weak ∨ a.sem = .relaxed ∨ a.sem = .volatile := by
    cases ha : a.sem <;> simp_all
  unfold accessTmpl bulkInitTmpl
  dsimp only
  repeat' first
    | rfl
    | split
    | exact (accessAcc_noTma hs ‹_›).1
    | exact (accessAcc_noTma hs ‹_›).2

/-- An atomic read-modify-write has no `.acquire` or `.release` event: its footprint is the
access's own (`MemAccess.atomAcc`). -/
theorem atomTmpl_noTma {t : TState} {a : MemAccess} :
    (atomTmpl A L g t a).isTma = false := by
  unfold atomTmpl
  dsimp only
  repeat' first
    | rfl
    | split

theorem memTmpl_noTma {t : TState} {a : MemAccess}
    (h : (match a.sem with | .acquire | .release | .acqRel => true | _ => false) = false) :
    (memTmpl A L g t a).isTma = false := by
  unfold memTmpl
  split
  · split
    · simp_all
    · exact loadTmpl_noTma
    · simp_all
    · exact storeTmpl_noTma
    · exact accessTmpl_noTma h
  · exact atomTmpl_noTma
  · split
    · exact accessTmpl_noTma h
    · rfl

theorem warpTmpl_noTma {t : TState} {w : WarpInstr}
    (h : (match w.kind with | .shfl _ => false | _ => true) = false) :
    (warpTmpl L g t w).isTma = false := by
  unfold warpTmpl
  split
  · exact shflTmpl_noTma
  all_goals first | rfl | simp_all

/-- A thread-local template is outside the consistency model: it is a read of the changing
special registers or undefined behaviour. -/
theorem localSregTmpl_noTma {t : TState} {r : RuleId} {op : Op} :
    (localSregTmpl A L g t r op).isTma = false := by
  cases r <;> simp [localSregTmpl, sregTmpl, Tmpl.isTma]

theorem eventTmpl_noTma {t : TState} {op : Op} (h : op.isTma = false) :
    (eventTmpl A L g t op).isTma = false := by
  cases op
  case mem a => exact memTmpl_noTma h
  case warp w => exact warpTmpl_noTma h
  case int i => simp only [eventTmpl, Op.rule]; split <;> first | rfl | exact localSregTmpl_noTma
  case move m => simp only [eventTmpl, Op.rule]; split <;> first | rfl | exact localSregTmpl_noTma
  case cvt c => simp only [eventTmpl, Op.rule]; split <;> first | rfl | exact localSregTmpl_noTma
  all_goals simp only [Op.isTma, Op.isLocal, Bool.not_true, Bool.not_false,
    Bool.true_eq_false] at h
  all_goals simp only [eventTmpl]
  all_goals first
    | exact barTmpl_noTma
    | rfl

theorem out_noTma (hK : K.NoTma) {t : TState} {m : Tmpl} (h : out K A L g t = .ev m) :
    m.isTma = false := by
  unfold out at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · rename_i ins hins
      split at h
      · cases h; rfl
      · cases h
      · split at h
        · split at h
          · cases h
          · cases h; rfl
        · cases h
          have := List.all_eq_true.mp hK ins (List.mem_of_getElem? hins)
          simp only [Bool.not_eq_true'] at this
          exact eventTmpl_noTma this

theorem fires_noTma {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : m.isTma = false)
    (h : Fires pc m e o) : e.kind.isTma = false := by
  cases m <;> simp only [Tmpl.isTma, Bool.true_eq_false] at hm <;>
    simp only [Fires] at h
  case read => obtain ⟨bs, _, rfl, _⟩ := h; exact hm
  case readNC => obtain ⟨bs, _, rfl, _⟩ := h; rfl
  case shfl => obtain ⟨r, k, rfl, _⟩ := h; rfl
  case bar mode => cases mode <;> simp only [Bool.true_eq_false] at hm; rw [h.1]; rfl
  case rmw => obtain ⟨old, -, rfl, -⟩ := h; rfl
  case sreg => obtain ⟨vals, -, rfl, -⟩ := h; rfl
  all_goals rw [h.1]; first | exact hm | rfl

theorem run_noTma (hK : K.NoTma) {t : TState} {l : List Event} {o : Option TState}
    (h : Run K A L g t l o) : ∀ e ∈ l, e.kind.isTma = false := by
  induction h with
  | nil => simp
  | step _ he _ ih =>
    obtain ⟨m, hm, hf⟩ := he
    intro e' h'
    rcases List.mem_cons.mp h' with rfl | h'
    · exact fires_noTma (out_noTma hK hm) hf
    · exact ih e' h'
  | last _ he =>
    obtain ⟨m, hm, hf⟩ := he
    intro e' h'
    rcases List.mem_singleton.mp h' with rfl
    exact fires_noTma (out_noTma hK hm) hf

theorem noTma_of_consistent {mem0 : Mem0} {X : Execution} (hK : K.NoTma)
    (hX : Consistent L K A mem0 X) : X.NoTma := by
  intro v pc k hv
  have hlt : v.2 < (X.tr v.1).length := by
    unfold Execution.get at hv; exact (List.getElem?_eq_some_iff.mp hv).1
  have hg : v.1 < L.threads := by
    by_contra hn; rw [hX.outside v.1 (by omega)] at hlt; simp at hlt
  obtain ⟨o, hr⟩ := hX.thr v.1 hg
  have hmem : (⟨pc, k⟩ : Event) ∈ X.tr v.1 := by
    unfold Execution.get at hv; exact List.mem_of_getElem? hv
  exact run_noTma hK hr _ hmem

end

/-- No event of `X` is a `tcgen05` event. -/
def Execution.NoTc (X : Execution) : Prop := ∀ e pc k, X.get e ≠ some ⟨pc, .tc k⟩

namespace Execution.NoTc
variable {L : Launch} {X : Execution} (h : X.NoTc)
include h

theorem not_mma_issue {x : EvId} {d : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} : ¬ X.MmaIssue x d s accum mask := fun ⟨_, hp⟩ => h _ _ _ hp

theorem not_tld {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape} : ¬ X.TLd e a vals sh :=
  fun ⟨_, hp⟩ => h _ _ _ hp

theorem not_commit {e : EvId} {s : TcCommit.Spec} : ¬ X.Commit e s := fun ⟨_, hp⟩ => h _ _ _ hp

theorem emptyHistory (hh : Tmem.Pair.HistoriesOk L X) (cta : Nat) : X.tmemHistory cta = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  exact h _ _ _ (((hh.1 cta).1 r hr).2.2.2.2.1 0)

theorem emptyPairing (hh : Tmem.Pair.HistoriesOk L X) : X.tmemPairing = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  exact h _ _ _ ((hh.2.1 q hq).1.2.1.2.2.1 0)

theorem not_resourceUnsafe (hh : Tmem.Pair.HistoriesOk L X) : ¬ Tmem.Pair.ResourceUnsafe L X := by
  rintro ⟨cta, ⟨reason, hk⟩ | ⟨k, l, d, a, hk, _⟩⟩ <;>
    simp [h.emptyHistory hh cta, Tmem.Pair.runRequests] at hk

theorem not_releaseUnsafe (hh : Tmem.Pair.HistoriesOk L X) : ¬ Tmem.Pair.ReleaseUnsafe L X := by
  rintro ⟨_, _, hr⟩
  apply hr
  intro cta s hs
  rw [h.emptyHistory hh cta] at hs
  simp only [Tmem.Pair.runRequests, Tmem.Outcome.done.injEq] at hs
  subst s
  rfl

theorem not_mmaCell {e : EvId} {cell : TcMma.Cell} : ¬ X.MmaCell e cell := by
  rintro ⟨_, _, _, _, _, _, hi, -⟩
  exact (h.not_mma_issue hi).elim

theorem not_mmaReadCell {e : EvId} {cell : TcMma.Cell} : ¬ X.MmaReadCell e cell := by
  rintro ⟨_, _, _, _, _, hi, -⟩
  exact (h.not_mma_issue hi).elim

theorem not_mmaACell {e : EvId} {cell : TcMma.Cell} : ¬ X.MmaACell e cell := by
  rintro ⟨_, _, _, _, _, _, hi, -⟩
  exact (h.not_mma_issue hi).elim

theorem not_mmaAccess {e : EvId} {cell : TcMma.Cell} : ¬ X.MmaAccess e cell := by
  rintro (hc | hr | ha)
  · exact h.not_mmaCell hc
  · exact h.not_mmaReadCell hr
  · exact h.not_mmaACell ha

theorem not_loadCell {e : EvId} {j : Nat} {cell : TcMma.Cell} :
    ¬ TcMma.LoadCell L X e j cell := by
  rintro ⟨_, _, _, hl, -⟩
  exact (h.not_tld hl).elim

theorem not_storeCell {e : EvId} {cell : TcMma.Cell} : ¬ TcMma.StoreCell L X e cell := by
  rintro ⟨_, _, _, _, ⟨pc, hs⟩, -⟩
  exact h _ _ _ hs

theorem not_cpCell {e : EvId} {cell : TcMma.Cell} : ¬ TcMma.CpCell X e cell := by
  rintro ⟨_, _, _, _, ⟨pc, hc⟩, -⟩
  exact h _ _ _ hc

theorem not_shiftCell {e : EvId} {cell : TcMma.Cell} : ¬ TcMma.ShiftCell X e cell := by
  rintro ⟨_, ⟨pc, hs⟩, -⟩
  exact h _ _ _ hs

theorem not_shiftReadCell {e : EvId} {cell : TcMma.Cell} : ¬ TcMma.ShiftReadCell X e cell := by
  rintro ⟨_, ⟨pc, hs⟩, -⟩
  exact h _ _ _ hs

theorem not_access {e : EvId} {cell : TcMma.Cell} : ¬ Tmem.Pair.Access L X e cell := by
  rintro (hm | ⟨j, hl⟩ | hs | hc | hsh | hsr)
  · exact h.not_mmaAccess hm
  · exact h.not_loadCell hl
  · exact h.not_storeCell hs
  · exact h.not_cpCell hc
  · exact h.not_shiftCell hsh
  · exact h.not_shiftReadCell hsr

theorem not_accessUnsafe : ¬ Tmem.Pair.AccessUnsafe L X :=
  fun hu => hu fun _ _ ha => (h.not_access ha).elim

theorem pairResult : Tmem.Pair.ResultOk L X :=
  fun _ _ _ _ _ he => (h _ _ _ he).elim

theorem not_tcK {e : EvId} {k : Nat} : ¬ X.TcK e k := by
  rintro ⟨⟨⟨pc, kd⟩, hp, hc⟩, -⟩
  cases kd <;> first | exact h _ _ _ hp | cases hc

theorem not_writesUnsafe : ¬ TcMma.WritesUnsafe L X := fun hu =>
  hu fun _ _ _ hx _ => by
    rcases hx with hm | hs | hc | hsh
    · exact (h.not_mmaCell hm).elim
    · exact (h.not_storeCell hs).elim
    · exact (h.not_cpCell hc).elim
    · exact (h.not_shiftCell hsh).elim

theorem not_instructionUnsafe {A : List Assumption} : ¬ TcMma.InstructionUnsafe L A X :=
  fun hu => hu ⟨fun i d s accum mask hi => (h.not_mma_issue hi).elim,
    fun i c hi => by obtain ⟨pc, hc⟩ := hi; exact (h _ _ _ hc).elim,
    TcMma.collectorSafe_of_noReuse fun i d s accum mask hi => by
      obtain ⟨pc, hc⟩ := hi; exact (h _ _ _ hc).elim⟩

theorem not_readsUnsafe : ¬ TcMma.ReadsUnsafe L X := fun hu =>
  hu fun k _ _ _ hr _ => by
    cases k
    · exact hr.elim
    · obtain ⟨_, _, _, _, _, hi, _⟩ := hr
      exact (h.not_mma_issue hi).elim
    · obtain ⟨_, _, _, _, _, _, hi, _⟩ := hr
      exact (h.not_mma_issue hi).elim
    · obtain ⟨_, ⟨_, hi⟩, _⟩ := hr
      exact (h _ _ _ hi).elim

/-- No `tcgen05` event, so no two lanes of a warp diverge at a `tcgen05` instruction. -/
theorem not_tcDivergent {K : Kernel} : ¬ AlignedClass.tc.Divergent L K X := by
  rw [AlignedClass.divergent_tc_iff]
  rintro ⟨_, _, _, _, _, _, _, -, hk, -⟩
  exact h.not_tcK hk

/-- No `tcgen05` event, so no participant of a `tcgen05` instruction exits before another
performs one. -/
theorem not_tcExited {K : Kernel} : ¬ AlignedClass.tc.Exited L K X := by
  rw [AlignedClass.exited_tc_iff]
  rintro ⟨_, _, _, -, hk, -⟩
  exact h.not_tcK hk

/-- A non-`tcgen05` execution has no Tensor Memory read that would need a source. -/
theorem sourceSafe {A : List Assumption} : TcMma.SourceSafe L A X := by
  intro k e cell hr
  cases k with
  | ld => obtain ⟨j, hj⟩ := hr; exact (h.not_loadCell hj).elim
  | acc => exact (h.not_mmaReadCell hr.2).elim
  | a => exact (h.not_mmaACell hr.2).elim
  | shift => exact hr.elim

end Execution.NoTc

namespace Execution.NoTma
variable {L : Launch} {mem0 : Mem0} {X : Execution} (h : X.NoTma)
include h

theorem noTc : X.NoTc := fun e pc _ hp => by cases h e pc _ hp

theorem not_arrive {e : EvId} {m : Loc} {tx count : Nat} {release : Bool} {scope : MbarScope} :
    ¬ X.Arrive e m tx count release scope := by
  rintro ⟨pc, hp⟩; cases h e pc _ hp

theorem not_copy {e : EvId} {s : AsyncCopy.Spec} : ¬ X.Copy e s := by
  rintro ⟨pc, hp⟩; cases h e pc _ hp

theorem not_mbInit {e : EvId} {m : Loc} {c : Nat} : ¬ X.MbInit e m c := by
  rintro ⟨pc, hp⟩; cases h e pc _ hp

theorem not_usesMbar {e : EvId} {m : Loc} : ¬ X.UsesMbar e m := by
  rintro (⟨tx, count, rel, scope, ha⟩ | ⟨s, hc, -⟩ | ⟨noinc, ⟨pc, hp⟩⟩ |
    ⟨_, _, ⟨pc, hp⟩, -⟩ | ⟨pc, q, ok, acq, scope, hp⟩ | ⟨pc, hp⟩ |
    ⟨_, _, ⟨pc, hp⟩, -⟩ | ⟨_, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, ⟨pc, hp⟩⟩)
  · exact h.not_arrive ha
  · exact h.not_copy hc
  · cases h e pc _ hp
  · cases h e pc _ hp
  · cases h e pc _ hp
  · cases h e pc _ hp
  · cases h e pc _ hp
  · cases h e pc _ hp
  · cases h e pc _ hp

theorem not_msync {e f : EvId} : ¬ MSync L X e f := by
  rintro ⟨x, w, m, rs, ws, -, ⟨⟨pc, parity, hp⟩, -⟩, -⟩; cases h _ _ _ hp

/-- A non-async kernel cannot supply an object operation or completion origin. -/
theorem objectAction_none (m : Loc) (id : AsyncCopy.Ref) :
    AsyncCopy.objectAction X X.async m id = none := by
  cases id with
  | thread e =>
    cases he : X.get e with
    | none => simp [AsyncCopy.objectAction, he]
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      have hn := h e pc kind he
      cases kind <;> simp_all [Kind.isTma, AsyncCopy.objectAction]
  | async i p =>
    cases he : X.get i with
    | none => cases p <;> simp [AsyncCopy.objectAction, AsyncCopy.issuedBy, he]
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      have hn := h i pc kind he
      cases p <;> cases kind <;>
        simp_all [Kind.isTma, AsyncCopy.objectAction, AsyncCopy.issuedBy]

theorem objects_empty {K : Kernel} {A : List Assumption}
    (hc : Consistent L K A mem0 X) (m : Loc) : X.objects m = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  have hh := (hc.tma.2.2.1 m).2.1 r hr
  rw [h.objectAction_none] at hh
  cases hh.1

theorem other_empty {K : Kernel} {A : List Assumption}
    (hc : Consistent L K A mem0 X) (i : EvId) :
    X.tensor i = none ∧ X.tensorStores i = none ∧ X.clc i = {} ∧ X.tcNotified i = ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases he : X.tensor i with
    | none => rfl
    | some o =>
      obtain ⟨addr, pc, hi⟩ := (hc.tensor i o he).1
      cases h i pc _ hi
  · cases he : X.tensorStores i with
    | none => rfl
    | some o =>
      obtain ⟨addr, pc, hi⟩ := (hc.store i o he).1
      cases h i pc _ hi
  · have hn : ¬ ((X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨
        (X.clc i).notified.Nonempty) := by
      intro hp
      obtain ⟨s, targets, pc, hi⟩ := hc.clc.2.2.1 i hp
      cases h i pc _ hi
    have hr : (X.clc i).resolved = none := by
      cases he : (X.clc i).resolved with
      | none => rfl
      | some r => exact (hn (.inl (by simp [he]))).elim
    have hw : (X.clc i).written = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (fun hp => hn (.inr (.inl hp)))
    have ht : (X.clc i).notified = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (fun hp => hn (.inr (.inr hp)))
    cases he : X.clc i
    simp_all
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rank hr
    obtain ⟨s, m, ⟨pc, hi⟩, _⟩ := (hc.tcCommit i rank hr).1
    cases h i pc _ hi

/-- A candidate non-async execution still must have no fabricated effects or histories. -/
def EmptyAsync (X : Execution) : Prop :=
  (∀ i, X.async.copies i = {} ∧ X.async.mmaStarted i = false ∧
    X.async.mmaDone i = false ∧ X.async.arrived i = false) ∧
  (∀ m, X.objects m = []) ∧
  ∀ i, X.tensor i = none ∧ X.tensorStores i = none ∧ X.clc i = {} ∧ X.tcNotified i = ∅

theorem emptyAsync {K : Kernel} {A : List Assumption}
    (hc : Consistent L K A mem0 X) : EmptyAsync X := by
  refine ⟨?_, h.objects_empty hc, h.other_empty hc⟩
  intro i
  have hn : ¬ AsyncCopy.nonempty (X.async.copies i) := by
    intro hp
    obtain ⟨s, hs, _⟩ := hc.tma.1 i hp
    unfold AsyncCopy.issuedBy at hs
    cases he : X.get i with
    | none => simp [he] at hs
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      have hh := h i pc kind he
      cases kind <;> simp_all [Kind.isTma]
  have hr : (X.async.copies i).readBytes = none := by
    cases he : (X.async.copies i).readBytes with
    | none => rfl
    | some bs => exact False.elim (hn ⟨.read .copy, by simp [AsyncCopy.present, he]⟩)
  have hw : (X.async.copies i).writeBytes = none := by
    cases he : (X.async.copies i).writeBytes with
    | none => rfl
    | some bs => exact False.elim (hn ⟨.write .copy, by simp [AsyncCopy.present, he]⟩)
  have hf : (X.async.copies i).notified = false :=
    Bool.eq_false_iff.mpr (fun h => hn ⟨.notify .copy, h⟩)
  have hew : (X.async.copies i).elemWrites = fun _ => none := by
    funext j
    cases hw : (X.async.copies i).elemWrites j with
    | none => rfl
    | some bs => exact absurd ⟨.write (.elem j), by simp [AsyncCopy.present, hw]⟩ hn
  have heo : (X.async.copies i).elemOld = fun _ => none := by
    funext j
    cases ho : (X.async.copies i).elemOld j with
    | none => rfl
    | some bs => exact absurd ⟨.old (.elem j), by simp [AsyncCopy.present, ho]⟩ hn
  have hs : X.async.mmaStarted i = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    rcases hc.tma.2.1.1 i hs with ⟨d, s, accum, mask, operands, ⟨pc, hm⟩, -⟩ |
      ⟨c, operands, ⟨pc, hm⟩, -⟩ | ⟨s, operands, ⟨pc, hm⟩, -⟩ <;> cases h i pc _ hm
  have hd : X.async.mmaDone i = false := by
    apply Bool.eq_false_iff.mpr
    intro hd
    have hh := hc.tma.2.1.2 i hd
    rw [hs] at hh
    cases hh
  have ha : X.async.arrived i = false := by
    apply Bool.eq_false_iff.mpr
    intro ha
    obtain ⟨⟨m, noinc, ⟨pc, hm⟩⟩, -⟩ := hc.tma.2.2.2 i ha
    cases h i pc _ hm
  refine ⟨?_, hs, hd, ha⟩
  have hc : X.async.copies i =
      ⟨(X.async.copies i).readBytes, (X.async.copies i).writeBytes,
        (X.async.copies i).notified, (X.async.copies i).elemWrites,
        (X.async.copies i).elemOld⟩ := rfl
  rw [hc, hr, hw, hf, hew, heo]

theorem tmaOk (he : EmptyAsync X) : TmaOk X := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    rw [(he.1 i).1] at hi
    obtain ⟨p, hp⟩ := hi
    cases p <;> cases hp
  · intro i hi; rw [(he.1 i).2.1] at hi; cases hi
  · intro i hi; rw [(he.1 i).2.2.1] at hi; cases hi
  · intro m
    rw [he.2.1 m]
    refine ⟨⟨by simp, none, .nil none⟩, ?_, ?_⟩
    · intro r hr; cases hr
    · intro id a ha
      rw [h.objectAction_none] at ha
      cases ha
  · intro i hi
    rw [(he.1 i).2.2.2] at hi
    cases hi

theorem not_tmaUnsafe (he : ∀ m, X.objects m = []) : ¬ TmaUnsafe L mem0 X := by
  rintro (⟨m, r, hr, -⟩ | ⟨m, r, hr, -⟩ | ⟨_, _, _, i, _, _, _, -, hi, -⟩ | hov | hmu)
  · rw [he m] at hr; cases hr
  · rw [he m] at hr; cases hr
  · exact h.not_mbInit hi
  · exact not_cpAsyncOverlap_of_none (fun e s hc _ => h.not_copy hc) hov
  · exact not_maskedRangeUnalloc_of_none (fun e s m hc _ => h.not_copy hc) hmu

theorem sourceSafe {A : List Assumption} : TcMma.SourceSafe L A X := h.noTc.sourceSafe

theorem countP_eq (g : Nat) : (X.tr g).countP Event.counts = (X.tr g).length := by
  rw [List.countP_eq_length]
  intro e he
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
  have hk := h (g, n) (X.tr g)[n].pc (X.tr g)[n].kind (by
    simp [Execution.get, List.getElem?_eq_getElem hn])
  generalize (X.tr g)[n] = ev at hk
  obtain ⟨pc, k⟩ := ev
  cases k <;> simp_all [Event.counts, Kind.isTma]

/-- In a consistent non-async execution, every counted item is a thread event. -/
theorem size_eq {K : Kernel} {A : List Assumption} (hc : Consistent L K A mem0 X) :
    X.size L = ((List.range L.threads).map fun g => (X.tr g).length).sum := by
  have he := h.emptyAsync hc
  have hz (g i : Nat) : X.asyncSize (g, i) = 0 := by
    obtain ⟨hc, hs, hd, ha⟩ := he.1 (g, i)
    obtain ⟨htn, hst, hcl, hmul⟩ := he.2.2 (g, i)
    have hes : X.elemSize (g, i) = 0 := by
      apply Execution.elemSize_eq_zero
      intro j
      rw [hc]
      simp
    simp [Execution.asyncSize, hes, hc, hs, hd, ha, htn, hst, hcl, hmul]
  have hp (cta : Nat) : X.tmemHistory cta = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro r hr
    cases h _ _ _ (((hc.tmemPair.1 cta).1 r hr).2.2.2.2.1 (0 : Fin 32))
  have hq : X.tmemPairing = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hqm
    cases h _ _ _ ((hc.tmemPair.2.1 q hqm).1.2.1.2.2.1 (0 : Fin 32))
  simp [Execution.size, Execution.threadSize, Execution.pairSize,
    hp, hq, hz, h.countP_eq]

end Execution.NoTma

end PTX

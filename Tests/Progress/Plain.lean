-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Progress.Common
public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Execution.NoAsync

@[expose] public section

/-!
# Progress tests: possible executions of plain loads and stores

`plain tr rf init` is the execution with thread traces `tr`, reads-from `rf`, initial content
`init` for the allocated bytes whose launch content is unspecified, and nothing else: no
asynchronous effects and empty object histories. When its events are weak or relaxed loads and
stores and exits (`PlainKinds`), every rule of `Consistent` except the thread traces, reads-from
and the two read axioms holds without further facts (`consistent_plain`), and base causality is
program order (`baseCausality_plain`), so the read axioms reduce to facts about one thread.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

/-- The execution with traces `tr`, reads-from `rf`, initial content `init` and no other
observation. -/
def plain (tr : Nat → List Event) (rf : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref)
    (init : Loc → Byte) : Execution where
  tr := tr
  rf := rf
  initial := init

/-- Every event is a load without `.acquire`, a store without `.release` or an exit. -/
def PlainKinds (X : Execution) : Prop :=
  ∀ e pc k, X.get e = some ⟨pc, k⟩ →
    (∃ a bs, k = .rd a bs ∧ a.acquire = false) ∨ (∃ a bs, k = .wr a bs ∧ a.release = false) ∨
      k = .exit

section
variable {L : Launch} {tr : Nat → List Event} {rf : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref}
  {init : Loc → Byte}

theorem PlainKinds.kind (h : PlainKinds (plain tr rf init)) {e : EvId} {pc : Nat} {k : Kind}
    (he : (plain tr rf init).get e = some ⟨pc, k⟩)
    (hr : ∀ a bs, k = .rd a bs → a.acquire = false → False)
    (hw : ∀ a bs, k = .wr a bs → a.release = false → False) (hx : k ≠ .exit) : False := by
  rcases h e pc k he with ⟨a, bs, rfl, ha⟩ | ⟨a, bs, rfl, ha⟩ | rfl
  · exact hr a bs rfl ha
  · exact hw a bs rfl ha
  · exact hx rfl

theorem PlainKinds.noTma (h : PlainKinds (plain tr rf init)) : (plain tr rf init).NoTma := by
  intro e pc k he
  rcases h e pc k he with ⟨a, bs, rfl, ha⟩ | ⟨a, bs, rfl, ha⟩ | rfl <;> simp [Kind.isTma, *]

/-- Base causality of a plain execution is program order: it stays in one thread and goes
forward. -/
theorem baseCausality_plain (h : PlainKinds (plain tr rf init)) {e f : EvId}
    (hb : baseCausality L (plain tr rf init) e f) : e.1 = f.1 ∧ e.2 < f.2 := by
  have hn := h.noTma
  have step : ∀ e f, (po (plain tr rf init) e f ∨ CtaBarSync L (plain tr rf init) e f ∨
      MSync L (plain tr rf init) e f ∨ ClusterSync L (plain tr rf init) e f ∨
      WarpBarSync L (plain tr rf init) e f ∨ synchronizesWith L (plain tr rf init) e f ∨
      FenceSync L (plain tr rf init) e f) → e.1 = f.1 ∧ e.2 < f.2 := by
    intro e f hs
    rcases hs with hp | hs | hs | hs | hs | hs | hs
    · exact ⟨hp.1, hp.2.1⟩
    · obtain ⟨-, key, i, j, hi, -⟩ := hs
      obtain ⟨idx, st, warp, count, lanes, g, hget, -⟩ := hi.2.2
      simp [plain] at hget
    · exact absurd hs hn.not_msync
    · obtain ⟨-, i, j, ⟨phase, ha, -⟩, -⟩ := hs
      simp [plain, ClusterBarrier.ArrivalOf] at ha
    · obtain ⟨i, j, ⟨-, mask, inst, ⟨pc, hw⟩, -⟩, -⟩ := hs
      exact (h.kind hw (by simp) (by simp) (by simp)).elim
    · obtain ⟨a, b, bs, cs, hw, -, hrel, -⟩ := hs
      rcases hw with ⟨pc, hw⟩ | ⟨o, pc, hw⟩
      · exact (h.kind hw (by simp) (by rintro a' bs' ⟨rfl, rfl⟩ h'; simp [h'] at hrel)
          (by simp)).elim
      · exact (h.kind hw (by simp) (by simp) (by simp)).elim
    · exact absurd hs (not_fenceSync_of_noFence (fun e sem s ⟨pc, hf⟩ =>
        h.kind hf (by simp) (by simp) (by simp)) e f)
  induction hb with
  | single hs => exact step _ _ hs
  | tail _ hs ih => exact ⟨ih.1.trans (step _ _ hs).1, ih.2.trans (step _ _ hs).2⟩

/-- A rank that every `Waits` edge of a plain execution increases: issue and return points of
the thread events in program order. -/
def rank : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * e.2 + if b then 1 else 0
  | (.async _ _, _) => 0

theorem PlainKinds.notAsync (_h : PlainKinds (plain tr rf init)) (i : EvId) (p : AsyncCopy.Part) :
    ¬ (plain tr rf init).AsyncPresent i p := by
  cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, plain]

theorem PlainKinds.free (h : PlainKinds (plain tr rf init)) {e : EvId} {ev : Event}
    (he : (plain tr rf init).get e = some ev) : ev.kind.resume = .free := by
  obtain ⟨pc, k⟩ := ev
  rcases h e pc k he with ⟨a, bs, rfl, -⟩ | ⟨a, bs, rfl, -⟩ | rfl <;> rfl

theorem PlainKinds.noNeeds (h : PlainKinds (plain tr rf init)) (e : EvId) :
    Needs L (plain tr rf init) e = [] := by
  unfold Needs
  cases he : (plain tr rf init).get e with
  | none => rfl
  | some ev => exact kindNeeds_free L _ _ _ (h.free he)

theorem PlainKinds.waits_rank (h : PlainKinds (plain tr rf init)) {a c : AsyncCopy.Ref × Bool}
    (hw : Waits L (plain tr rf init) a c) : rank a < rank c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases hw with ⟨rfl, rfl, rfl, hp⟩ | ⟨rfl, rfl, i, j, rfl, rfl, -, hj, -⟩ |
    ⟨i, j, rfl, rfl, -, -, hc⟩ |
    ⟨rfl, rfl, i, j, rfl, rfl, -, n, ⟨⟨pc, md, va, vb, vc, vr, vo, hev⟩, -⟩, -⟩ |
    ⟨rfl, rfl, i, j, rfl, rfl, -, k, ⟨⟨ev, hev, hs⟩, -⟩, -⟩ | ⟨rfl, rfl, hs⟩ |
    ⟨rfl, rfl, m, hm⟩ | ⟨i, j, rfl, rfl, -, -, hc⟩ | ⟨rfl, rfl, j, rfl, fills, hn, -⟩ |
    ⟨rfl, rfl, i, j, rfl, rfl, -, mask, inst, ⟨pc, hb⟩, -⟩ | ⟨rfl, rfl, i, j, rfl, rfl, hs⟩ |
    ⟨i, j, rfl, rfl, -, -, -, -, pc, inc, n, ei, fi, hr, -⟩ |
    ⟨rfl, rfl, i, j, rfl, rfl, cta, k, l, x, y, hx, -⟩ | ⟨rfl, rfl, i, j, rfl, rfl, hs⟩ |
    ⟨rfl, rfl, -, -, i, p, rfl, rfl, -, hp, -⟩
  · cases e with
    | thread e => simp [rank]
    | async i p => exact absurd hp (h.notAsync i p)
  · simp only [rank, ite_true]; omega
  · exfalso
    rcases hc with ⟨-, -, c, i, j, r, q, hr, -⟩ | ⟨-, -, -, key, ⟨-, ⟨cnt, pc, hb⟩, -⟩, -⟩ |
      ⟨-, -, key, i, r, -, hr, -⟩
    · simp [plain] at hr
    · obtain ⟨mode, hb⟩ := hb
      exact h.kind hb (by simp) (by simp) (by simp)
    · simp [plain] at hr
  · exact (h.kind hev (by simp) (by simp) (by simp)).elim
  · exfalso
    obtain ⟨pc, k⟩ := ev
    rcases h _ _ _ hev with ⟨a, bs, rfl, -⟩ | ⟨a, bs, rfl, -⟩ | rfl <;> simp [isTcColl] at hs
  · exfalso
    rcases hs with ⟨-, h1, -⟩ | ⟨-, -, hs⟩
    · cases h1
    · have hna := h.notAsync
      cases e <;> cases f <;> unfold StageEdge at hs <;> split at hs <;> simp_all
  · exfalso; simp [plain, MBarrier.Before] at hm
  · exfalso
    rcases hc with ⟨c, i, j, r, q, hr, -⟩ | ⟨-, -, c, r, hr, -⟩ |
      ⟨-, -, ph, c, ha, -⟩ | ⟨-, -, ph, c, ha, -⟩
    · simp [plain] at hr
    · simp [plain] at hr
    · simp [plain, ClusterBarrier.ArrivalOf] at ha
    · simp [plain, ClusterBarrier.ArrivalOf] at ha
  · exfalso
    rw [h.noNeeds] at hn
    simp at hn
  · exact (h.kind hb (by simp) (by simp) (by simp)).elim
  · exfalso
    obtain ⟨a, b, bs, cs, hw, -, hrel, -⟩ := hs
    rcases hw with ⟨pc, hw⟩ | ⟨o, pc, hw⟩
    · exact h.kind hw (by simp) (by rintro a' bs' ⟨rfl, rfl⟩ h'; simp [h'] at hrel) (by simp)
    · exact h.kind hw (by simp) (by simp) (by simp)
  · exact (h.kind hr (by simp) (by simp) (by simp)).elim
  · exfalso; simp [plain] at hx
  · exact absurd hs (not_fenceSync_of_noFence (fun e sem s ⟨pc, hf⟩ =>
      h.kind hf (by simp) (by simp) (by simp)) i j)
  · exact absurd hp (h.notAsync i p)

theorem plain_emptyAsync : Execution.NoTma.EmptyAsync (plain tr rf init) :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, (fun _ => rfl), fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

theorem modelCausality_plain (h : PlainKinds (plain tr rf init)) {l : Loc} {e f : EvId}
    (hm : modelCausality L (plain tr rf init) l (.thread e) (.thread f)) :
    e.1 = f.1 ∧ e.2 < f.2 := by
  rcases hm with hb | ha
  · exact baseCausality_plain h hb
  · obtain ⟨_, _, _, _, ha, _, _, _, _⟩ := ha
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hget, _, _, _⟩ := ha
    exact (h.kind hget (by simp) (by simp) (by simp)).elim

private theorem plain_no_mma (hk : PlainKinds (plain tr rf init))
    (i : EvId) (d : Nat) (s : TcMma.OperandSpec) (accum : Bool) (mask : List Nat) :
    ¬ (plain tr rf init).MmaIssue i d s accum mask := by
  rintro ⟨pc, h⟩
  exact hk.kind h (by simp) (by simp) (by simp)

private theorem plain_no_cp (hk : PlainKinds (plain tr rf init)) (i : EvId)
    (spec : TcCopy.Spec) : ¬ (plain tr rf init).CpIssue i spec := by
  rintro ⟨pc, h⟩
  exact hk.kind h (by simp) (by simp) (by simp)

private theorem byteCausality_plain (hk : PlainKinds (plain tr rf init)) {l : Loc} {e f : EvId}
    (hb : ByteCausality L (plain tr rf init) l (.thread e) (.thread f)) :
    e.1 = f.1 ∧ e.2 < f.2 :=
  modelCausality_plain hk
    ((ByteCausality.direct_iff_of_no_operand (plain_no_mma hk) (plain_no_cp hk)).1 hb)

/-- MEM-READ-AXIOMS, first clause: in a plain execution a read that reads only from writes of
other threads reads from no write it precedes. -/
theorem noFuture_plain (hk : PlainKinds (plain tr rf init))
    (hcross : ∀ i k w, rf (.thread i) k = some w → ∃ j, w = .thread j ∧ i.1 ≠ j.1) :
    NoFuture L (plain tr rf init) := by
  intro e a bs k w hr _ hw hc
  obtain ⟨i, rfl, -⟩ := Execution.NoTma.memReads_thread plain_emptyAsync hr
  obtain ⟨j, rfl, hne⟩ := hcross i k w hw
  exact hne (byteCausality_plain hk hc).1

/-- MEM-READ-AXIOMS, second clause: in a plain execution no read follows, in its own thread, a
store that covers a byte it reads. -/
theorem hidden_plain (hk : PlainKinds (plain tr rf init))
    (hsame : ∀ i j a bs a' bs', (plain tr rf init).Reads i a bs →
      (plain tr rf init).Writes j a' bs' → i.1 = j.1 → j.2 < i.2 →
      ∀ k < a.size, ¬ a'.Covers (a.loc.at k)) :
    Hidden L (plain tr rf init) := by
  intro e a bs k w a' bs' hr hk' hw hcov hc
  obtain ⟨i, rfl, hr | ⟨new, ⟨pc, hm⟩⟩⟩ := Execution.NoTma.memReads_thread plain_emptyAsync hr
  · obtain ⟨j, rfl, hw | ⟨old, ⟨pc, hm⟩⟩⟩ :=
      Execution.NoTma.memWrites_thread plain_emptyAsync hw
    · obtain ⟨h1, h2⟩ := byteCausality_plain hk hc
      exact absurd hcov (hsame i j a bs a' bs' hr hw h1.symm h2 k hk')
    · exact (hk.kind hm (by simp) (by simp) (by simp)).elim
  · exact (hk.kind hm (by simp) (by simp) (by simp)).elim

/-- A plain execution in which every launched thread ended with `exit` is complete. -/
theorem complete_plain (hk : PlainKinds (plain tr rf init))
    (hx : ∀ g < L.threads, ∃ pc, (tr g).getLast? = some ⟨pc, .exit⟩) :
    Complete L (plain tr rf init) :=
  hk.noTma.complete_of_exits L hx

/-- A plain execution is possible when its traces are runs of the kernel, its reads read what
`rf` names and the two read axioms hold; every other rule of `Consistent` holds because no event
synchronizes, waits or starts an asynchronous operation and every object history is empty. -/
theorem consistent_plain {K : Kernel} {mem0 : Mem0} (hk : PlainKinds (plain tr rf init))
    (hl : L.clusterGridValid) (thr : ∀ g < L.threads, Produces K [] L g (tr g))
    (outside : ∀ g, L.threads ≤ g → tr g = []) (hrf : RfWf mem0 (plain tr rf init))
    (noFuture : NoFuture L (plain tr rf init)) (hidden : Hidden L (plain tr rf init)) :
    Consistent L K [] mem0 (plain tr rf init) := by
  have hn := hk.noTma
  have he : Execution.NoTma.EmptyAsync (plain tr rf init) :=
    ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, (fun _ => rfl), fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  have ht := hn.tmaOk he
  have hna := hk.notAsync
  have acyc : ∀ {R : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop},
      (∀ a c, R a c → Relation.TransGen (Waits L (plain tr rf init)) a c) →
      ∀ n, ¬ Relation.TransGen R n n := by
    intro R hR n hc
    have hlt : ∀ {a c}, Relation.TransGen (Waits L (plain tr rf init)) a c → rank a < rank c := by
      intro a c hp
      induction hp with
      | single hw => exact hk.waits_rank hw
      | tail _ hw ih => exact ih.trans (hk.waits_rank hw)
    have hlt' : ∀ {a c}, Relation.TransGen R a c → rank a < rank c := by
      intro a c hp
      induction hp with
      | single hw => exact hlt (hR _ _ hw)
      | tail _ hw ih => exact ih.trans (hlt (hR _ _ hw))
    exact lt_irrefl _ (hlt' hc)
  have kd := @PlainKinds.kind tr rf init hk
  have noRmw := fun p l n => show ¬ (plain tr rf init).RmwAt p l n from by
    cases p with
    | thread e =>
      rintro ⟨a, old, new, ⟨pc, h⟩, -⟩
      exact kd h (by simp) (by simp) (by simp)
    | tensor i x y =>
      rintro ⟨fp, hred, -⟩
      obtain ⟨o, red, loc, ho, -⟩ := hred
      simp [plain] at ho
    | copy i j =>
      rintro ⟨s, r, a, hc, -⟩
      obtain ⟨pc, hc⟩ := hc
      exact kd hc (by simp) (by simp) (by simp)
  have noSc : ∀ e s, ¬ (plain tr rf init).ThreadFence e .sc s := fun e s ⟨pc, h⟩ =>
    kd h (by simp) (by simp) (by simp)
  have syncObject : ∀ {o : OrderObject} {a c : AsyncCopy.Ref × Bool},
      SyncObjectOrder L (plain tr rf init) o a c → ObjectOrder L (plain tr rf init) o a c := by
    intro o a c h
    cases o with
    | mbar m => exact h.1
    | ctaBar c id => exact h
    | cluster c => exact h
    | tmem cta => exact h
  refine {
    thr := thr
    outside := outside
    rf := hrf
    ctaBar := ⟨fun _ _ => rfl, fun c _ => ⟨by simp [plain], by simp [plain], ⟨{}, rfl⟩⟩⟩
    cluster := ⟨hl, fun _ _ => rfl, fun c _ => ⟨by simp [plain], by simp [plain], ⟨{}, rfl⟩⟩⟩
    dependency := {
      ready := fun e hret => by
        exfalso
        unfold Returned at hret
        cases he : (plain tr rf init).get e with
        | none => simp [he] at hret
        | some ev =>
          obtain ⟨pc, k⟩ := ev
          rcases hk e pc k he with ⟨a, bs, rfl, -⟩ | ⟨a, bs, rfl, -⟩ | rfl <;>
            simp [he, Kind.resume] at hret
      acyclic := fun o _ n => acyc (fun a c h => h.elim DepStep.waits
        (fun h => .single (ObjectOrder.waits h))) n }
    shfl := fun g i n pc m a b c recv ok h _ => (kd h (by simp) (by simp) (by simp)).elim
    vote := fun g i n pc mask a ballot h _ => (kd h (by simp) (by simp) (by simp)).elim
    warpValue := ⟨fun _ _ _ _ _ _ _ _ h _ => (kd h (by simp) (by simp) (by simp)).elim,
      fun _ _ _ _ _ _ _ _ _ h _ => (kd h (by simp) (by simp) (by simp)).elim,
      fun _ _ _ _ _ _ _ _ _ _ h _ => (kd h (by simp) (by simp) (by simp)).elim,
      fun _ _ _ _ h => (kd h (by simp) (by simp) (by simp)).elim⟩
    matrix := fun g i pc op own recv n h _ => (kd h (by simp) (by simp) (by simp)).elim
    elect := ?_
    warpBar := ?_
    observation := ?_
    object := fun o n => acyc (fun a c h => h.elim stageCausality.waits
      (fun h => .single (ObjectOrder.waits (syncObject h)))) n
    asyncObject := fun m i p y hb => by simp [MBarrier.Before, plain] at hb
    initFence := fun m init w y _ _ hb => by simp [MBarrier.Before, plain] at hb
    noFuture := noFuture
    hidden := hidden
    tma := ht
    clc := ?_
    tensor := by simp [TensorOk, plain]
    store := by simp [TensorStoreOk, plain]
    reduce := TensorStore.ReduceOk.of_none (fun _ _ h => by simp [plain] at h)
      (fun _ _ h => by obtain ⟨pc, hp⟩ := h; exact (kd hp (by simp) (by simp) (by simp)).elim)
    atomic := {
      unique := fun p q l n k hp => absurd hp (noRmw p l n)
      acyclic := by
        intro p path
        obtain ⟨q, edge, -⟩ := Relation.TransGen.head'_iff.mp path
        obtain ⟨l, n, hp, -⟩ := edge
        exact noRmw p l n hp }
    fenceSc := fenceScOk_of_noSc noSc
    tmemPair := by
      simp [Tmem.Pair.HistoriesOk, Tmem.Pair.RequestHistory, Tmem.Pair.runRequests, plain]
    tmemPairCompletion :=
      fun ws hws => by rcases hws with ⟨_, _, h, _⟩ | ⟨_, h, _⟩ <;> simp [plain] at h
    tmemPairResult := hn.noTc.pairResult
    tcCommit := by simp [AsyncCopy.CommitOk, plain]
    mmaCompletion := ?_
    tcRead := ?_
    asm := by simp }
  · refine ⟨fun e pc mask inst leader h => ?_, fun e f _ _ _ _ _ _ _ h => ?_,
      fun e f _ _ _ _ _ _ _ h => ?_⟩ <;>
      exact (kd (show (plain tr rf init).get e = _ from h) (by simp) (by simp) (by simp)).elim
  · refine ⟨fun e mask inst ⟨pc, h⟩ => ?_, fun e f mask mask' inst ⟨pc, h⟩ => ?_⟩ <;>
      exact (kd h (by simp) (by simp) (by simp)).elim
  · intro x w ho
    rcases ho with ⟨-, j, m, pc, q, ws, us, g, -, hj, -⟩ | ⟨i, p, j, k, -, -, hp, -⟩
    · exact (kd hj (by simp) (by simp) (by simp)).elim
    · exact (hna i p hp).elim
  · refine ⟨Relation.ReflTransGen.refl, by simp [plain, Clc.initial], by simp [plain],
      fun i s t ⟨pc, h⟩ => (kd h (by simp) (by simp) (by simp)).elim,
      fun ⟨i, s, t, pc, h⟩ => (kd h (by simp) (by simp) (by simp)).elim⟩
  · intro i j _ hd
    simp [plain] at hd
  · exact ⟨fun _ _ _ _ _ _ _ _ h => absurd h hn.noTc.not_tld,
      fun _ _ _ _ _ _ _ ⟨_, _, _, _, h, _⟩ => absurd h hn.noTc.not_mma_issue⟩

end

end

end PTX.Tests.Progress

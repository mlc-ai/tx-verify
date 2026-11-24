-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RankCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderArrivals
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Lemmas.Flow.Final
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTileDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitDefs

@[expose] public section

/-! # The loader's counts along its run

A loader (warp 11, elected lane) runs its tasks one after another: sixteen trips of eight K
blocks, then the CLC response poll, read, query and acknowledgement. Along its run it keeps one
invariant, `Counts`: its successful empty polls go round the four slots (`rank`) and fix its
site (`cond`); its response polls and reads (`resp`, `rel`); the arrivals and tensor issues on
each full slot are covered by its empty polls (`arrive`, `issue`); and its polls keep the parity
of its successful polls (`parity`). `run` proves `Counts` by `Code.run_inv`, one step per site. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Loader

/-- Whether a loader site runs an object instruction: a poll, an arrival or a tensor copy. -/
def Site.obj : Site → Bool
  | .wait _ | .load _ _ | .arrive _ | .clcWait | .drain _ | .ack => true
  | _ => false

/-- A loader site that runs no object instruction runs an instruction that uses no object. -/
theorem code_objectOp (s : Site) (hs : s.obj = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : objectOp ins.op = false := by
  cases s with
  | wait _ => simp [Site.obj] at hs
  | load _ _ => simp [Site.obj] at hs
  | arrive _ => simp [Site.obj] at hs
  | clcWait => simp [Site.obj] at hs
  | clcLoad => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_0); rfl
  | clcStatus => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_0); rfl
  | clcFirst => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_1); rfl
  | clcFence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1); rfl
  | ack => simp [Site.obj] at hs
  | drain _ => simp [Site.obj] at hs
  | exitArrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1); rfl
  | exitWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1); rfl
  | exit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0); rfl

end Loader

/-- A loader state that has left its task loop: it drains, or it leaves through the common exit. -/
def Loader.Site.leaving : Loader.Site → Bool
  | .drain _ | .exitArrive | .exitWait | .exit => true
  | _ => false

/-- The task loop's sites: a block's poll, loads and arrival. -/
def Loader.Site.inTask : Loader.Site → Bool
  | .wait _ | .load _ _ | .arrive _ => true
  | _ => false

namespace LoaderTasks

/-- The loader's latest successful response poll is followed by a read of the response `rr`. -/
def HeldRdL (L : Launch) (g : Nat) (es : List Event) (rr : ClcResponse) : Prop :=
  ∃ j pc p acq sc pcr a bs, es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
    es[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧ a.loc = respLoc L g ∧ a.size = 16 ∧
    Flow.responseOf bs = some rr ∧ okPolls (clcResp L g) (es.take j) + 1 = okPolls (clcResp L g) es

/-- The first CTA a response names, as the loader's `x` register holds it. -/
def firstOfL (rr : ClcResponse) : Nat := (rr.firstCta.map fun c => c.1.toNat).getD Loader.none32

theorem firstOfL_of_not {rr : ClcResponse} (h : ¬ rr.firstCta.isSome = true) :
    firstOfL rr = Loader.none32 := by
  unfold firstOfL
  cases hc : rr.firstCta with
  | none => rfl
  | some c => simp [hc] at h

theorem HeldRdL.snoc {L : Launch} {g : Nat} {es : List Event} {rr : ClcResponse} {e : Event}
    (h : HeldRdL L g es rr) (he : okPoll (clcResp L g) e = false) :
    HeldRdL L g (es ++ [e]) rr := by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, ha, hs, hr, hc⟩ := h
  have hlt : j + 1 < es.length := (List.getElem?_eq_some_iff.mp h2).1
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, ?_, ?_, ha, hs, hr, ?_⟩
  · rw [List.getElem?_append_left (by omega)]; exact h1
  · rw [List.getElem?_append_left hlt]; exact h2
  · rw [List.take_append_of_le_length (by omega), okPolls_snoc, he, Nat.add_zero]; exact hc

theorem HeldRdL.of_read {L : Launch} {g : Nat} {es : List Event} {rr : ClcResponse} {pe e : Event}
    {p : Nat} {acq : Bool} {sc : MbarScope} {a : Acc} {bs : List (Option Byte)}
    (hl : es.getLast? = some pe) (hpe : pe.kind = .wait (clcResp L g) p true acq sc)
    (hk : e.kind = .rd a bs) (ha : a.loc = respLoc L g) (hs : a.size = 16)
    (hr : Flow.responseOf bs = some rr) : HeldRdL L g (es ++ [e]) rr := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  obtain ⟨pc, k⟩ := pe
  obtain ⟨epc, ek⟩ := e
  simp only at hpe hk
  subst hpe hk
  refine ⟨ys.length, pc, p, acq, sc, epc, a, bs, ?_, ?_, ha, hs, hr, ?_⟩
  · simp
  · simp
  · rw [List.take_append_of_le_length (by simp), List.take_left' rfl]
    simp [Flow.okPolls, List.countP_append, okPoll, sourceWaitSuccess]

/-- The loader's site against its successful empty polls `N` and its successful response polls
`R` (so far): at a wait `R = N / 128`; after a block's poll `R = (N - 1) / 128`; at the response
poll `R + 1 = N / 128`; in the rest of the task and in the drain `R = N / 128`. -/
def CountOK (d : Loader.D) (N R : Nat) : Prop :=
  match d.site with
  | .wait _ => R = N / 128
  | .load _ _ | .arrive _ => R = (N - 1) / 128
  | .clcWait => R + 1 = N / 128
  | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack | .drain _ => R = N / 128
  | .exitArrive | .exitWait | .exit => (0 < R ∧ N = 128 * R + 4) ∨ (N = 0 ∧ R = 0)

/-- The loader is still in its task loop: it has not decided to drain or to leave. -/
def Live (d : Loader.D) : Prop :=
  match d.site with
  | .drain _ | .exitArrive | .exitWait | .exit => False
  | .clcStatus | .clcFirst => ∀ rr, d.resp = .clc rr → Loader.claims rr
  | .clcFence | .ack => d.x ≠ Loader.none32
  | _ => True

/-- The event at index `i` reads, from the response buffer, a response that claims a CTA. -/
def ReadOk (L : Launch) (g : Nat) (es : List Event) (i : Nat) : Prop :=
  ∃ pcr, ∃ src : Acc, ∃ bs rr, es[i]? = some ⟨pcr, .rd src bs⟩ ∧ src.loc = respLoc L g ∧
    src.size = 16 ∧ Flow.responseOf bs = some rr ∧ Loader.claims rr

/-- Along the loader's run from `d`: a live loader's response poll is followed by a `ReadOk` read,
and a last response poll leaves the loader at its read. -/
def Rel (L : Launch) (g : Nat) (d : Loader.D) (es : List Event) : Prop :=
  (∀ j pc p acq sc, j + 1 < es.length → es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
    Live d → ReadOk L g es (j + 1)) ∧
  (∀ pc p acq sc, es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ → d.site = .clcLoad)

variable {L : Launch} {g : Nat}

theorem clcResp_ne_empty (s : Fin 4) : clcResp L g ≠ Loader.emptyOf L g s := by
  intro h
  have h' := congrArg Loc.addr h
  simp only [clcResp, Loader.emptyOf, InputRing.emptyLoc, Bar.loc, Bar.off] at h'
  have := s.isLt
  omega

theorem okPoll_clc_empty {pc p : Nat} {ok acq : Bool} {sc : MbarScope} {s : Fin 4} {e : Event}
    (he : e = ⟨pc, .wait (Loader.emptyOf L g s) p ok acq sc⟩) :
    okPoll (clcResp L g) e = false := by
  rw [okPoll_wait he, decide_eq_false (fun h => clcResp_ne_empty s h.symm)]
  simp

theorem okPoll_clc_lit {pc p : Nat} {ok acq : Bool} {sc : MbarScope} {e : Event}
    (he : e = ⟨pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩) :
    okPoll (clcResp L g) e = ok := by
  have h : (⟨.shared, g / L.block, L.sharedBase + 104⟩ : Loc) = clcResp L g := rfl
  rw [okPoll_wait he, h]
  simp

theorem okPoll_empty_lit {pc p : Nat} {ok acq : Bool} {sc : MbarScope} {s : Fin 4} {e : Event}
    (he : e = ⟨pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩) :
    okPoll (Loader.emptyOf L g s) e = false := by
  have hne : (⟨.shared, g / L.block, L.sharedBase + 104⟩ : Loc) ≠ Loader.emptyOf L g s :=
    clcResp_ne_empty s
  rw [okPoll_wait he, decide_eq_false hne]
  simp

/-- A successful response poll that is not the latest one is followed by a read of a response that
claims a CTA. -/
def ClaimsBefore (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∀ j pc p acq sc, es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
    okPolls (clcResp L g) (es.take j) + 1 < okPolls (clcResp L g) es → ReadOk L g es (j + 1)

theorem ReadOk.snoc {es : List Event} {i : Nat} (e : Event) (h : ReadOk L g es i) :
    ReadOk L g (es ++ [e]) i := by
  obtain ⟨pcr, src, bs, rr, h1, h2, h3, h4, h5⟩ := h
  refine ⟨pcr, src, bs, rr, ?_, h2, h3, h4, h5⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]
  exact h1

/-- Appending an event that is no successful response poll keeps the claimed reads. -/
theorem ClaimsBefore.snoc_no {es : List Event} {e : Event} (h : ClaimsBefore L g es)
    (hn : okPoll (clcResp L g) e = false) : ClaimsBefore L g (es ++ [e]) := by
  intro j pc p acq sc hj hcount
  have hok : okPolls (clcResp L g) (es ++ [e]) = okPolls (clcResp L g) es := okPolls_snoc_zero hn
  have hjlt : j < es.length := by
    by_contra hge
    have hlen : j < (es ++ [e]).length := (List.getElem?_eq_some_iff.mp hj).1
    have hjeq : j = es.length := by simp at hlen; omega
    subst hjeq
    rw [List.getElem?_concat_length] at hj
    have he2 := Option.some.inj hj
    rw [he2] at hn
    simp [okPoll, sourceWaitSuccess] at hn
  rw [List.take_append_of_le_length hjlt.le, hok] at hcount
  rw [List.getElem?_append_left hjlt] at hj
  exact (h j pc p acq sc hj hcount).snoc e

/-- A trace with no successful response poll has the property. -/
theorem ClaimsBefore.of_zero {es : List Event} (h : okPolls (clcResp L g) es = 0) :
    ClaimsBefore L g es := fun _ _ _ _ _ _ hc => absurd hc (by omega)

/-- A successful response poll at the loader's CLC poll site: its earlier polls' reads claim a CTA,
since the task loop is live there. -/
theorem ClaimsBefore.snoc_poll {d : Loader.D} {es : List Event} (hr : Rel L g d es)
    (hd : Live d) (hs : d.site ≠ .clcLoad) (h : ClaimsBefore L g es) (e : Event)
    (hok : okPoll (clcResp L g) e = true) : ClaimsBefore L g (es ++ [e]) := by
  intro j pc p acq sc hj hcount
  have hokS : okPolls (clcResp L g) (es ++ [e]) = okPolls (clcResp L g) es + 1 := by
    rw [okPolls_snoc, hok]; simp
  have hlen : j < (es ++ [e]).length := (List.getElem?_eq_some_iff.mp hj).1
  have hjlt : j < es.length := by
    by_contra hge
    have hjeq : j = es.length := by simp at hlen; omega
    subst hjeq
    rw [List.take_append_of_le_length le_rfl, List.take_length, hokS] at hcount
    omega
  rw [List.getElem?_append_left hjlt] at hj
  rw [List.take_append_of_le_length hjlt.le, hokS] at hcount
  rcases Nat.lt_or_ge (okPolls (clcResp L g) (es.take j) +
    1) (okPolls (clcResp L g) es) with hlt | hge
  · exact (h j pc p acq sc hj hlt).snoc e
  · have hj1 : j + 1 < es.length := by
      by_contra hcon
      have hlast : es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := by
        rw [List.getLast?_eq_getElem?, show es.length - 1 = j by omega]
        exact hj
      exact hs (hr.2 pc p acq sc hlast)
    exact (hr.1 j pc p acq sc hj1 hj hd).snoc e

theorem lcount_snoc_zero {pre : List Event} {e : Event}
    (h : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false) :
    lcount L g (pre ++ [e]) = lcount L g pre := by
  unfold lcount
  exact Finset.sum_congr rfl fun s _ => okPolls_snoc_zero (h s)

/-- The response relation grows by one event: a new successful response poll leads to a read. -/
theorem Rel.step {d d' : Loader.D} {pre : List Event} {e : Event} (h : Rel L g d pre)
    (hW : ∀ pc p acq sc, e = ⟨pc, .wait (clcResp L g) p true acq sc⟩ → d'.site = .clcLoad)
    (hnew : ∀ pc p acq sc, pre.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      Live d' → ReadOk L g (pre ++ [e]) pre.length)
    (hlive : Live d' → Live d) : Rel L g d' (pre ++ [e]) := by
  refine ⟨fun j pc p acq sc hj hw hL => ?_, fun pc p acq sc hl => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge (j + 1) pre.length with hlt | hge
    · have hj0 : j < pre.length := by omega
      rw [List.getElem?_append_left hj0] at hw
      obtain ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩ :=
        h.1 j pc p acq sc hlt hw (hlive hL)
      exact ⟨pcr, src, bs, rr, by rw [List.getElem?_append_left hlt]; exact hr, h1, h2, h3, h4⟩
    · have hj' : j + 1 = pre.length := by omega
      have hj0 : j < pre.length := by omega
      rw [List.getElem?_append_left hj0] at hw
      rw [hj']
      refine hnew pc p acq sc ?_ hL
      rw [List.getLast?_eq_getElem?, show pre.length - 1 = j by omega]
      exact hw
  · rw [List.getLast?_concat, Option.some.injEq] at hl
    exact hW pc p acq sc hl

/-- A step that is no successful response poll keeps the response relation. -/
theorem Rel.of_notPoll {d d' : Loader.D} {pre : List Event} {e : Event} (h : Rel L g d pre)
    (hk : okPoll (clcResp L g) e = false) (hsite : d.site ≠ .clcLoad)
    (hlive : Live d' → Live d) : Rel L g d' (pre ++ [e]) :=
  Rel.step h (fun pc p acq sc he => by rw [he] at hk; simp [okPoll, sourceWaitSuccess] at hk)
    (fun pc p acq sc hl _ => absurd (h.2 pc p acq sc hl) hsite) hlive

/-- With no successful response poll at all, the response relation holds for any site. -/
theorem rel_of_zero {d : Loader.D} {es : List Event} (h : okPolls (clcResp L g) es = 0) :
    Rel L g d es := by
  refine ⟨fun j pc p acq sc _ hj _ => ?_, fun pc p acq sc hl => ?_⟩
  · have : 0 < okPolls (clcResp L g) es :=
      List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hj, by simp [okPoll, sourceWaitSuccess]⟩
    omega
  · have : 0 < okPolls (clcResp L g) es :=
      List.countP_pos_iff.mpr ⟨_, List.mem_of_getLast? hl, by simp [okPoll, sourceWaitSuccess]⟩
    omega

/-- The loader's trace has no undefined behaviour: no event of it is `ub`. -/
def NoUb (es : List Event) : Prop := ∀ e ∈ es, ∀ f, e.kind ≠ .ub f

theorem NoUb.of_snoc {es : List Event} {e : Event} (h : NoUb (es ++ [e])) : NoUb es :=
  fun x hx f => h x (List.mem_append.mpr (Or.inl hx)) f

theorem NoUb.last {es : List Event} {e : Event} (h : NoUb (es ++ [e])) :
    ∀ f, e.kind ≠ .ub f :=
  fun f => h e (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) f

/-- The loader's counts along its run, at the loader state `l` after the events `es`. -/
structure Counts (L : Launch) (g : Nat) (l : Loader.D) (es : List Event) : Prop where
  rank : ∀ s : Fin 4, okPolls (Loader.emptyOf L g s) es = (lcount L g es + 3 - s.val) / 4
  cond : LoaderCond l (lcount L g es)
  q8 : l.q % 8 = 0
  resp : CountOK l (lcount L g es) (okPolls (clcResp L g) es)
  rel : Rel L g l es
  arrive : ∀ s : Fin 4, arrivals (Loader.fullOf L g s) es +
    (if Loader.pending l s then 1 else 0) ≤ okPolls (Loader.emptyOf L g s) es
  issue : ∀ s : Fin 4, es.countP (issuesTo (Loader.fullOf L g s)) + Loader.remaining l s ≤
    3 * okPolls (Loader.emptyOf L g s) es
  parity : l.site.done = false → ∀ s : Fin 4,
    okPolls (Loader.emptyOf L g s) es % 2 = Loader.polled l s % 2
  /-- Along a trace without undefined behaviour, the counts are exact outside the drain's exit stage
  (`done` false). On each slot, the tensor issues and the loads still to issue there, with the
  drain's polls, are three times the successful empty polls. The leader's arrivals and pending
  batch, with the drain's polls, are the successful polls. -/
  exact : l.site.done = false → NoUb es →
    (∀ s : Fin 4, es.countP (issuesTo (Loader.fullOf L g s)) + Loader.remaining l s +
      3 * Loader.drained l s = 3 * okPolls (Loader.emptyOf L g s) es) ∧
    (Loader.leader L g = true → ∀ s : Fin 4, arrivals (Loader.fullOf L g s) es +
      (if Loader.pending l s then 1 else 0) + Loader.drained l s =
        okPolls (Loader.emptyOf L g s) es)
  /-- At the exit stage, reached through the drain's last poll: with no undefined behaviour and at
  least one successful response poll (`0 < lcount`), the counts are exact with the drain's polls on
  every slot. The tensor issues plus three are three times the successful empty polls, and the
  leader's arrivals plus one are its successful polls. An idle lane has no poll and the gate
  excludes it. -/
  exitExact : l.site.done = true → 0 < lcount L g es → NoUb es →
    (∀ s : Fin 4, es.countP (issuesTo (Loader.fullOf L g s)) + 3 =
      3 * okPolls (Loader.emptyOf L g s) es) ∧
    (Loader.leader L g = true → ∀ s : Fin 4, arrivals (Loader.fullOf L g s) es + 1 =
      okPolls (Loader.emptyOf L g s) es)
  /-- At the exit stage with at least one successful empty poll, the empty polls are the response
  polls' 128 blocks per task plus the drain's four polls. -/
  exitTasks : l.site.done = true → 0 < lcount L g es →
    lcount L g es = 128 * okPolls (clcResp L g) es + 4
  /-- After a successful response poll, unless at its read, the loader holds the response of the
  latest poll: the response is its `resp`, and the latest read. -/
  heldR : l.site ≠ .clcLoad → 0 < okPolls (clcResp L g) es → ∃ rr, HeldRdL L g es rr ∧ l.resp =
    .clc rr
  /-- At the fence, the acknowledgement, the drain and the exit, its `x` is the held response's
  first CTA. -/
  heldX : (l.site = .clcFence ∨ l.site = .ack ∨ l.site.leaving = true) → 0 <
    okPolls (clcResp L g) es →
    ∃ rr, HeldRdL L g es rr ∧ l.x = firstOfL rr
  /-- Once the loader has left its task loop after a response, its `x` is none. -/
  leaveX : l.site.leaving = true → 0 < okPolls (clcResp L g) es → l.x = Loader.none32
  /-- At its read the loader has polled the response last. -/
  polledL : l.site = .clcLoad → ∃ e' p acq sc, es.getLast? = some e' ∧
    e'.kind = .wait (clcResp L g) p true acq sc
  /-- A successful response poll that is not the latest is followed by a read of a response that
  claims a CTA. -/
  claimsBefore : ClaimsBefore L g es

/-- Along a thread's run: the prologue is quiet, and a loader state is `Counts`. -/
def Along (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Quiet es
  | .inr (.loader l), es => Counts L g l es
  | _, _ => True

/-- The loader's first states after the prologue move no count. -/
theorem start {es : List Event} (hq : Quiet es) (l : Loader.D)
    (hl : l = Prologue.loaderStart L g ∨ l = Prologue.loaderIdle) : Counts L g l es := by
  have h0 : ∀ m, okPolls m es = 0 := fun m => (hq m).1
  have hL0 : lcount L g es = 0 := by unfold lcount; simp [h0]
  have hA : ∀ s : Fin 4, arrivals (Loader.fullOf L g s) es = 0 := fun s => (hq _).2.1
  have hI : ∀ s : Fin 4, es.countP (issuesTo (Loader.fullOf L g s)) = 0 :=
    fun s => (hq _).2.2.2.1
  rcases hl with rfl | rfl
  · exact ⟨fun s => by rw [h0, hL0]; have := s.isLt; omega,
      by simp [LoaderCond, Prologue.loaderStart, hL0], by simp [Prologue.loaderStart],
      by simp [CountOK, Prologue.loaderStart, hL0, h0], rel_of_zero (h0 _),
      fun s => by simp [Loader.pending, Prologue.loaderStart, hA s, h0],
      fun s => by simp [Loader.remaining, Prologue.loaderStart, hI s],
      fun _ s => by simp [Loader.polled, Prologue.loaderStart, h0],
      fun _ _ => ⟨fun s => by simp [Loader.remaining, Loader.drained, Prologue.loaderStart, hI s,
        h0],
        fun _ s => by simp [Loader.pending, Loader.drained, Prologue.loaderStart, hA s, h0]⟩,
      fun hd _ _ => by simp [Prologue.loaderStart, Loader.Site.done] at hd,
      fun hd _ => by simp [Prologue.loaderStart, Loader.Site.done] at hd,
      fun _ h => absurd h (by have := h0 (clcResp L g); omega),
      fun _ h => absurd h (by have := h0 (clcResp L g); omega),
      fun h _ => by simp [Prologue.loaderStart, Loader.Site.leaving] at h,
      fun h => by simp [Prologue.loaderStart] at h, ClaimsBefore.of_zero (h0 _)⟩
  · exact ⟨fun s => by rw [h0, hL0]; have := s.isLt; omega,
      by simp [LoaderCond, Prologue.loaderIdle], by simp [Prologue.loaderIdle],
      by simp [CountOK, Prologue.loaderIdle, hL0, h0], rel_of_zero (h0 _),
      fun s => by simp [Loader.pending, Prologue.loaderIdle, hA s, h0],
      fun s => by simp [Loader.remaining, Prologue.loaderIdle, hI s],
      fun h => by simp [Prologue.loaderIdle, Loader.Site.done] at h,
      fun h _ => by simp [Prologue.loaderIdle, Loader.Site.done] at h,
      fun _ hpos _ => by omega,
      fun _ hpos => by omega,
      fun _ h => absurd h (by have := h0 (clcResp L g); omega),
      fun _ h => absurd h (by have := h0 (clcResp L g); omega),
      fun _ h => absurd h (by have := h0 (clcResp L g); omega),
      fun h => by simp [Prologue.loaderIdle] at h, ClaimsBefore.of_zero (h0 _)⟩

/-- An exit-stage loader has no remaining tensor copies. -/
theorem remaining_of_done {l : Loader.D} (h : l.site.done = true) (s : Fin 4) :
    Loader.remaining l s = 0 := by
  unfold Loader.remaining
  split <;> simp_all [Loader.Site.done]

/-- An exit-stage loader has no pending batch. -/
theorem pending_of_done {l : Loader.D} (h : l.site.done = true) (s : Fin 4) :
    Loader.pending l s = false := by
  unfold Loader.pending
  split <;> simp_all [Loader.Site.done]

/-- A step that moves no successful poll keeps `Counts` when its arrivals and tensor issues move as
the pending batch and the remaining copies say. Its exact deltas (`hissEq`, `harrEq`) say the same
on a trace without undefined behaviour, and the drain's polls move by nothing (`hdr`). -/
theorem zero_step {l l' : Loader.D} {pre : List Event} {e : Event} (hc : Counts L g l pre)
    (h1 : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false)
    (h4 : okPoll (clcResp L g) e = false)
    (hq8' : l'.q % 8 = 0)
    (harr : ∀ s : Fin 4, (if arrivesOn (Loader.fullOf L g s) e then 1 else 0) +
      (if Loader.pending l' s then 1 else 0) ≤ if Loader.pending l s then 1 else 0)
    (hiss : ∀ s : Fin 4, (if issuesTo (Loader.fullOf L g s) e then 1 else 0) +
      Loader.remaining l' s ≤ Loader.remaining l s)
    (hissEq : NoUb (pre ++ [e]) → ∀ s : Fin 4,
      (if issuesTo (Loader.fullOf L g s) e then 1 else 0) + Loader.remaining l' s =
        Loader.remaining l s)
    (harrEq : Loader.leader L g = true → ∀ s : Fin 4,
      (if arrivesOn (Loader.fullOf L g s) e then 1 else 0) +
        (if Loader.pending l' s then 1 else 0) =
        if Loader.pending l s then 1 else 0)
    (hdr : ∀ s : Fin 4, Loader.drained l' s = Loader.drained l s := by
      intro s; simp [Loader.drained])
    (hs : l.site ≠ .clcLoad := by simp)
    (hlive : Live l' → Live l := by intro h; simp [Live] at h ⊢)
    (hcond : LoaderCond l' (lcount L g pre) := by simp only [LoaderCond]; omega)
    (hresp : CountOK l' (lcount L g pre) (okPolls (clcResp L g) pre) := by
      simp only [CountOK]; omega)
    (hpar : l'.site.done = false → l.site.done = false ∧
      ∀ s : Fin 4, Loader.polled l' s % 2 = Loader.polled l s % 2 := by
      intro hd; refine ⟨hd, fun s => ?_⟩; have := s.isLt; simp only [Loader.polled] <;>
        split_ifs <;>
        omega)
    (hdone : l'.site.done = true → l.site.done = true := by
      intro h; simp [Loader.Site.done] at h)
    (hresEq : l'.resp = l.resp := by rfl)
    (hheldX : 0 < okPolls (clcResp L g) pre →
      (l'.site = .clcFence ∨ l'.site = .ack ∨ l'.site.leaving = true) →
      ∃ rr, HeldRdL L g pre rr ∧ l'.x = firstOfL rr := by
      intro _ hl
      exact absurd hl (by simp [Loader.Site.leaving]))
    (hlvx : l'.site.leaving = true → 0 < okPolls (clcResp L g) pre → l'.x = Loader.none32 := by
      intro h _
      exact absurd h (by simp [Loader.Site.leaving]))
    (hpl : l'.site ≠ .clcLoad := by simp) :
    Counts L g l' (pre ++ [e]) := by
  have hN : lcount L g (pre ++ [e]) = lcount L g pre := lcount_snoc_zero h1
  refine ⟨fun s => ?_, ?_, hq8', ?_, Rel.of_notPoll hc.rel h4 hs hlive, fun s => ?_,
    fun s => ?_, fun hd s => ?_, fun hd hnu => ?_, fun hd hpos hnu => ?_, fun hd hpos => ?_,
    fun hl hR' => ?_, fun hl hR' => ?_, fun h hR' => ?_, fun hl => ?_, hc.claimsBefore.snoc_no h4⟩
  · rw [hN, okPolls_snoc_zero (h1 s), hc.rank s]
  · rw [hN]; exact hcond
  · rw [hN, okPolls_snoc_zero h4]; exact hresp
  · rw [arrivals_snoc, okPolls_snoc_zero (h1 s)]
    have := hc.arrive s
    have := harr s
    omega
  · rw [issues_snoc, okPolls_snoc_zero (h1 s)]
    have := hc.issue s
    have := hiss s
    omega
  · obtain ⟨hd0, hp⟩ := hpar hd
    rw [okPolls_snoc_zero (h1 s), hc.parity hd0 s, hp s]
  · obtain ⟨hd0, -⟩ := hpar hd
    obtain ⟨c1, c2⟩ := hc.exact hd0 (NoUb.of_snoc hnu)
    refine ⟨fun s => ?_, fun hL s => ?_⟩
    · have := c1 s
      have := hissEq hnu s
      have := hdr s
      rw [issues_snoc, okPolls_snoc_zero (h1 s)]
      omega
    · have := c2 hL s
      have := harrEq hL s
      have := hdr s
      rw [arrivals_snoc, okPolls_snoc_zero (h1 s)]
      omega
  · have hl1 : l.site.done = true := hdone hd
    have hpos' : 0 < lcount L g pre := by rw [hN] at hpos; exact hpos
    obtain ⟨c1, c2⟩ := hc.exitExact hl1 hpos' (NoUb.of_snoc hnu)
    refine ⟨fun s => ?_, fun hL s => ?_⟩
    · have c1s := c1 s
      have h2 := hiss s
      have h3 := remaining_of_done hd s
      have h4 := remaining_of_done hl1 s
      rw [issues_snoc, okPolls_snoc_zero (h1 s)]
      omega
    · have c2s := c2 hL s
      have h2 := harr s
      have h5 : (if Loader.pending l' s then 1 else 0) = 0 := by simp [pending_of_done hd s]
      have h6 : (if Loader.pending l s then 1 else 0) = 0 := by simp [pending_of_done hl1 s]
      rw [arrivals_snoc, okPolls_snoc_zero (h1 s)]
      omega
  · have hl1 : l.site.done = true := hdone hd
    have hpos' : 0 < lcount L g pre := by rw [hN] at hpos; exact hpos
    rw [hN, okPolls_snoc_zero h4]
    exact hc.exitTasks hl1 hpos'
  · rw [okPolls_snoc_zero h4] at hR'
    obtain ⟨rr, hrr, hres⟩ := hc.heldR hs hR'
    exact ⟨rr, hrr.snoc h4, by rw [hresEq]; exact hres⟩
  · rw [okPolls_snoc_zero h4] at hR'
    obtain ⟨rr, hrr, hx⟩ := hheldX hR' hl
    exact ⟨rr, hrr.snoc h4, hx⟩
  · rw [okPolls_snoc_zero h4] at hR'
    exact hlvx h hR'
  · exact absurd hl hpl

/-- A step at a site that runs no object instruction moves no count. -/
theorem free_step {l l' : Loader.D} {pre : List Event} {e : Event} {t : TState} {ins : Instr}
    {o : Option TState} (hc : Counts L g l pre) (hs : l.site.obj = false)
    (hl : l.site ≠ .clcLoad) (hcode : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o) (hlive : Live l' → Live l)
    (hq8' : l'.q % 8 = 0) (hcond : LoaderCond l' (lcount L g pre))
    (hresp : CountOK l' (lcount L g pre) (okPolls (clcResp L g) pre))
    (hpend : ∀ s : Fin 4, Loader.pending l' s = false)
    (hrem : ∀ s : Fin 4, Loader.remaining l' s = 0) (hrem0 : ∀ s : Fin 4, Loader.remaining l s = 0)
    (hpar : l'.site.done = false → l.site.done = false ∧
      ∀ s : Fin 4, Loader.polled l' s % 2 = Loader.polled l s % 2)
    (hpend0 : ∀ s : Fin 4, Loader.pending l s = false := by intro s; rfl)
    (hdr : ∀ s : Fin 4, Loader.drained l' s = Loader.drained l s := by
      intro s; simp [Loader.drained])
    (hdone : l'.site.done = true → l.site.done = true := by
      intro h; simp [Loader.Site.done] at h)
    (hresEq : l'.resp = l.resp := by rfl)
    (hheldX : 0 < okPolls (clcResp L g) pre →
      (l'.site = .clcFence ∨ l'.site = .ack ∨ l'.site.leaving = true) →
      ∃ rr, HeldRdL L g pre rr ∧ l'.x = firstOfL rr := by
      intro _ hl
      exact absurd hl (by simp [Loader.Site.leaving]))
    (hlvx : l'.site.leaving = true → 0 < okPolls (clcResp L g) pre → l'.x = Loader.none32 := by
      intro h _
      exact absurd h (by simp [Loader.Site.leaving]))
    (hpl : l'.site ≠ .clcLoad := by simp) :
    Counts L g l' (pre ++ [e]) := by
  have hk := fun m => quiet (Loader.code_objectOp l.site hs hcode) hfire m
  exact zero_step hc (fun s => (hk _).1) (hk _).1 hq8'
    (fun s => by simp [(hk _).2.1, hpend s]) (fun s => by simp [(hk _).2.2.2.1, hrem s, hrem0 s])
    (fun _ s => by simp [(hk _).2.2.2.1, hrem s, hrem0 s])
    (fun _ s => by simp [(hk _).2.1, hpend s, hpend0 s]) hdr
    (hs := hl) (hlive := hlive) (hcond := hcond) (hresp := hresp) (hpar := hpar)
    (hdone := hdone) (hresEq := hresEq) (hheldX := hheldX) (hlvx := hlvx) (hpl := hpl)

/-- A successful empty poll of slot `r`: the loader's successful polls on that slot grow by one, and
the slot takes the next block of the round robin (`rr_succ`). Its exact deltas (`hdelta`, `harrEq`)
say how the batch's copies and the drain move with it. -/
theorem poll_step {l l' : Loader.D} {pre : List Event} {e : Event} {r : Fin 4} {pc p : Nat}
    {acq : Bool} {sc : MbarScope} (hc : Counts L g l pre)
    (he : e = ⟨pc, .wait (Loader.emptyOf L g r) p true acq sc⟩)
    (hr4 : lcount L g pre % 4 = r.val) (hs : l.site ≠ .clcLoad) (hlive : Live l' → Live l)
    (hq8' : l'.q % 8 = 0)
    (harr : ∀ s : Fin 4, (if arrivesOn (Loader.fullOf L g s) e then 1 else 0) +
      (if Loader.pending l' s then 1 else 0) ≤
      (if Loader.pending l s then 1 else 0) + if r = s then 1 else 0)
    (hiss : ∀ s : Fin 4, (if issuesTo (Loader.fullOf L g s) e then 1 else 0) +
      Loader.remaining l' s ≤ Loader.remaining l s + 3 * if r = s then 1 else 0)
    (hdelta : l'.site.done = false → ∀ s : Fin 4,
      Loader.remaining l' s + 3 * Loader.drained l' s =
        Loader.remaining l s + 3 * Loader.drained l s + 3 * if r = s then 1 else 0)
    (harrEq : Loader.leader L g = true → l'.site.done = false → ∀ s : Fin 4,
      (if arrivesOn (Loader.fullOf L g s) e then 1 else 0) +
        (if Loader.pending l' s then 1 else 0) +
        Loader.drained l' s = (if Loader.pending l s then 1 else 0) + Loader.drained l s +
          (if r = s then 1 else 0))
    (hcond : LoaderCond l' (lcount L g pre + 1) := by simp only [LoaderCond]; omega)
    (hresp : CountOK l' (lcount L g pre + 1) (okPolls (clcResp L g) pre) := by
      simp only [CountOK]; omega)
    (hpar : l'.site.done = false → l.site.done = false ∧ ∀ s : Fin 4,
      (Loader.polled l s + if r = s then 1 else 0) % 2 = Loader.polled l' s % 2 := by
      intro hd; refine ⟨by simp [Loader.Site.done], fun s => ?_⟩; have := s.isLt
      simp only [Loader.polled] <;> split_ifs <;> omega)
    (hdx : l'.site.done = true → ∃ i : Fin 4, l.site = .drain i ∧ i.val = 3 ∧ r.val = 3 := by
      intro h; simp [Loader.Site.done] at h)
    (hresEq : l'.resp = l.resp := by rfl)
    (hheldX : 0 < okPolls (clcResp L g) pre →
      (l'.site = .clcFence ∨ l'.site = .ack ∨ l'.site.leaving = true) →
      ∃ rr, HeldRdL L g pre rr ∧ l'.x = firstOfL rr := by
      intro _ hl
      exact absurd hl (by simp [Loader.Site.leaving]))
    (hlvx : l'.site.leaving = true → 0 < okPolls (clcResp L g) pre → l'.x = Loader.none32 := by
      intro h _
      exact absurd h (by simp [Loader.Site.leaving]))
    (hpl : l'.site ≠ .clcLoad := by simp) :
    Counts L g l' (pre ++ [e]) := by
  have hN : lcount L g (pre ++ [e]) = lcount L g pre + 1 :=
    lcount_snoc (fun s => okPolls_snoc_ok he s)
  refine ⟨fun s => ?_, ?_, hq8', ?_, Rel.of_notPoll hc.rel (okPoll_clc_empty he) hs hlive,
    fun s => ?_, fun s => ?_, fun hd s => ?_, fun hd hnu => ?_, fun hd _hpos hnu => ?_,
    fun hd _ => ?_, fun hl hR' => ?_, fun hl hR' => ?_, fun h hR' => ?_, fun hl => ?_,
      hc.claimsBefore.snoc_no (okPoll_clc_empty he)⟩
  · rw [hN, okPolls_snoc_ok he s, hc.rank s]
    exact (rr_succ hr4 s).symm
  · rw [hN]
    exact hcond
  · rw [hN, okPolls_snoc_zero (okPoll_clc_empty he)]
    exact hresp
  · have h := hc.arrive s
    have h' := harr s
    rw [arrivals_snoc, okPolls_snoc_ok he s]
    omega
  · have h := hc.issue s
    have h' := hiss s
    rw [issues_snoc, okPolls_snoc_ok he s]
    omega
  · obtain ⟨hd0, hp⟩ := hpar hd
    have h := hc.parity hd0 s
    have h' := hp s
    rw [okPolls_snoc_ok he s]
    omega
  · obtain ⟨hd0, -⟩ := hpar hd
    obtain ⟨c1, c2⟩ := hc.exact hd0 (NoUb.of_snoc hnu)
    refine ⟨fun s => ?_, fun hL s => ?_⟩
    · have hI0 : issuesTo (Loader.fullOf L g s) e = false := by rw [he]; rfl
      have h1 := c1 s
      have h2 := hdelta hd s
      rw [issues_snoc, okPolls_snoc_ok he s, hI0]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    · have hA0 : arrivesOn (Loader.fullOf L g s) e = false := by rw [he]; rfl
      have h1 := c2 hL s
      have h2 := harrEq hL hd s
      simp only [hA0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h2
      rw [arrivals_snoc, okPolls_snoc_ok he s, hA0]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
  · obtain ⟨i, hl3, hi3, hr3⟩ := hdx hd
    have hl3' : l.site.done = false := by rw [hl3]; rfl
    obtain ⟨c1, c2⟩ := hc.exact hl3' (NoUb.of_snoc hnu)
    have hI0 : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hA0 : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hpl : ∀ s : Fin 4, Loader.pending l s = false := fun s => by simp [hl3, Loader.pending]
    have hrem : ∀ s : Fin 4, Loader.remaining l s = 0 := fun s => by simp [hl3, Loader.remaining]
    have hdrn : ∀ s : Fin 4, Loader.drained l s = if s.val < 3 then 1 else 0 :=
      fun s => by simp [hl3, Loader.drained, hi3]
    have hrs : ∀ s : Fin 4, r = s ↔ s.val = 3 := by
      intro s
      constructor
      · intro h
        rw [h] at hr3
        exact hr3
      · intro h
        exact Fin.ext (by omega)
    refine ⟨fun s => ?_, fun hL s => ?_⟩
    · have c1s := c1 s
      have hs4 := s.isLt
      rw [hrem s, Nat.add_zero, hdrn s] at c1s
      rw [issues_snoc, okPolls_snoc_ok he s, hI0 s]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hr : r = s
      · have hs3 : s.val = 3 := (hrs s).mp hr
        simp only [hr, ↓reduceIte]
        simp only [show ¬ (s.val < 3) by omega, ↓reduceIte] at c1s
        omega
      · have hs3 : s.val ≠ 3 := fun h => hr ((hrs s).mpr h)
        simp only [hr, ↓reduceIte]
        simp only [show s.val < 3 by omega, ↓reduceIte] at c1s
        omega
    · have c2s := c2 hL s
      have hs4 := s.isLt
      rw [hpl s] at c2s
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at c2s
      rw [hdrn s] at c2s
      rw [arrivals_snoc, okPolls_snoc_ok he s, hA0 s]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hr : r = s
      · have hs3 : s.val = 3 := (hrs s).mp hr
        simp only [hr, ↓reduceIte]
        simp only [show ¬ (s.val < 3) by omega, ↓reduceIte] at c2s
        omega
      · have hs3 : s.val ≠ 3 := fun h => hr ((hrs s).mpr h)
        simp only [hr, ↓reduceIte]
        simp only [show s.val < 3 by omega, ↓reduceIte] at c2s
        omega
  · obtain ⟨i, hl3, hi3, hr3⟩ := hdx hd
    have hcd := hc.cond
    have hrs2 := hc.resp
    simp only [LoaderCond, hl3] at hcd
    simp only [CountOK, hl3] at hrs2
    rw [hN, okPolls_snoc_zero (okPoll_clc_empty he)]
    omega
  · rw [okPolls_snoc_zero (okPoll_clc_empty he)] at hR'
    obtain ⟨rr, hrr, hres⟩ := hc.heldR hs hR'
    exact ⟨rr, hrr.snoc (okPoll_clc_empty he), by rw [hresEq]; exact hres⟩
  · rw [okPolls_snoc_zero (okPoll_clc_empty he)] at hR'
    obtain ⟨rr, hrr, hx⟩ := hheldX hR' hl
    exact ⟨rr, hrr.snoc (okPoll_clc_empty he), hx⟩
  · rw [okPolls_snoc_zero (okPoll_clc_empty he)] at hR'
    exact hlvx h hR'
  · exact absurd hl hpl

/-- A successful CLC response poll moves the loader to the response read. -/
theorem resp_step {l : Loader.D} {pre : List Event} {e : Event} {pc p : Nat} {acq : Bool} {sc :
    MbarScope}
    (hc : Counts L g l pre) (hl : l.site = .clcWait)
    (he : e = ⟨pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p true acq sc⟩) :
    Counts L g { l with site := .clcLoad } (pre ++ [e]) := by
  have hP : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false := fun s =>
    okPoll_empty_lit (s := s) he
  have hC : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre + 1 := by
    rw [okPolls_snoc, okPoll_clc_lit he]
    simp
  have hN : lcount L g (pre ++ [e]) = lcount L g pre := lcount_snoc_zero hP
  have hA : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
  have hI : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
  refine ⟨fun s => ?_, ?_, hc.q8, ?_, ?_, fun s => ?_, fun s => ?_, fun _ s => ?_, fun _ hnu => ?_,
    fun hd _ _ => absurd hd (by simp [Loader.Site.done]), fun hd _ =>
      absurd hd (by simp [Loader.Site.done]),
    fun h _ => absurd rfl h, fun h _ => absurd h (by simp [Loader.Site.leaving]),
    fun h _ => absurd h (by simp [Loader.Site.leaving]), fun _ =>
      ⟨e, p, acq, sc, by simp, by rw [he]; rfl⟩,
    ClaimsBefore.snoc_poll hc.rel (by simp [Live, hl]) (by
      simp [hl]) hc.claimsBefore e (okPoll_clc_lit he)⟩
  · rw [hN, okPolls_snoc_zero (hP s)]
    exact hc.rank s
  · rw [hN]
    have h := hc.cond
    simp only [LoaderCond, hl] at h ⊢
    exact h
  · rw [hN, hC]
    have h := hc.resp
    simp only [CountOK, hl] at h ⊢
    omega
  · exact Rel.step hc.rel (fun _ _ _ _ _ => rfl)
      (fun _ _ _ _ hL _ => absurd (hc.rel.2 _ _ _ _ hL) (by simp [hl]))
      (fun _ => by simp [Live, hl])
  · have h := hc.arrive s
    rw [arrivals_snoc, hA s, okPolls_snoc_zero (hP s)]
    simp only [Loader.pending, hl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h ⊢
    omega
  · have h := hc.issue s
    rw [issues_snoc, hI s, okPolls_snoc_zero (hP s)]
    simp only [Loader.remaining, hl, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at h ⊢
    omega
  · have h := hc.parity (by simp [hl, Loader.Site.done]) s
    rw [okPolls_snoc_zero (hP s)]
    simpa [Loader.polled, hl] using h
  · obtain ⟨c1, c2⟩ := hc.exact (by simp [hl, Loader.Site.done]) (NoUb.of_snoc hnu)
    refine ⟨fun s => ?_, fun hL s => ?_⟩
    · have h1 := c1 s
      rw [issues_snoc, hI s, okPolls_snoc_zero (hP s)]
      simp only [Loader.remaining, Loader.drained, hl, Nat.add_zero, Bool.false_eq_true,
        ↓reduceIte] at h1 ⊢
      omega
    · have h1 := c2 hL s
      rw [arrivals_snoc, hA s, okPolls_snoc_zero (hP s)]
      simp only [Loader.pending, Loader.drained, hl, Nat.add_zero, Bool.false_eq_true,
        ↓reduceIte] at h1 ⊢
      omega

/-- One step of the loader's run: `Counts` moves with the event the site fires. -/
theorem step {P : Params} {mem0 : Mem0} {pre : List Event} {e : Event} {l l' : Loader.D}
    {t : TState} {ins : Instr} {o : Option TState} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hi : Loader.Inv l) (hc : Counts L g l pre) (hat : At t l.site.pc (Loader.facts L g l))
    (hcode : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : Loader.next L g l e = some (some l')) : Counts L g l' (pre ++ [e]) := by
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  have hq8 : q % 8 = 0 := hi.q8
  have hq128 : q < 128 := hi.q
  cases site with
  | wait b =>
    obtain ⟨ok, acq, sc, he⟩ := Loader.wait_event hpre b rfl hat hcode hfire
    have hR : okPoll (clcResp L g) e = false := okPoll_clc_empty he
    have hA : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hI : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    cases ok
    · simp only [Loader.next, he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact zero_step hc (fun s => by rw [Loader.okPoll_wait_empty he]; simp) hR hq8
        (fun s => by simp [hA s]) (fun s => by simp [hI s])
        (hissEq := fun _ s => by simp [hI s]) (harrEq := fun _ s => by simp [hA s])
        (hcond := hc.cond) (hresp := hc.resp)
    · simp only [Loader.next, he, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      have hcd : lcount L g pre % 128 = q + b.val := hc.cond
      have hr4 : lcount L g pre % 4 = (InputRing.slotOf b).val := by
        have : (InputRing.slotOf b).val = b.val % 4 := rfl
        omega
      have hrs : okPolls (clcResp L g) pre = lcount L g pre / 128 := hc.resp
      exact poll_step hc he hr4 (by simp) (fun _ => by simp [Live]) hq8
        (fun s => by simp [Loader.pending, hA s]) (fun s => by simp [Loader.remaining, hI s])
        (hdelta := fun _ s => by
          simp only [Loader.remaining, Loader.drained, Fin.val_zero]; split_ifs <;> omega)
        (harrEq := fun _ _ s => by simp [Loader.pending, Loader.drained, hA s])
  | load b j =>
    have hb8 := b.isLt
    have hP : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false := fun s =>
      okPoll_of_notPoll (Loader.code_notPoll (.load b j) rfl hcode) hfire
    have hR : okPoll (clcResp L g) e = false :=
      okPoll_of_notPoll (Loader.code_notPoll (.load b j) rfl hcode) hfire
    have hA : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s =>
      arrivesOn_of_arriveOp (Loader.code_arriveOp (.load b j) rfl hcode) hfire
    have hIs : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = true → InputRing.slotOf b = s := by
      intro s hs
      cases o with
      | none => rw [issuesTo_notTensor (fires_none_notTensor hfire)] at hs; cases hs
      | some u =>
        obtain ⟨addr, spec, he, hmb⟩ := Loader.load_event hpre hg b j rfl hat hcode hfire
        rw [he, issuesTo_tensorIssue, hmb] at hs
        exact fullLoc_eq_iff.mp (of_decide_eq_true hs)
    have hI : ∀ s : Fin 4, (if issuesTo (Loader.fullOf L g s) e then 1 else 0) ≤
        if InputRing.slotOf b = s then 1 else 0 := by
      intro s
      by_cases h : issuesTo (Loader.fullOf L g s) e = true
      · simp [h, hIs s h]
      · simp [h]
    -- without undefined behaviour the load is a tensor issue on its slot, so the issues are exact
    have hIe : NoUb (pre ++ [e]) → ∀ s : Fin 4,
        (if issuesTo (Loader.fullOf L g s) e then 1 else 0) =
          if InputRing.slotOf b = s then 1 else 0 := by
      intro hnu s
      cases o with
      | none =>
        rcases fires_none_ends hfire with ⟨f, hf⟩ | hx
        · exact absurd hf (hnu.last f)
        · obtain ⟨dst, map, cs, hc'⟩ := Loader.code_load_op b j
          rw [hc'] at hcode
          cases hcode
          exact absurd (fires_exit_op hfire hx) (by simp)
      | some u =>
        obtain ⟨addr, spec, he, hmb⟩ := Loader.load_event hpre hg b j rfl hat hcode hfire
        rw [he, issuesTo_tensorIssue, hmb]
        simp [Loader.fullOf, fullLoc_eq_iff]
    have hcd : 0 < lcount L g pre ∧ (lcount L g pre - 1) % 128 = q + b.val := hc.cond
    have hrs : okPolls (clcResp L g) pre = (lcount L g pre - 1) / 128 := hc.resp
    have hjl := j.isLt
    simp only [Loader.next, Loader.endOfTrip] at hn
    split_ifs at hn with h1 h2 h3 h4 <;> obtain rfl := Option.some.inj (Option.some.inj hn)
    · -- the next load of the batch
      exact zero_step hc hP hR hq8 (fun s => by simp [Loader.pending, hA s]) (fun s => by
        have := hI s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (hissEq := fun hnu s => by
          have := hIe hnu s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (harrEq := fun _ s => by simp [Loader.pending, hA s])
    · -- the batch's arrival on the leader CTA's full barrier
      exact zero_step hc hP hR hq8 (fun s => by simp [Loader.pending, hA s]) (fun s => by
        have := hI s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (hissEq := fun hnu s => by
          have := hIe hnu s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (harrEq := fun _ s => by simp [Loader.pending, hA s])
    · -- the next block's wait
      exact zero_step hc hP hR hq8 (fun s => by simp [Loader.pending, hA s]) (fun s => by
        have := hI s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (hissEq := fun hnu s => by
          have := hIe hnu s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (harrEq := fun hL => absurd hL h2)
    · -- the trip ends: the next trip's first wait, from block 7
      exact zero_step hc hP hR (by show (q + 8) % 8 = 0; omega)
        (fun s => by simp [Loader.pending, hA s]) (fun s => by
          have := hI s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (hissEq := fun hnu s => by
          have := hIe hnu s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (harrEq := fun hL => absurd hL h2)
        (hcond := by simp only [LoaderCond, Fin.val_zero]; omega)
    · -- the trip ends: the response poll
      exact zero_step hc hP hR hq8 (fun s => by simp [Loader.pending, hA s]) (fun s => by
        have := hI s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (hissEq := fun hnu s => by
          have := hIe hnu s; simp only [Loader.remaining] at this ⊢; split_ifs at this ⊢ <;> omega)
        (harrEq := fun hL => absurd hL h2)
  | arrive b =>
    have hb8 := b.isLt
    obtain ⟨rel, sc, he⟩ := Loader.arrive_event hpre hg b rfl hat hcode hfire
    have hP : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false := fun s => by rw [he]; rfl
    have hR : okPoll (clcResp L g) e = false := by rw [he]; rfl
    have hI0 : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hA : ∀ s : Fin 4, (if arrivesOn (Loader.fullOf L g s) e then 1 else 0) ≤
        if InputRing.slotOf b = s then 1 else 0 := by
      intro s
      by_cases h : arrivesOn (Loader.fullOf L g s) e = true
      · have h' : InputRing.slotOf b = s := by
          rw [arrivesOn_arrive he] at h
          exact fullLoc_eq_iff.mp (of_decide_eq_true h)
        simp [h, h']
      · simp [h]
    have hAeq : ∀ s : Fin 4, (if arrivesOn (Loader.fullOf L g s) e then 1 else 0) =
        if InputRing.slotOf b = s then 1 else 0 := by
      intro s
      rw [arrivesOn_arrive he]
      simp [Loader.fullOf, fullLoc_eq_iff]
    have hcd : 0 < lcount L g pre ∧ (lcount L g pre - 1) % 128 = q + b.val := hc.cond
    have hrs : okPolls (clcResp L g) pre = (lcount L g pre - 1) / 128 := hc.resp
    simp only [Loader.next, Loader.endOfTrip] at hn
    split_ifs at hn with h1 h2 <;> obtain rfl := Option.some.inj (Option.some.inj hn)
    · -- the next block's wait
      exact zero_step hc hP hR hq8 (fun s => by simpa [Loader.pending] using hA s)
        (fun s => by simp [Loader.remaining, hI0 s])
        (hissEq := fun _ s => by simp [Loader.remaining, hI0 s])
        (harrEq := fun _ s => by simp [Loader.pending, hAeq s])
    · -- the trip ends: the next trip's first wait
      exact zero_step hc hP hR (by show (q + 8) % 8 = 0; omega)
        (fun s => by simpa [Loader.pending] using hA s) (fun s => by simp [Loader.remaining, hI0 s])
        (hissEq := fun _ s => by simp [Loader.remaining, hI0 s])
        (harrEq := fun _ s => by simp [Loader.pending, hAeq s])
        (hcond := by simp only [LoaderCond, Fin.val_zero]; omega)
    · -- the trip ends: the response poll
      exact zero_step hc hP hR hq8 (fun s => by simpa [Loader.pending] using hA s)
        (fun s => by simp [Loader.remaining, hI0 s])
        (hissEq := fun _ s => by simp [Loader.remaining, hI0 s])
        (harrEq := fun _ s => by simp [Loader.pending, hAeq s])
  | clcWait =>
    obtain ⟨p, ok, acq, sc, -, he⟩ := Loader.clcWait_event hpre rfl hat hcode hfire
    have hP : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false := fun s =>
      okPoll_empty_lit (s := s) he
    have hA : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hI : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hR : okPoll (clcResp L g) e = ok := okPoll_clc_lit he
    cases ok
    · simp only [Loader.next, he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact zero_step hc hP hR hq8 (fun s => by simp [hA s]) (fun s => by simp [hI s])
        (hissEq := fun _ s => by simp [hI s]) (harrEq := fun _ s => by simp [hA s])
        (hcond := hc.cond) (hresp := hc.resp)
    · simp only [Loader.next, he, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact resp_step hc rfl he
  | clcLoad =>
    code_at hcode
    subst hcode
    have hbase := hpre.sharedRange
    unfold sharedBytes at hbase
    have hr : t.regs 814 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by loader_values))
    rcases fires_ldAcquire_kind hfire with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · obtain ⟨ha, hs⟩ := (fires_ldAcquire128 (effAddr_b32 hr (by omega)) hat.2.1 hfire) a bs hk
      have hP : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false := fun s => okPoll_of_rd hk
      have hR : okPoll (clcResp L g) e = false := okPoll_of_rd hk
      have hA : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s =>
        arrivesOn_notArrive (fun _ _ _ _ _ h => by rw [hk] at h; cases h)
      have hI : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s =>
        issuesTo_notTensor (fun _ _ h => by rw [hk] at h; cases h)
      have hN : lcount L g (pre ++ [e]) = lcount L g pre := lcount_snoc_zero hP
      have hC : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre :=
        okPolls_snoc_zero hR
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp only [Loader.next, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      obtain ⟨e', p', acq', sc', hl', hpe'⟩ := hc.polledL rfl
      refine ⟨fun s => ?_, ?_, hq8, ?_, ?_, fun s => ?_, fun s => ?_, fun hd s => ?_,
        fun hd hnu => ?_, fun hd _ _ => absurd hd (by simp [Loader.Site.done]),
        fun hd _ => absurd hd (by simp [Loader.Site.done]),
        fun _ _ => ⟨rr, HeldRdL.of_read hl' hpe' rfl ha hs hrr, rfl⟩,
        fun h _ => absurd h (by simp [Loader.Site.leaving]),
        fun h _ => absurd h (by simp [Loader.Site.leaving]), fun h => absurd h (by simp),
        hc.claimsBefore.snoc_no hR⟩
      · rw [hN, okPolls_snoc_zero (hP s)]
        exact hc.rank s
      · rw [hN]
        exact hc.cond
      · rw [hN, hC]
        exact hc.resp
      · exact Rel.step hc.rel (fun _ _ _ _ he' => by cases he')
          (fun _ _ _ _ _ hL => ⟨epc, a, bs, rr, by simp, ha, hs, hrr, hL rr rfl⟩)
          (fun _ => by simp [Live])
      · rw [arrivals_snoc, hA s, okPolls_snoc_zero (hP s)]
        have := hc.arrive s
        simp only [Loader.pending, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this ⊢
        omega
      · rw [issues_snoc, hI s, okPolls_snoc_zero (hP s)]
        have := hc.issue s
        simp only [Loader.remaining, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at this ⊢
        omega
      · rw [okPolls_snoc_zero (hP s)]
        have := hc.parity rfl s
        simpa [Loader.polled] using this
      · obtain ⟨c1, c2⟩ := hc.exact (by simp [Loader.Site.done]) (NoUb.of_snoc hnu)
        refine ⟨fun s => ?_, fun hL s => ?_⟩
        · have := c1 s
          rw [issues_snoc, hI s, okPolls_snoc_zero (hP s)]
          simp only [Loader.remaining, Loader.drained, Nat.add_zero, Bool.false_eq_true,
            ↓reduceIte] at this ⊢
          omega
        · have := c2 hL s
          rw [arrivals_snoc, hA s, okPolls_snoc_zero (hP s)]
          simp only [Loader.pending, Loader.drained, Bool.false_eq_true, ↓reduceIte,
            Nat.add_zero] at this ⊢
          omega
    · obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp [Loader.next] at hn
  | clcStatus =>
    simp only [Loader.next] at hn
    split at hn
    · rename_i q' rr hk
      obtain rfl := Option.some.inj (Option.some.inj hn)
      split_ifs with hf
      · exact free_step hc rfl (by simp) hcode hfire id hq8 hc.cond hc.resp (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun hd => ⟨hd, fun _ => rfl⟩)
          (hheldX := fun _ hl => absurd hl (by simp [Loader.Site.leaving]))
      · exact free_step hc rfl (by simp) hcode hfire (fun h => by simp [Live] at h) hq8 hc.cond
          hc.resp (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun hd => ⟨hd, fun _ => rfl⟩)
          (hheldX := fun hR _ => by
            obtain ⟨rr0, hrr0, hres0⟩ := hc.heldR (by simp) hR
            exact ⟨rr0, hrr0,
              by rw [← (Loader.query_site hat hcode hfire hk).2 rr0 hres0];
                 exact (firstOfL_of_not hf).symm⟩)
    · cases hn
  | clcFirst =>
    simp only [Loader.next] at hn
    split at hn
    · rename_i q' rr' hk
      obtain rfl := Option.some.inj (Option.some.inj hn)
      refine free_step hc rfl (by simp) hcode hfire (fun hL rr0 hres => ?_) hq8 hc.cond hc.resp
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun hd => ⟨hd, fun _ => rfl⟩)
        (hheldX := fun hR _ => by
          obtain ⟨rr0, hrr0, hres0⟩ := hc.heldR (by simp) hR
          exact ⟨rr0, hrr0, by rw [(Loader.query_site hat hcode hfire hk).2 rr0 hres0]; rfl⟩)
      have hrr := (Loader.query_site (d := ⟨.clcFirst, m, n, q, cp, resp, x⟩) hat hcode hfire
        hk).2 rr0 hres
      subst hrr
      exact hL
    · cases hn
  | clcFence =>
    simp only [Loader.next, Option.some.injEq] at hn
    subst hn
    exact free_step hc rfl (by simp) hcode hfire id hq8 hc.cond hc.resp (fun _ => rfl)
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inl rfl) hR;
                                    exact ⟨rr, hrr, hx⟩)
      (fun _ => rfl) (fun _ => rfl) (fun hd => ⟨hd, fun _ => rfl⟩)
  | ack =>
    have hk0 : ∀ s : Fin 4, okPoll (Loader.emptyOf L g s) e = false ∧
        arrivesOn (Loader.fullOf L g s) e = false ∧ issuesTo (Loader.fullOf L g s) e = false ∧
        okPoll (clcResp L g) e = false := by
      intro s
      cases o with
      | none => exact ⟨okPoll_notWait (fires_none_notWait hfire),
          arrivesOn_notArrive (fires_none_notArrive hfire),
          issuesTo_notTensor (fires_none_notTensor hfire),
            okPoll_notWait (fires_none_notWait hfire)⟩
      | some u =>
        obtain ⟨tx, c, rel', sc', he⟩ := Loader.ack_event hpre hg rfl hat hcode hfire
        refine ⟨by rw [he]; rfl, ?_, by rw [he]; rfl, by rw [he]; rfl⟩
        rw [arrivesOn_arrive he]
        exact decide_eq_false (ackLoc_ne_fullOf L g s)
    simp only [Loader.next] at hn
    split_ifs at hn with hx
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact zero_step hc (fun s => (hk0 s).1) (hk0 0).2.2.2 hq8
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inr (Or.inl rfl)) hR;
                                    exact ⟨rr, hrr, hx⟩)
        (fun s => by simp [(hk0 s).2.1, Loader.pending])
        (fun s => by simp [(hk0 s).2.2.1, Loader.remaining])
        (hissEq := fun _ s => by simp [(hk0 s).2.2.1, Loader.remaining])
        (harrEq := fun _ s => by simp [(hk0 s).2.1, Loader.pending])
        (hcond := hc.cond) (hresp := hc.resp) (hlvx := fun _ _ => hx)
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact zero_step hc (fun s => (hk0 s).1) (hk0 0).2.2.2 (by simp)
        (fun s => by simp [(hk0 s).2.1, Loader.pending])
        (fun s => by simp [(hk0 s).2.2.1, Loader.remaining])
        (hissEq := fun _ s => by simp [(hk0 s).2.2.1, Loader.remaining])
        (harrEq := fun _ s => by simp [(hk0 s).2.1, Loader.pending])
        (hlive := fun _ => hx)
        (hcond := by have hcd := hc.cond; simp only [LoaderCond] at hcd ⊢; omega)
        (hresp := hc.resp)
  | drain i =>
    obtain ⟨ok, acq, sc, he⟩ := Loader.drain_event hpre i rfl hat hcode hfire
    have hR : okPoll (clcResp L g) e = false := okPoll_clc_empty he
    have hA : ∀ s : Fin 4, arrivesOn (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    have hI : ∀ s : Fin 4, issuesTo (Loader.fullOf L g s) e = false := fun s => by rw [he]; rfl
    cases ok
    · simp only [Loader.next, he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact zero_step hc (fun s => by rw [Loader.okPoll_wait_empty he]; simp) hR hq8
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inr (Or.inr rfl)) hR;
                                    exact ⟨rr, hrr, hx⟩)
          (hlvx := fun h hR => hc.leaveX h hR)
        (fun s => by simp [hA s]) (fun s => by simp [hI s])
        (hissEq := fun _ s => by simp [hI s]) (harrEq := fun _ s => by simp [hA s])
        (hcond := hc.cond) (hresp := hc.resp)
    · simp only [Loader.next, he, ↓reduceIte] at hn
      have hcd : 128 ≤ lcount L g pre ∧ lcount L g pre % 128 = i.val := hc.cond
      have hrs : okPolls (clcResp L g) pre = lcount L g pre / 128 := hc.resp
      have hr4 : lcount L g pre % 4 = i.val := by have := i.isLt; omega
      have hi3 := i.isLt
      split at hn
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        exact poll_step hc he hr4 (by simp) (fun h => by simp [Live] at h) hq8
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inr (Or.inr rfl)) hR;
                                    exact ⟨rr, hrr, hx⟩)
          (hlvx := fun h hR => hc.leaveX h hR)
          (fun s => by simp [Loader.pending, hA s]) (fun s => by simp [Loader.remaining, hI s])
          (hdelta := fun _ s => by
            simp only [Loader.remaining, Loader.drained, Fin.ext_iff]
            split_ifs <;> omega)
          (harrEq := fun _ _ s => by
            simp only [Loader.pending, Loader.drained, hA s, Bool.false_eq_true, ↓reduceIte,
              Fin.ext_iff]
            split_ifs <;> omega)
      · have hi3eq : i.val = 3 := by omega
        obtain rfl := Option.some.inj (Option.some.inj hn)
        exact poll_step hc he hr4 (by simp) (fun h => by simp [Live] at h) hq8
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inr (Or.inr rfl)) hR;
                                    exact ⟨rr, hrr, hx⟩)
          (hlvx := fun h hR => hc.leaveX h hR)
          (fun s => by simp [Loader.pending, hA s]) (fun s => by simp [Loader.remaining, hI s])
          (hdelta := fun h => by simp [Loader.Site.done] at h)
          (harrEq := fun _ h => by simp [Loader.Site.done] at h)
          (hcond := trivial) (hresp := by simp only [CountOK]; omega)
          (hpar := fun hd => by simp [Loader.Site.done] at hd)
          (hdx := fun _ => ⟨i, rfl, hi3eq, hi3eq⟩)
  | exitArrive =>
    simp only [Loader.next, Option.some.injEq] at hn
    subst hn
    exact free_step hc rfl (by simp) hcode hfire (fun h => by simp [Live] at h) hq8 (by trivial)
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inr (Or.inr rfl)) hR;
                                    exact ⟨rr, hrr, hx⟩)
          (hlvx := fun h hR => hc.leaveX h hR)
      (by simpa [CountOK] using hc.resp) (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl)
      (fun h => by simp [Loader.Site.done] at h) (hdone := fun _ => by simp [Loader.Site.done])
  | exitWait =>
    simp only [Loader.next, Option.some.injEq] at hn
    subst hn
    exact free_step hc rfl (by simp) hcode hfire (fun h => by simp [Live] at h) hq8 (by trivial)
          (hheldX := fun hR _ => by obtain ⟨rr, hrr, hx⟩ := hc.heldX (Or.inr (Or.inr rfl)) hR;
                                    exact ⟨rr, hrr, hx⟩)
          (hlvx := fun h hR => hc.leaveX h hR)
      (by simpa [CountOK] using hc.resp) (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl)
      (fun h => by simp [Loader.Site.done] at h) (hdone := fun _ => by simp [Loader.Site.done])
  | exit => simp [Loader.next] at hn

/-- The tile of the loader's task loop: the tile of its task numbered by its successful response
polls (`Consumer.TileAt`). -/
def TileRel (L : Launch) (g : Nat) (l : Loader.D) (es : List Event) : Prop :=
  l.site.inTask = true → Consumer.TileAt L g es (okPolls (clcResp L g) es) l.m l.n

/-- The loader polls its CTA's response barrier only at its CLC poll. -/
theorem okPoll_resp_site {P : Params} {mem0 : Mem0} (hpre : Pre P L mem0) {l : Loader.D}
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : At t l.site.pc (Loader.facts L g l)) (hcode : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o)
    (h : okPoll (clcResp L g) e = true) : l.site = .clcWait := by
  cases hp : l.site.polls
  · rw [okPoll_of_notPoll (Loader.code_notPoll l.site hp hcode) hfire] at h
    cases h
  · obtain ⟨site, m, n, q, cp, r, x⟩ := l
    simp only at hp ⊢
    cases site with
    | wait b =>
      obtain ⟨ok, acq, sc, he⟩ := Loader.wait_event (d := ⟨.wait b, m, n, q, cp, r,
        x⟩) hpre b rfl hat hcode
        hfire
      rw [okPoll_clc_empty (s := InputRing.slotOf b) he] at h
      cases h
    | drain i =>
      obtain ⟨ok, acq, sc, he⟩ := Loader.drain_event (d := ⟨.drain i, m, n, q, cp, r,
        x⟩) hpre i rfl hat hcode
        hfire
      rw [okPoll_clc_empty (s := i) he] at h
      cases h
    | clcWait => rfl
    | _ => simp [Loader.Site.polls] at hp

set_option maxHeartbeats 8000000 in
/-- One step of the loader's run keeps the tile of its task loop: a step inside the task keeps the
tile and the task, and the acknowledgement's step into the next task takes the claimed tile of the
response it read. -/
theorem tile_step {P : Params} {mem0 : Mem0} {pre : List Event} {e : Event} {l l' : Loader.D}
    {t : TState} {ins : Instr} {o : Option TState} (hpre : Pre P L mem0)
    (hc : Counts L g l pre) (ht : TileRel L g l pre) (hat : At t l.site.pc (Loader.facts L g l))
    (hcode : kernel.code[l.site.pc]? = some ins)
    (hfire : Fires l.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : Loader.next L g l e = some (some l')) : TileRel L g l' (pre ++ [e]) := by
  intro hl'
  have hR : l.site ≠ .clcWait → okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
    intro hs
    rw [okPolls_snoc]
    cases h : okPoll (clcResp L g) e
    · simp
    · exact absurd (okPoll_resp_site hpre hat hcode hfire h) hs
  obtain ⟨site, m, n, q, cp, r, x⟩ := l
  cases site
  case ack =>
    simp only [Loader.next] at hn
    split_ifs at hn with hx
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      simp [Loader.Site.inTask] at hl'
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      have hcond : LoaderCond ⟨.ack, m, n, q, cp, r, x⟩ (lcount L g pre) := hc.cond
      have hresp : CountOK ⟨.ack, m, n, q, cp, r, x⟩ (lcount L g pre) (okPolls (clcResp L g) pre) :=
        hc.resp
      simp only [LoaderCond, CountOK] at hcond hresp
      have hpos : 0 < okPolls (clcResp L g) pre := by
        rw [hresp]; exact Nat.div_pos hcond.1 (by decide)
      obtain ⟨rr, hrr, hxr⟩ := hc.heldX (Or.inr (Or.inl rfl)) hpos
      obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, -, -, h5, h6⟩ := hrr
      rw [hR (by simp)]
      refine .inr ⟨x, hpos, ?_, hx, rfl, rfl⟩
      refine ⟨j, pc, p, acq, sc, pcr, a, bs, rr, ?_, ?_, ?_, h5, ?_⟩
      · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1
      · rw [List.take_append_of_le_length (List.getElem?_eq_some_iff.mp h1).1.le]; omega
      · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h2).1]; exact h2
      · simp only at hxr
        exact hxr
  case wait b =>
    have h0 := ht rfl
    rw [hR (by simp)]
    simp only [Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h0.snoc e
    · cases hn
  case load b j =>
    have h0 := ht rfl
    rw [hR (by simp)]
    simp only [Loader.next, Loader.endOfTrip] at hn
    split_ifs at hn <;> obtain rfl := Option.some.inj (Option.some.inj hn) <;>
      (try simp [Loader.Site.inTask] at hl') <;> exact h0.snoc e
  case arrive b =>
    have h0 := ht rfl
    rw [hR (by simp)]
    simp only [Loader.next, Loader.endOfTrip] at hn
    split_ifs at hn <;> obtain rfl := Option.some.inj (Option.some.inj hn) <;>
      (try simp [Loader.Site.inTask] at hl') <;> exact h0.snoc e
  all_goals exfalso
  all_goals clear ht hc hat hcode hfire hR
  all_goals simp only [Loader.next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
                  obtain ⟨_, -, rfl⟩ := hn))
  all_goals (try subst hn)
  all_goals simp_all [Loader.Site.inTask]

end LoaderTasks

namespace Loader

variable {L : Launch} {g : Nat}

/-- One loader step keeps the exit facts. -/
theorem exitQ_step {l l' : D} {es : List Event} {e : Event} (h : ExitQ L g l es)
    (hn : next L g l e = some (some l')) : ExitQ L g l' (es ++ [e]) := by
  obtain ⟨hA, hB⟩ := h
  obtain ⟨site, m, n, q, cp, r, x⟩ := l
  obtain ⟨pc, kind⟩ := e
  simp only [ExitQ] at hA hB ⊢
  cases site <;> simp only [next] at hn
  · -- wait: the input ring, vacuous for the exit facts
    cases kind <;> simp only [reduceCtorEq] at hn
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;> simp
  · -- load
    split at hn <;> (try split at hn) <;> (try split at hn) <;>
      simp only [Option.some.injEq] at hn <;> subst hn <;> (try simp only [endOfTrip]) <;>
      (try split_ifs) <;> simp
  · -- arrive
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      (try simp only [endOfTrip]) <;> (try split_ifs) <;> simp
  · -- clcWait
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i w p' ok acq sc
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;> simp
  · -- clcLoad
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i w bs
    cases hr : Flow.responseOf bs <;> simp only [hr, Option.map_none, Option.map_some,
      Option.some.injEq, reduceCtorEq] at hn
    subst hn
    simp
  · -- clcStatus
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i q0 r0
    by_cases hf : r0.firstCta.isSome = true
    · simp only [hf, ite_true, Option.some.injEq] at hn
      subst hn
      simp
    · have hf' : r0.firstCta.isSome = false := by simpa using hf
      have hnone : r0.firstCta = none := by simpa using hf'
      simp only [hf', Bool.false_eq_true, ite_false, Option.some.injEq] at hn
      subst hn
      refine ⟨fun hs => by simp at hs, fun _ hx => noClaimQ_snoc rfl ?_⟩
      simp [Loader.claims, hnone]
  · -- clcFirst
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i q0 r0
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun hs => by simp at hs, fun _ hx => noClaimQ_snoc rfl ?_⟩
    simp only [Loader.claims, ne_eq, not_not]
    exact hx
  · -- clcFence
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun hs => by simp at hs, fun _ hx => ?_⟩
    exact NoClaimQ.append ⟨pc, kind⟩ (hB (Or.inl rfl) hx)
  · -- ack: the no-CTA value leads to the drain, otherwise back to the input ring
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨fun _ => Or.inl (NoClaimQ.append _ ?_), fun hs => by simp at hs⟩
      exact hB (Or.inr rfl) ‹_›
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨fun hs => by simp at hs, fun hs => by simp at hs⟩
  · -- drain i: a successful drain poll moves on, or leaves for the exit stage after the last one
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i w p' ok acq sc
    cases ok
    · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at hn
      subst hn
      rcases hA (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))) with h1 | h1
      · exact ⟨fun _ => Or.inl (NoClaimQ.append _ h1), fun hs => by simp at hs⟩
      · exact ⟨fun _ => Or.inr (ElectOut.append _ h1), fun hs => by simp at hs⟩
    · simp only [ite_true] at hn
      split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
      · rcases hA (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))) with h1 | h1
        · exact ⟨fun _ => Or.inl (NoClaimQ.append _ h1), fun hs => by simp at hs⟩
        · exact ⟨fun _ => Or.inr (ElectOut.append _ h1), fun hs => by simp at hs⟩
      · rcases hA (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))) with h1 | h1
        · exact ⟨fun _ => Or.inl (NoClaimQ.append _ h1), fun hs => by simp at hs⟩
        · exact ⟨fun _ => Or.inr (ElectOut.append _ h1), fun hs => by simp at hs⟩
  · -- exitArrive
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun _ => ?_, fun hs => by simp at hs⟩
    rcases hA (Or.inl rfl) with h1 | h1
    · exact Or.inl (NoClaimQ.append _ h1)
    · exact Or.inr (ElectOut.append _ h1)
  · -- exitWait
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun _ => ?_, fun hs => by simp at hs⟩
    rcases hA (Or.inr (Or.inl rfl)) with h1 | h1
    · exact Or.inl (NoClaimQ.append _ h1)
    · exact Or.inr (ElectOut.append _ h1)
  · -- exit: no further step
    simp at hn

/-- A loader left idle by the prologue was left by an election whose leader is another lane. -/
theorem idle_elect {L : Launch} {g : Nat} {p : Prologue.D} {e : Event}
    (hn : Prologue.next L g p e = some (some (.inr (.loader Prologue.loaderIdle)))) :
    ∃ mk inst leader, e.kind = .elect mk inst leader ∧ leader ≠ laneOf L g := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.loader.injEq] at hn)
  all_goals first
    | (simp_all [Prologue.loaderStart, Prologue.loaderIdle]; done)
    | (rename_i a b c hk hne; exact ⟨a, b, c, hk, fun h => hne h.symm⟩)

/-- A loader step into the exit stage is the drain's last poll or a step of the exit stage. -/
theorem done_of_next {L : Launch} {g : Nat} {l l' : D} {e : Event} (h : next L g l e =
    some (some l'))
    (hd : l'.site.done = true) : l.site = .drain 3 ∨ l.site.done = true := by
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  cases site <;> simp only [next, endOfTrip] at h
  clc_sweep h
  all_goals first | (simp_all [Site.done]; done) | (left; simp_all [Site.done]; omega)

end Loader

namespace LoaderTasks

variable {L : Launch} {g : Nat}

/-- An exit-stage loader without successful empty polls was left idle by an election of another
lane. -/
def Idle (L : Launch) (g : Nat) (l : Loader.D) (es : List Event) : Prop :=
  l.site.done = true → lcount L g es = 0 → ElectOut L g es

/-- One loader step keeps `Idle`: the drain's last poll leaves at least 128 empty polls. -/
theorem idle_step {l l' : Loader.D} {pre : List Event} {e : Event} (hc : Counts L g l pre)
    (hn : Loader.next L g l e = some (some l')) (h : Idle L g l pre) : Idle L g l' (pre ++ [e]) :=
    by
  intro hd h0
  have hmono : lcount L g pre ≤ lcount L g (pre ++ [e]) := by
    unfold lcount
    exact Finset.sum_le_sum fun s _ => by rw [okPolls_snoc]; omega
  rcases Loader.done_of_next hn hd with hs | hs
  · have := hc.cond
    simp only [LoaderCond, hs] at this
    omega
  · exact (h hs (by omega)).append e

/-- The loader's run invariant: its counts, the tile of its task loop, its exit query
(`Loader.ExitQ`) and the idle lane's election (`Idle`). -/
def AlongT (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inr (.loader l), es => Counts L g l es ∧ TileRel L g l es ∧ Loader.ExitQ L g l es ∧
      Idle L g l es
  | d, es => Along L g d es

/-- Along a thread's run, the loader's run invariant holds at each of its states (`step`,
`tile_step`, `exitQ_step`, `idle_step` at each site). -/
theorem runT {P : Params} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    {es : List Event} (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      AlongT L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (AlongT L g) (show Quiet [] from quiet_nil) ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · have hq' : Quiet pre := hq
    have hq2 : Quiet (pre ++ [e]) := hq'.snoc (Prologue.fires_quiet hc hf)
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · exact hq2
    · refine ⟨start hq2 l' (Prologue.next_loader hn), ?_⟩
      rcases Prologue.next_loader hn with rfl | rfl
      · exact ⟨fun _ => .inl ⟨(hq2 _).1, rfl, rfl⟩, by simp [Loader.ExitQ, Prologue.loaderStart],
          fun hd => by simp [Prologue.loaderStart, Loader.Site.done] at hd⟩
      · obtain ⟨mk, inst, leader, hk, hne⟩ := Loader.idle_elect hn
        have hout : ElectOut L g (pre ++ [e]) := ⟨pre.length, e, by simp, mk, inst, leader, hk, hne⟩
        exact ⟨fun hl => absurd hl (by decide),
          ⟨fun _ => .inr hout, fun hs => by simp [Prologue.loaderIdle] at hs⟩, fun _ _ => hout⟩
    · trivial
    · trivial
    · trivial
  · obtain ⟨l', hl, rfl⟩ := next_of_loader hn
    exact ⟨step hpre hg hinv.1 hq.1 hat hc hf hl, tile_step hpre hq.1 hq.2.1 hat hc hf hl,
      Loader.exitQ_step hq.2.2.1 hl, idle_step hq.1 hl hq.2.2.2⟩
  · obtain ⟨m', -, rfl⟩ := next_of_mma hn
    trivial
  · obtain ⟨s', -, rfl⟩ := next_of_sched hn
    trivial
  · obtain ⟨c', -, rfl⟩ := next_of_cons hn
    trivial

/-- Along a thread's run, the loader's counts hold at each of its states (`step` at each site). -/
theorem run {P : Params} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    {es : List Event} (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      Along L g d (es.take j) := by
  intro j d hd
  have h := runT hpre hg htr j d hd
  rcases d with p | (l | m | sd | cs)
  · exact h
  · exact h.1
  all_goals trivial

end LoaderTasks

/-- Round robin: after `K` successful empty polls of the loader in all, slot `s` has had those
with index ≡ `s` mod 4, and the loader's site fixes `K` modulo the task's 128 blocks. -/
theorem loader_counts {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es)
    {k : Nat} {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (es.take k) =
      some (some (.inr (.loader l)))) :
    (∀ s : Fin 4, okPolls (inputEmpty L (g / L.block) s) (es.take k) =
      (loaderCount L g (es.take k) + 3 - s) / 4) ∧
    (match l.site with
     | .wait b => loaderCount L g (es.take k) % 128 = l.q + b.val ∧ l.q % 8 = 0
     | .load b _ | .arrive b => 0 < loaderCount L g (es.take k) ∧
         (loaderCount L g (es.take k) - 1) % 128 = l.q + b.val
     | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack =>
         128 ≤ loaderCount L g (es.take k) ∧ loaderCount L g (es.take k) % 128 = 0
     | .drain i => 128 ≤ loaderCount L g (es.take k) ∧ loaderCount L g (es.take k) % 128 = i.val
     | _ => True) := by
  have c : LoaderTasks.Counts L g l (es.take k) := LoaderTasks.run hpre hg htr k _ hσ
  simp only [loaderCount_eq]
  refine ⟨fun s => ?_, ?_⟩
  · rw [inputEmpty_eq]
    exact c.rank s
  · obtain ⟨site, m, n, q, cp, r, x⟩ := l
    cases site <;> first | exact ⟨c.cond, c.q8⟩ | exact c.cond

/-- The loader at its empty wait after its run: its empty polls in tasks of 128 are its response
polls, each followed by a read of a response that claims a CTA. -/
theorem loader_tasks_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {l : Loader.D} {b : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .wait b) :
    loaderCount L g (X.tr g) / 128 = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
    ∀ j pc p acq sc,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l))
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  have hco' : okPolls (clcResp L g) (X.tr g) = lcount L g (X.tr g) / 128 := by
    have h := c.resp
    unfold LoaderTasks.CountOK at h
    rw [hs] at h
    exact h
  have hLive : LoaderTasks.Live l := by
    unfold LoaderTasks.Live
    rw [hs]
    trivial
  refine ⟨?_, ?_⟩
  · rw [loaderCount_eq]
    exact hco'.symm
  · intro j pc p acq sc hw
    have hw' : (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := hw
    have hjlt : j < (X.tr g).length := by
      obtain ⟨h1, -⟩ := List.getElem?_eq_some_iff.mp hw'
      exact h1
    have hj1 : j + 1 < (X.tr g).length := by
      by_contra hcon
      have hlast : (X.tr g).getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := by
        rw [List.getLast?_eq_getElem?, show (X.tr g).length - 1 = j by omega]
        exact hw'
      have hcl := c.rel.2 pc p acq sc hlast
      rw [hs] at hcl
      cases hcl
    obtain ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩ := c.rel.1 j pc p acq sc hj1 hw' hLive
    refine ⟨pcr, src, bs, rr, hr, ?_, h3, h4⟩
    show src.loc = _ ∧ src.size = _
    exact ⟨h1, h2⟩

/-- A loader's successful response polls that are not its latest are followed by reads of responses
that claim a CTA. -/
theorem loader_claims_before_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l)))) :
    ∀ j pc p acq sc, X.get (g, j) = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      okPolls (clcResp L g) ((X.tr g).take j) + 1 < okPolls (clcResp L g) (X.tr g) →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l))
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  intro j pc p acq sc hw hcount
  obtain ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩ := c.claimsBefore j pc p acq sc hw hcount
  refine ⟨pcr, src, bs, rr, hr, ?_, h3, h4⟩
  show src.loc = _ ∧ src.size = _
  exact ⟨h1, h2⟩

/-- The loader at its CLC poll after its run has one task more than its successful response polls:
its successful empty polls are 128 per task. -/
theorem loader_clc_count_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .clcWait) :
    loaderCount L g (X.tr g) / 128 = okPolls (clcResp L g) (X.tr g) + 1 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l))
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  have h := c.resp
  simp only [LoaderTasks.CountOK, hs] at h
  rw [loaderCount_eq]
  omega

namespace InputRing

/-- At a loader's arrival on slot `s`'s full barrier, its earlier arrivals there are fewer than
its successful polls of slot `s`'s empty barrier. -/
theorem arrival_budget {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.loader l))))
    {s : Fin 4} {tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive (Loader.fullOf L g s) tx c rel sc) :
    arrivals (Loader.fullOf L g s) ((X.tr g).take k) + 1 ≤
      okPolls (Loader.emptyOf L g s) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, _, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hp := Loader.arrive_pending (l := l) hpre hg hat hc hfire hk
  have hq : LoaderTasks.Counts L g l ((X.tr g).take k) := LoaderTasks.run hpre hg htr k _ hσ
  have h := hq.arrive s
  rw [hp] at h
  simpa using h

/-- At a loader's tensor issue on slot `s`, its earlier issues there are fewer than three times
its empty polls of slot `s`. -/
theorem issue_budget {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.loader l))))
    {s : Fin 4} (hk : issuesTo (Loader.fullOf L g s) e = true) :
    ((X.tr g).take k).countP (issuesTo (Loader.fullOf L g s)) + 1 ≤
      3 * okPolls (Loader.emptyOf L g s) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, _, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hp := Loader.issue_pending (l := l) hpre hg hat hc hfire hk
  have hq : LoaderTasks.Counts L g l ((X.tr g).take k) := LoaderTasks.run hpre hg htr k _ hσ
  have h := hq.issue s
  omega

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof

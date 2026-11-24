-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCommits
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.RankDefs
public import Kernels.Fp16Gemm8192.Proof.Rings

@[expose] public section

/-! # The MMA warps' counting invariant

`Mma.Counts` relates an MMA thread's commits, polls and accumulator counts along its run: commits
to each slot's empty barrier (with the pending commit) equal its successful full polls, its commits
go round the four slots, and the CLC response is tracked by `task`, `held`, `polled` and `exitPoll`.
`Mma.counts_step` keeps it: an event that moves no count is `Mma.Counts.frame`, the others are
`Mma.Counts.step`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- The MMA thread's commits to the input empty barriers among `es`, summed by slot. -/
def mcount (L : Launch) (g : Nat) (es : List Event) : Nat :=
  ∑ s : Fin 4, es.countP (commitsTo (emptyAt L g s))

/-- The MMA thread's site against its commits `M` (so far): its K block is `M` modulo the task's
128 blocks. -/
def MmaCond (m : Mma.D) (M : Nat) : Prop :=
  match m.site with
  | .elect => M = 0
  | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack | .accWait => M % 128 = 0
  | .full s | .mma s _ | .commit s => M % 128 = m.q + s.val
  | .accCommit => 128 ≤ M ∧ M % 128 = 0
  | _ => True

theorem inputEmpty_emptyAt (L : Launch) (g : Nat) (s : Fin 4) :
    inputEmpty L (g / L.block) s.val = emptyAt L g s := by
  simp only [inputEmpty, Bar.loc, Bar.off, emptyAt, Nat.add_assoc]

theorem mmaCount_eq (L : Launch) (g : Nat) (es : List Event) : mmaCount L g es = mcount L g es := by
  unfold mmaCount mcount
  exact Finset.sum_congr rfl fun s _ => congrArg (fun m => es.countP (commitsTo m))
    (inputEmpty_emptyAt L g s)

/-- A commit on barrier `emptyAt s0` is a commit to slot `s0`'s empty barrier. -/
theorem countP_snoc_commit {L : Launch} {g : Nat} {pre : List Event} {e : Event} {s0 : Fin 4}
    (hk : e.kind = .tc (.commit (Mma.commitSpec L g s0))) (s : Fin 4) :
    (pre ++ [e]).countP (commitsTo (emptyAt L g s)) =
      pre.countP (commitsTo (emptyAt L g s)) + if s0 = s then 1 else 0 := by
  rw [commits_snoc, commitsTo_of_commitSpec hk]
  by_cases h : s0 = s <;> simp [h]

theorem mcount_snoc {L : Launch} {g : Nat} {pre : List Event} {e : Event} {r : Fin 4}
    (h : ∀ s : Fin 4, (pre ++ [e]).countP (commitsTo (emptyAt L g s)) =
      pre.countP (commitsTo (emptyAt L g s)) + if r = s then 1 else 0) :
    mcount L g (pre ++ [e]) = mcount L g pre + 1 := by
  unfold mcount
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- An event that is no commit to barrier `m` leaves its commit count unchanged. -/
theorem countP_snoc_none {m : Loc} {pre : List Event} {e : Event} (h : commitsTo m e = false) :
    (pre ++ [e]).countP (commitsTo m) = pre.countP (commitsTo m) := by
  rw [commits_snoc, h]
  simp

theorem mcount_snoc_none {L : Launch} {g : Nat} {pre : List Event} {e : Event}
    (h : ∀ s : Fin 4, commitsTo (emptyAt L g s) e = false) :
    mcount L g (pre ++ [e]) = mcount L g pre :=
  Finset.sum_congr rfl fun s _ => countP_snoc_none (h s)

/-- A wait on `l` is a successful poll of `m` exactly when it succeeds on `m`. -/
theorem okPoll_of_wait {m l : Loc} {e : Event} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (h : e.kind = .wait l p ok acq sc) : okPoll m e = (ok && decide (l = m)) := by
  obtain ⟨pc, k⟩ := e
  simp only at h
  subst h
  cases ok <;> simp [okPoll, sourceWaitSuccess]

/-- A wait is no commit. -/
theorem commitsTo_of_wait {m l : Loc} {e : Event} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (h : e.kind = .wait l p ok acq sc) : commitsTo m e = false :=
  commitsTo_of_notCommit fun sp hk => by rw [h] at hk; cases hk

/-- Barriers with different shared offsets are different locations. -/
theorem loc_ne {a b : Loc} (h : a.addr ≠ b.addr) : a ≠ b := fun e => h (congrArg Loc.addr e)

/-- The MMA thread's election event is a non-object event. -/
theorem elect_kind {L : Launch} {g : Nat} {d m' : Mma.D} {e : Event} (hs : d.site = .elect)
    (hn : Mma.next L g d e = some (some m')) : ∃ a b c, e.kind = .elect a b c := by
  obtain ⟨epc, ek⟩ := e
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs
  subst hs
  cases ek <;> simp [Mma.next] at hn ⊢

namespace Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Accumulator barrier `j` in thread `g`'s CTA (`full` or empty). -/
abbrev accBar (L : Launch) (g j : Nat) (full : Bool) : Loc :=
  Bar.loc L (g / L.block) ⟨.acc, j, full⟩

theorem accBar_eq (L : Launch) (g j : Nat) :
    accBar L g j false = ⟨.shared, g / L.block, L.sharedBase + 8 * j + 88⟩ := by
  simp only [accBar, Bar.loc, Bar.off]
  congr 1
  omega

theorem accBar_inj {a b : Nat} : accBar L g a false = accBar L g b false ↔ a = b := by
  rw [accBar_eq, accBar_eq]
  constructor
  · intro h
    have := congrArg Loc.addr h
    simp only at this
    omega
  · rintro rfl
    rfl

/-- Whether the MMA thread holds its accumulator: from the first full poll of a task to the
accumulator commit. -/
def holdsAcc (d : D) : Nat := match d.site with
  | .full _ | .mma _ _ | .commit _ | .accCommit => 1
  | _ => 0

/-- The event an MMA state fires, by its site: a poll (full, accumulator-empty or CLC response
barrier) or a commit (slot or accumulator); every other site fires neither. -/
def FiresAt (L : Launch) (g : Nat) (d : D) (e : Event) : Prop := match d.site with
  | .full s => ∃ ok acq sc, e.kind = .wait (fullOf L g s) d.fp ok acq sc
  | .accWait => ∃ ok acq sc, e.kind = .wait (accBar L g (d.w % 2) false) d.ap ok acq sc
  | .clcWait => ∃ p ok acq sc, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc
  | .commit s => e.kind = .tc (.commit (commitSpec L g s))
  | .accCommit => e.kind = .tc (.commit (accSpec L g d.w))
  | _ => (∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc) ∧ ∀ sp, e.kind ≠ .tc (.commit sp)

/-- A site that polls nothing and commits nothing fires neither. -/
theorem others_event {t : TState} {ins : Instr} {e : Event} {o : Option TState} (s : Site)
    (hp : s.polls = false) (hcm : s.commits = false) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Prod L g t ins.op) e o) :
    (∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc) ∧ ∀ sp, e.kind ≠ .tc (.commit sp) :=
  ⟨fun l p ok acq sc => fires_notWait (eventTmpl_notWait (code_notPoll s hp hc)) hf l p ok acq sc,
    notCommit_fires s hcm hc hf⟩

/-- The event an MMA state fires is the event of its site (`FiresAt`). -/
theorem site_event {t : TState} {ins : Instr} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? =
      some ins) (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    FiresAt L g d e := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hi hat hc hf
  cases site with
  | full s =>
    obtain ⟨ok, acq, sc, he⟩ := full_event hpre s rfl hi hat hc hf
    exact ⟨ok, acq, sc, by rw [he]⟩
  | accWait =>
    obtain ⟨ok, acq, sc, he⟩ := accWait_event hpre rfl hi hat hc hf
    exact ⟨ok, acq, sc, by rw [he, accBar_eq]⟩
  | clcWait =>
    obtain ⟨p, ok, acq, sc, -, he⟩ :=
      clcWait_event (d := ⟨.clcWait, w, q, fp, ap, cp, r, x⟩) hpre rfl hat hc hf
    exact ⟨p, ok, acq, sc, by rw [he]⟩
  | commit s =>
    simp only [FiresAt]
    rw [commit_event (d := ⟨.commit s, w, q, fp, ap, cp, r, x⟩) hpre hg s rfl hat hc hf]
  | accCommit =>
    simp only [FiresAt]
    rw [accCommit_spec (d := ⟨.accCommit, w, q, fp, ap, cp, r, x⟩) hpre hg rfl hat hc hf]
  | _ => exact others_event _ rfl rfl hc hf

/-- The CLC response barrier of thread `g`'s CTA, which the CLC poll waits on. -/
abbrev respBar (L : Launch) (g : Nat) : Loc := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩

/-- The response buffer of thread `g`'s CTA: the 16 bytes a CLC response is read from. -/
abbrev respLoc (L : Launch) (g : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + 144⟩

theorem respBar_eq {L : Launch} {g : Nat} :
    respBar L g = ⟨.shared, g / L.block, L.sharedBase + 104⟩ := by
  simp [respBar, Bar.loc, Bar.off]

/-- The response barrier is no accumulator barrier. -/
theorem accBar_ne_respBar {L : Launch} {g j : Nat} (hj : j < 2) :
    accBar L g j false ≠ respBar L g := by
  intro h
  rw [accBar_eq, respBar_eq] at h
  have h' := congrArg Loc.addr h
  simp only at h'
  omega

/-- The response barrier is no slot's full barrier. -/
theorem fullOf_ne_respBar {L : Launch} {g : Nat} (s : Fin 4) : fullOf L g s ≠ respBar L g := by
  intro h
  rw [respBar_eq] at h
  have h' := congrArg Loc.addr h
  simp only at h'
  have := s.isLt
  omega

/-- The first CTA a response names, as the query's `x` register holds it (`none32` when none). -/
def firstOf (rr : ClcResponse) : Nat := (rr.firstCta.map fun c => c.1.toNat).getD Loader.none32

/-- Whether the thread's task has started: from its response poll to its accumulator commit. -/
def taskStarted (d : D) : Nat := match d.site with
  | .elect | .clcWait | .accCommit | .exitArrive | .exitWait | .exit => 0
  | _ => 1

/-- The trip's position inside its task: slot `s`'s block `q + s` at the trip's sites. -/
def taskPos (d : D) : Nat := match d.site with
  | .full s | .mma s _ | .commit s => d.q + s.val
  | _ => 0

/-- A site that is no election, response read or query, and not past the task loop. -/
def Site.Plain (s : Site) : Prop :=
  s ≠ .elect ∧ s ≠ .clcLoad ∧ s ≠ .clcStatus ∧ s ≠ .clcFirst ∧ s.done = false

/-- Event `j` of `es` is the latest successful response poll, and event `j + 1` reads `rr`. -/
def HeldRead (L : Launch) (g : Nat) (es : List Event) (rr : ClcResponse) : Prop :=
  ∃ j pc p acq sc pcr a bs, es[j]? = some ⟨pc, .wait (respBar L g) p true acq sc⟩ ∧
    es[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧ a.loc = respLoc L g ∧ a.size = 16 ∧
    Flow.responseOf bs = some rr ∧
    okPolls (respBar L g) (es.take j) + 1 = okPolls (respBar L g) es

/-- A further event that is no response poll keeps the held response. -/
theorem HeldRead.snoc {L : Launch} {g : Nat} {es : List Event} {rr : ClcResponse} {e : Event}
    (h : HeldRead L g es rr) (he : okPoll (respBar L g) e = false) :
    HeldRead L g (es ++ [e]) rr := by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, ha, hs, hr, hc⟩ := h
  have hlt : j + 1 < es.length := (List.getElem?_eq_some_iff.mp h2).1
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, ?_, ?_, ha, hs, hr, ?_⟩
  · rw [List.getElem?_append_left (by omega)]
    exact h1
  · rw [List.getElem?_append_left hlt]
    exact h2
  · rw [List.take_append_of_le_length (by omega), okPolls_snoc, he, Nat.add_zero]
    exact hc

/-- A read of the response, right after the latest response poll `pe`, holds the response. -/
theorem HeldRead.of_read {L : Launch} {g : Nat} {es : List Event} {rr : ClcResponse} {pe e : Event}
    {p : Nat} {acq : Bool} {sc : MbarScope} {a : Acc} {bs : List (Option Byte)}
    (hl : es.getLast? = some pe) (hpe : pe.kind = .wait (respBar L g) p true acq sc)
    (hk : e.kind = .rd a bs) (ha : a.loc = respLoc L g) (hs : a.size = 16)
    (hr : Flow.responseOf bs = some rr) : HeldRead L g (es ++ [e]) rr := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  obtain ⟨pc, k⟩ := pe
  obtain ⟨epc, ek⟩ := e
  simp only at hpe hk
  subst hpe hk
  refine ⟨ys.length, pc, p, acq, sc, epc, a, bs, ?_, ?_, ha, hs, hr, ?_⟩
  · simp
  · simp
  · rw [List.take_append_of_le_length (by simp), List.take_append_of_le_length le_rfl,
      List.take_length, okPolls_snoc, okPolls_snoc, okPoll_of_rd (e := ⟨epc, .rd a bs⟩) rfl,
      okPoll_of_wait (e := ⟨pc, _⟩) rfl]
    simp

/-- An MMA state's response register holds its response. -/
theorem rq8_of_at {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : At t d.site.pc (facts L g d)) (hlive : 975 ∈ Flow.live d.site.pc) :
    t.regs 975 = some d.resp :=
  holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨975, hlive, by mma_values⟩)

/-- A response that names no first CTA is answered by `none32`. -/
theorem firstOf_of_not {rr : ClcResponse} (h : ¬ rr.firstCta.isSome = true) :
    firstOf rr = Loader.none32 := by
  unfold firstOf
  cases hc : rr.firstCta with
  | none => rfl
  | some c => simp [hc] at h

/-- The event at index `i` of a trace reads, from the response buffer, a response that claims a
CTA. -/
def CbReadClaims (L : Launch) (g : Nat) (es : List Event) (i : Nat) : Prop :=
  ∃ pcr a bs rr, es[i]? = some ⟨pcr, .rd a bs⟩ ∧ a.loc = respLoc L g ∧ a.size = 16 ∧
    Flow.responseOf bs = some rr ∧ Loader.claims rr

theorem cbOkPolls_take_le (m : Loc) (es : List Event) {k k' : Nat} (h : k ≤ k') :
    okPolls m (es.take k) ≤ okPolls m (es.take k') := by
  unfold okPolls
  exact (List.take_sublist_take_left (l := es) h).countP_le

theorem cbPoll_succ {m : Loc} {es : List Event} {j : Nat} {e : Event}
    (hj : es[j]? = some e) (hp : okPoll m e = true) :
    okPolls m (es.take (j + 1)) = okPolls m (es.take j) + 1 := by
  unfold okPolls
  rw [List.take_add_one, List.countP_append]
  simp [hj, hp]

/-- Two successful polls with the same number of earlier polls are the same index. -/
theorem cbPoll_index_eq {m : Loc} {es : List Event} {j j' : Nat} {e e' : Event}
    (hj : es[j]? = some e) (hp : okPoll m e = true)
    (hj' : es[j']? = some e') (hp' : okPoll m e' = true)
    (h : okPolls m (es.take j) = okPolls m (es.take j')) : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have h1 := cbPoll_succ (m := m) hj hp
    have h2 := cbOkPolls_take_le m es (show j + 1 ≤ j' from hlt)
    omega
  · exact heq
  · have h1 := cbPoll_succ (m := m) hj' hp'
    have h2 := cbOkPolls_take_le m es (show j' + 1 ≤ j from hgt)
    omega

/-- Appending an event that is no successful response poll keeps the claimed reads of the polls
that are not the latest. -/
theorem claimsBefore_snoc_no {L : Launch} {g : Nat} {es : List Event} {e : Event}
    (hC : ∀ j pc p acq sc, es[j]? = some ⟨pc, .wait (respBar L g) p true acq sc⟩ →
      okPolls (respBar L g) (es.take j) + 1 < okPolls (respBar L g) es →
        CbReadClaims L g es (j + 1))
    (hn : okPoll (respBar L g) e = false) :
    ∀ j pc p acq sc, (es ++ [e])[j]? = some ⟨pc, .wait (respBar L g) p true acq sc⟩ →
      okPolls (respBar L g) ((es ++ [e]).take j) + 1 < okPolls (respBar L g) (es ++ [e]) →
      CbReadClaims L g (es ++ [e]) (j + 1) := by
  intro j pc p acq sc hj hcount
  have hlen : j < (es ++ [e]).length := (List.getElem?_eq_some_iff.mp hj).1
  have hjlt : j < es.length := by
    by_contra hge
    have hjeq : j = es.length := by simp at hlen; omega
    subst hjeq
    have hsome : (es ++ [e])[es.length]? = some e := by simp
    rw [hsome] at hj
    have he2 : e = ⟨pc, .wait (respBar L g) p true acq sc⟩ := Option.some.inj hj
    rw [he2] at hn
    simp [okPoll, sourceWaitSuccess] at hn
  have hj' : es[j]? = some ⟨pc, .wait (respBar L g) p true acq sc⟩ := by
    rw [← List.getElem?_append_left hjlt]; exact hj
  have htake : (es ++ [e]).take j = es.take j := List.take_append_of_le_length hjlt.le
  have hok : okPolls (respBar L g) (es ++ [e]) = okPolls (respBar L g) es := by
    rw [okPolls_snoc, hn]; simp
  rw [htake, hok] at hcount
  obtain ⟨pcr, a, bs, rr, hrd, ha, hs, hr, hcl⟩ := hC j pc p acq sc hj' hcount
  refine ⟨pcr, a, bs, rr, ?_, ha, hs, hr, hcl⟩
  have hlt1 : j + 1 < es.length := (List.getElem?_eq_some_iff.mp hrd).1
  rw [List.getElem?_append_left hlt1]
  exact hrd

/-- The counting invariant of an MMA state `d` after the events `es`. Besides the input-ring counts
and the accumulator counts, it keeps the response: the task's blocks against the response polls,
the response the state holds with its read, and the exit's claim. -/
structure Counts (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  /-- The commits to each slot's empty barrier, with the pending commit, are its full polls. -/
  commit : ∀ s : Fin 4, es.countP (commitsTo (emptyAt L g s)) +
    (if pendingCommit d s then 1 else 0) = okPolls (fullOf L g s) es
  /-- The full polls have the parity of the trip (`polledFull`). -/
  full : d.site.done = false → ∀ s : Fin 4, okPolls (fullOf L g s) es % 2 = polledFull d s % 2
  /-- The accumulator commits, with the held accumulator, are the accumulator polls. -/
  acc : ∀ j, j < 2 → es.countP (commitsTo (accBar L g j true)) +
    (if j = d.w % 2 then holdsAcc d else 0) = okPolls (accBar L g j false) es
  /-- The accumulator commits of the thread's own buffer, with the accumulator commit it is making,
  are its commits to the input empty barriers over 128: one accumulator per completed task. -/
  accRound : es.countP (commitsTo (accBar L g (d.w % 2) true)) +
    (if d.site = .accCommit then 1 else 0) = mcount L g es / 128
  /-- The accumulator polls have the parity after the held accumulator. -/
  accPar : d.site ≠ .elect → d.site.done = false →
    okPolls (accBar L g (d.w % 2) false) es % 2 = (d.ap + 1 + holdsAcc d) % 2
  /-- Before the election the thread has no event but the prologue's. -/
  elect : d.site = .elect → Quiet es
  /-- The commits go round the four slots. -/
  rank : ∀ s : Fin 4, es.countP (commitsTo (emptyAt L g s)) = (mcount L g es + 3 - s.val) / 4
  /-- The site fixes the commits modulo the task. -/
  cond : MmaCond d (mcount L g es)
  /-- The K block is a multiple of four. -/
  q4 : d.q % 4 = 0
  /-- A started task is 128 blocks, less the trip's position. -/
  task : 128 * okPolls (respBar L g) es + taskPos d = mcount L g es + 128 * taskStarted d
  /-- A state that reads the response has polled it last. -/
  polled : d.site = .clcLoad → ∃ e' p acq sc, es.getLast? = some e' ∧
    e'.kind = .wait (respBar L g) p true acq sc
  /-- After a response poll, the state holds the response of the latest poll and its read. -/
  held : d.site ≠ .clcLoad → 0 < okPolls (respBar L g) es → ∃ rr, d.resp = .clc rr ∧
    HeldRead L g es rr ∧ (d.site ≠ .clcStatus → d.site ≠ .clcFirst → d.x = firstOf rr) ∧
    (d.site.done = true → d.x = Loader.none32)
  /-- A state past the task loop has polled the response or lost the election. -/
  exitPoll : d.site.done = true → 0 < okPolls (respBar L g) es ∨ Loader.leader L g = false ∨
    ∃ e ∈ es, ∃ mask inst l, e.kind = .elect mask inst l ∧ l ≠ laneOf L g
  /-- At the CLC poll after a response poll, the state's first CTA is the previous task's, which
  claims. -/
  entryX : d.site = .clcWait → 0 < okPolls (respBar L g) es → d.x ≠ Loader.none32
  /-- A successful response poll that is not the latest one is followed by a read that claims a
  CTA. -/
  claimsBefore : ∀ j pc p acq sc, es[j]? = some ⟨pc, .wait (respBar L g) p true acq sc⟩ →
    okPolls (respBar L g) (es.take j) + 1 < okPolls (respBar L g) es → CbReadClaims L g es (j + 1)

/-- A successful response poll at the CLC poll site: the earlier latest poll's read claims a CTA,
since
the state holds the first CTA of its response and that CTA is not none. -/
theorem claimsBefore_snoc_poll {L : Launch} {g : Nat} {m : D} {pre : List Event}
    (hC : Counts L g m pre) (hm : m.site = .clcWait)
    (e : Event) (hok : okPoll (respBar L g) e = true) :
    ∀ j pc' p' acq' sc', (pre ++ [e])[j]? = some ⟨pc', .wait (respBar L g) p' true acq' sc'⟩ →
      okPolls (respBar L g) ((pre ++ [e]).take j) + 1 < okPolls (respBar L g) (pre ++ [e]) →
      CbReadClaims L g (pre ++ [e]) (j + 1) := by
  intro j pc' p' acq' sc' hj hcount
  have hokS : okPolls (respBar L g) (pre ++ [e]) = okPolls (respBar L g) pre + 1 := by
    rw [okPolls_snoc, hok]; simp
  have hlen : j < (pre ++ [e]).length := (List.getElem?_eq_some_iff.mp hj).1
  have hjlt : j < pre.length := by
    by_contra hge
    have hjeq : j = pre.length := by simp at hlen; omega
    subst hjeq
    rw [List.take_append_of_le_length le_rfl, List.take_length, hokS] at hcount
    omega
  have hj' : pre[j]? = some ⟨pc', .wait (respBar L g) p' true acq' sc'⟩ := by
    rw [← List.getElem?_append_left hjlt]; exact hj
  have htake : (pre ++ [e]).take j = pre.take j := List.take_append_of_le_length hjlt.le
  rw [htake, hokS] at hcount
  have hpos : 0 < okPolls (respBar L g) pre := by omega
  obtain ⟨rr, hres, hHR, hxr, -⟩ := hC.held (by rw [hm]; simp) hpos
  obtain ⟨j0, pc0, p0, acq0, sc0, pcr0, a0, bs0, hj0, hrd0, ha0, hs0, hr0, hcnt0⟩ := hHR
  rcases Nat.lt_or_ge (okPolls (respBar L g) (pre.take j) +
    1) (okPolls (respBar L g) pre) with hlt | hge
  · obtain ⟨pcr, a, bs, rr', hrd, ha, hs, hr, hcl⟩ :=
      hC.claimsBefore j pc' p' acq' sc' hj' hlt
    refine ⟨pcr, a, bs, rr', ?_, ha, hs, hr, hcl⟩
    have hlt1 : j + 1 < pre.length := (List.getElem?_eq_some_iff.mp hrd).1
    rw [List.getElem?_append_left hlt1]
    exact hrd
  · have heq : okPolls (respBar L g) (pre.take j) = okPolls (respBar L g) (pre.take j0) := by
      omega
    have hjj0 : j = j0 :=
      cbPoll_index_eq hj' (by simp [okPoll, sourceWaitSuccess]) hj0
        (by simp [okPoll, sourceWaitSuccess]) heq
    subst hjj0
    have hxne := hC.entryX hm hpos
    have hxf := hxr (by rw [hm]; simp) (by rw [hm]; simp)
    have hf : firstOf rr ≠ Loader.none32 := by
      rw [← hxf]; exact hxne
    refine ⟨pcr0, a0, bs0, rr, ?_, ha0, hs0, hr0, hf⟩
    have hlt1 : j + 1 < pre.length := (List.getElem?_eq_some_iff.mp hrd0).1
    rw [List.getElem?_append_left hlt1]
    exact hrd0

/-- An event that polls no barrier and commits to none: no count of the MMA thread moves on it. -/
def NoCount (e : Event) : Prop := ∀ m : Loc, okPoll m e = false ∧ commitsTo m e = false

theorem noCount_of_other {e : Event}
    (h : (∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc) ∧ ∀ sp, e.kind ≠ .tc (.commit sp)) :
    NoCount e :=
  fun _ => ⟨okPoll_notWait h.1, commitsTo_of_notCommit h.2⟩

theorem noCount_of_wait_false {l : Loc} {e : Event} {p : Nat} {acq : Bool} {sc : MbarScope}
    (he : e.kind = .wait l p false acq sc) : NoCount e :=
  fun m => ⟨by rw [okPoll_of_wait he]; simp, commitsTo_of_wait he⟩

/-- A step from a plain site that polls no response barrier keeps the held response. -/
theorem held_keep {m m' : D} {pre : List Event} {e : Event} (hC : Counts L g m pre)
    (hR : okPoll (respBar L g) e = false) (hpm : m.site.Plain := by simp [Site.Plain, Site.done])
    (hd' : m'.site.done = false := by simp [Site.done]) (hr : m'.resp = m.resp := by rfl)
    (hx : m'.x = m.x := by rfl) :
    m'.site ≠ .clcLoad → 0 < okPolls (respBar L g) (pre ++ [e]) → ∃ rr,
      m'.resp = .clc rr ∧ HeldRead L g (pre ++ [e]) rr ∧
      (m'.site ≠ .clcStatus → m'.site ≠ .clcFirst → m'.x = firstOf rr) ∧
      (m'.site.done = true → m'.x = Loader.none32) := by
  intro _ hpos
  have hpos' : 0 < okPolls (respBar L g) pre := by simpa [okPolls_snoc, hR] using hpos
  obtain ⟨rr, hr0, hH0, hx0, -⟩ := hC.held hpm.2.1 hpos'
  exact ⟨rr, hr.trans hr0, HeldRead.snoc hH0 hR,
    fun _ _ => hx.trans (hx0 hpm.2.2.1 hpm.2.2.2.1), fun h => by rw [hd'] at h; cases h⟩

/-- An event that commits to no accumulator and changes no input commit count keeps the accumulator
round, when neither state is an accumulator commit. -/
theorem accRound_frame {m m' : D} {pre : List Event} {e : Event} (hC : Counts L g m pre)
    (hm : m.site ≠ .accCommit) (hm' : m'.site ≠ .accCommit) (hw : m'.w = m.w)
    (hA : ∀ j, j < 2 → commitsTo (accBar L g j true) e = false)
    (hM : mcount L g (pre ++ [e]) = mcount L g pre) :
    (pre ++ [e]).countP (commitsTo (accBar L g (m'.w % 2) true)) +
      (if m'.site = .accCommit then 1 else 0) = mcount L g (pre ++ [e]) / 128 := by
  have h := hC.accRound
  rw [hw, countP_snoc_none (hA _ (Nat.mod_lt _ (by decide))), hM]
  simp only [hm, hm', ↓reduceIte, Nat.add_zero] at h ⊢
  exact h

/-- One more event `e` of an MMA run: each count moves by the event's own delta, and the new state's
counted facts follow from the old ones; the trivial side conditions default to their tactics. -/
theorem Counts.step {m m' : D} {pre : List Event} {e : Event} (hC : Counts L g m pre)
    (hp : ∀ s : Fin 4, (if pendingCommit m' s then 1 else 0) +
      (if commitsTo (emptyAt L g s) e then 1 else 0) =
      (if pendingCommit m s then 1 else 0) + if okPoll (fullOf L g s) e then 1 else 0)
    (hf : m'.site.done = false → ∀ s : Fin 4,
      (polledFull m s + if okPoll (fullOf L g s) e then 1 else 0) % 2 = polledFull m' s % 2)
    (hh : ∀ j, j < 2 → (if commitsTo (accBar L g j true) e then 1 else 0) +
      (if j = m.w % 2 then holdsAcc m' else 0) =
      (if okPoll (accBar L g j false) e then 1 else 0) + if j = m.w % 2 then holdsAcc m else 0)
    (ha : m'.site.done = false → (m.ap + 1 + holdsAcc m +
      if okPoll (accBar L g (m.w % 2) false) e then 1 else 0) % 2 = (m'.ap + 1 + holdsAcc m') % 2)
    (hr : ∀ s : Fin 4, (pre ++ [e]).countP (commitsTo (emptyAt L g s)) =
      (mcount L g (pre ++ [e]) + 3 - s.val) / 4)
    (hcond : MmaCond m' (mcount L g (pre ++ [e])))
    (hq4 : m'.q % 4 = 0)
    (ht : 128 * okPolls (respBar L g) (pre ++ [e]) + taskPos m' =
      mcount L g (pre ++ [e]) + 128 * taskStarted m')
    (hH : m'.site ≠ .clcLoad → 0 < okPolls (respBar L g) (pre ++ [e]) → ∃ rr,
      m'.resp = .clc rr ∧ HeldRead L g (pre ++ [e]) rr ∧
      (m'.site ≠ .clcStatus → m'.site ≠ .clcFirst → m'.x = firstOf rr) ∧
      (m'.site.done = true → m'.x = Loader.none32))
    (hm : m.site ≠ .elect := by simp) (hm' : m'.site ≠ .elect := by simp)
    (hd : m'.site.done = false → m.site.done = false := by simp [Site.done])
    (hw : m'.w = m.w := by rfl)
    (hP : m'.site = .clcLoad → ∃ e' p acq sc, (pre ++ [e]).getLast? = some e' ∧
      e'.kind = .wait (respBar L g) p true acq sc := by intro h; simp at h)
    (hE : m'.site.done = true → 0 < okPolls (respBar L g) (pre ++ [e]) ∨
      Loader.leader L g = false ∨ ∃ e' ∈ pre ++ [e], ∃ mask inst l,
        e'.kind = .elect mask inst l ∧ l ≠ laneOf L g := by intro h; simp [Site.done] at h)
    (hAR : (pre ++ [e]).countP (commitsTo (accBar L g (m'.w % 2) true)) +
      (if m'.site = .accCommit then 1 else 0) = mcount L g (pre ++ [e]) / 128)
    (hEX : m'.site = .clcWait → 0 < okPolls (respBar L g) (pre ++ [e]) → m'.x ≠ Loader.none32 := by
      intro h; simp at h)
    (hCB : ∀ j pc p acq sc, (pre ++ [e])[j]? = some ⟨pc, .wait (respBar L g) p true acq sc⟩ →
      okPolls (respBar L g) ((pre ++ [e]).take j) + 1 < okPolls (respBar L g) (pre ++ [e]) →
      CbReadClaims L g (pre ++ [e]) (j + 1)) :
    Counts L g m' (pre ++ [e]) :=
  { commit := fun s => by
      rw [commits_snoc, okPolls_snoc]
      have h1 := hC.commit s
      have h2 := hp s
      omega
    full := fun hd' s => by
      rw [okPolls_snoc]
      have h1 := hC.full (hd hd') s
      have h2 := hf hd' s
      omega
    acc := fun j hj => by
      rw [commits_snoc, okPolls_snoc, hw]
      have h1 := hC.acc j hj
      have h2 := hh j hj
      omega
    accPar := fun _ hd' => by
      rw [okPolls_snoc, hw]
      have h1 := hC.accPar hm (hd hd')
      have h2 := ha hd'
      omega
    elect := fun h => absurd h hm'
    rank := hr
    cond := hcond
    q4 := hq4
    task := ht
    polled := hP
    held := hH
    exitPoll := hE
    accRound := hAR
    entryX := hEX
    claimsBefore := hCB }

/-- A `NoCount` event between plain sites keeps the response, the first CTA and the counted
facts. -/
theorem Counts.frame {m m' : D} {pre : List Event} {e : Event} (hC : Counts L g m pre)
    (hS : NoCount e) (hq4 : m'.q % 4 = 0)
    (hpm : m.site.Plain := by simp [Site.Plain, Site.done])
    (hpm' : m'.site.Plain := by simp [Site.Plain, Site.done])
    (hp : ∀ s : Fin 4, pendingCommit m' s = pendingCommit m s := by
      intro s; simp [pendingCommit])
    (hf : ∀ s : Fin 4, polledFull m' s = polledFull m s := by intro s; simp [polledFull, past])
    (hh : holdsAcc m' = holdsAcc m := by rfl) (hw : m'.w = m.w := by rfl)
    (ha : m'.ap = m.ap := by rfl)
    (ht : taskPos m' = taskPos m ∧ taskStarted m' = taskStarted m := by constructor <;> rfl)
    (hr : m'.resp = m.resp := by rfl) (hx : m'.x = m.x := by rfl)
    (hcond : MmaCond m' (mcount L g pre) := by simpa [MmaCond] using hC.cond)
    (hm : m.site ≠ .accCommit := by simp) (hm' : m'.site ≠ .accCommit := by simp)
    (hEXf : m'.site = .clcWait → 0 < okPolls (respBar L g) (pre ++ [e]) → m'.x ≠ Loader.none32 := by
      intro h; simp at h) :
    Counts L g m' (pre ++ [e]) := by
  have h0 : ∀ l : Loc, okPoll l e = false := fun l => (hS l).1
  have h0' : ∀ l : Loc, commitsTo l e = false := fun l => (hS l).2
  have hM : mcount L g (pre ++ [e]) = mcount L g pre := mcount_snoc_none fun _ => h0' _
  refine Counts.step hC (fun s => by simp [h0, h0', hp s]) (fun _ s => by simp [h0, hf s])
    (fun j _ => by simp [h0, h0', hh]) (fun _ => by simp [h0, ha, hh])
    (fun s => by rw [countP_snoc_none (h0' _), hM]; exact hC.rank s)
    (by rw [hM]; exact hcond) hq4
    (by rw [okPolls_snoc, h0, hM, ht.1, ht.2]; simp only [Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero]; exact hC.task)
    (held_keep hC (h0 _) hpm hpm'.2.2.2.2 hr hx)
    (hm := hpm.1) (hm' := hpm'.1) (hd := fun _ => hpm.2.2.2.2) (hw := hw)
    (hP := fun h => absurd h hpm'.2.1)
    (hE := fun h => by rw [hpm'.2.2.2.2] at h; cases h)
    (hAR := accRound_frame hC hm hm' hw (fun j _ => (hS _).2) hM)
    (hCB := claimsBefore_snoc_no hC.claimsBefore (h0 (respBar L g)))
    (hEX := hEXf)

/-- The counts of a state after a quiet history, when its counted data is zero. -/
theorem counts_quiet {m : D} {es : List Event} (hQ : Quiet es)
    (hs : m.site = .clcWait ∧ m.fp = 0 ∧ m.ap = 1 ∨ m.site = .exitArrive ∨ m.site = .elect)
    (hq : m.q % 4 = 0)
    (hx : m.site.done = true → Loader.leader L g = false ∨ ∃ e ∈ es, ∃ mask inst l,
      e.kind = .elect mask inst l ∧ l ≠ laneOf L g) : Counts L g m es := by
  have h0 : ∀ s : Fin 4, es.countP (commitsTo (emptyAt L g s)) = 0 := fun s => (hQ _).2.2.1
  have hF : ∀ s : Fin 4, okPolls (fullOf L g s) es = 0 := fun s => (hQ _).1
  have hA : ∀ j, okPolls (accBar L g j false) es = 0 := fun j => (hQ _).1
  have hAc : ∀ j, es.countP (commitsTo (accBar L g j true)) = 0 := fun j => (hQ _).2.2.1
  have hO : okPolls (respBar L g) es = 0 := (hQ _).1
  have hM : mcount L g es = 0 := Finset.sum_eq_zero fun s _ => h0 s
  have hpend : ∀ s, pendingCommit m s = false := fun s => by
    rcases hs with ⟨h, -⟩ | h | h <;> simp [pendingCommit, h]
  have hhold : holdsAcc m = 0 := by rcases hs with ⟨h, -⟩ | h | h <;> simp [holdsAcc, h]
  have hpf : ∀ s : Fin 4, m.site.done = false → polledFull m s % 2 = 0 := by
    intro s hd
    rcases hs with ⟨h, hfp, -⟩ | h | h
    · simp [polledFull, past, h, hfp]
    · simp [Site.done, h] at hd
    · simp [polledFull, h]
  exact
    { commit := fun s => by rw [h0 s, hpend s, hF s]; simp
      full := fun hd s => by rw [hF s, hpf s hd]
      acc := fun j _ => by rw [hAc j, hhold, hA j]; simp
      accPar := fun hne hd => by
        rw [hA _, hhold]
        rcases hs with ⟨h, -, hap⟩ | h | h
        · simp [hap]
        · simp [Site.done, h] at hd
        · exact absurd h hne
      elect := fun _ => hQ
      rank := fun s => by rw [h0 s, hM]; have := s.isLt; omega
      cond := by rw [hM]; rcases hs with ⟨h, -, -⟩ | h | h <;> simp [MmaCond, h]
      q4 := hq
      task := by
        rw [hO, hM]
        rcases hs with ⟨h, -, -⟩ | h | h <;> simp [taskPos, taskStarted, h]
      polled := fun h => by
        rcases hs with ⟨h', -, -⟩ | h' | h' <;> simp [h'] at h
      held := fun _ hpos => by rw [hO] at hpos; omega
      exitPoll := fun hd => Or.inr (hx hd)
      accRound := by rw [hAc, hM]; rcases hs with ⟨h, -, -⟩ | h | h <;> simp [h]
      entryX := fun _ hpos => by rw [hO] at hpos; omega
      claimsBefore := fun _ _ _ _ _ _ hcount => by rw [hO] at hcount; omega }

/-- One step of an MMA run keeps the counting invariant, by cases on the site (`site_event`). -/
theorem counts_step {t : TState} {ins : Instr} {m m' : D} {pre : List Event} {e : Event}
    {o : Option TState} (hpre : Pre P L mem0) (hg : g < L.threads) (hi : Inv m) (hq : QReset m)
    (hC : Counts L g m pre) (hat : At t m.site.pc (facts L g m))
    (hc : kernel.code[m.site.pc]? = some ins)
    (hfire : Fires m.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next L g m e = some (some m')) : Counts L g m' (pre ++ [e]) := by
  have hF := site_event hpre hg hi hat hc hfire
  have hq4 : m.q % 4 = 0 := hi.q4
  have hfp : m.fp < 2 := hi.fp
  have hap : m.ap < 2 := hi.ap
  have hq128 : m.q < 128 := hi.q
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  simp only at hq4 hfp hap hq128 hC hq hF hn hat
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  cases site with
  | elect =>
    obtain ⟨a, b, c, hk⟩ := elect_kind rfl hn
    have hnot : ¬ ObjectKind e.kind := by rw [hk]; exact fun h => h
    have hQ' : Quiet (pre ++ [e]) := Quiet.snoc (hC.elect rfl) fun l => quiet_of_kind hnot l
    simp only [next, hk] at hn
    split_ifs at hn with hl
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact counts_quiet hQ' (Or.inl ⟨rfl, rfl, rfl⟩) rfl (fun h => absurd h (by simp [Site.done]))
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact counts_quiet hQ' (Or.inr (Or.inl rfl)) hq4 fun _ =>
        Or.inr ⟨e, List.mem_append_right _ (List.mem_singleton.mpr rfl), a, b, c, hk,
          fun h => hl h.symm⟩
  | clcWait =>
    simp only [FiresAt] at hF
    obtain ⟨p, ok, acq, sc, he⟩ := hF
    simp only [next, he] at hn
    cases ok
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact Counts.frame hC (noCount_of_wait_false he) hq4 (hEXf := fun _ hp =>
        hC.entryX rfl (by rw [okPolls_snoc, okPoll_of_wait he] at hp; simpa using hp))
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      have hne : ∀ s : Fin 4, (⟨.shared, g / L.block, L.sharedBase + 104⟩ : Loc) ≠ fullOf L g s :=
        fun s => loc_ne (by simp only; have := s.isLt; omega)
      have hne' : ∀ j, j < 2 → (⟨.shared, g / L.block, L.sharedBase + 104⟩ : Loc) ≠
          accBar L g j false := fun j hj => loc_ne (by rw [accBar_eq]; simp only; omega)
      have hF0 : ∀ s : Fin 4, okPoll (fullOf L g s) e = false := fun s => by
        rw [okPoll_of_wait he]; simp [hne s]
      have hA0 : ∀ j, j < 2 → okPoll (accBar L g j false) e = false := fun j hj => by
        rw [okPoll_of_wait he]; simp [hne' j hj]
      have hok : okPoll (respBar L g) e = true := by rw [okPoll_of_wait he, respBar_eq]; simp
      have hM : mcount L g (pre ++ [e]) = mcount L g pre :=
        mcount_snoc_none fun _ => commitsTo_of_wait he
      refine Counts.step (hEX := fun h => absurd h (by simp)) (hCB :=
        claimsBefore_snoc_poll hC rfl e (by rw [okPoll_of_wait he, respBar_eq]; simp)) (hAR :=
          accRound_frame hC (by simp) (by simp) rfl (fun j _ =>
            commitsTo_of_wait he) hM) hC (fun s => by simp [pendingCommit, commitsTo_of_wait he,
              hF0 s])
        (fun _ s => by simp [polledFull, past, hF0 s])
        (fun j hj => by simp [holdsAcc, commitsTo_of_wait he, hA0 j hj])
        (fun _ => by simp [holdsAcc, hA0 (w % 2) (Nat.mod_lt _ (by decide))])
        (fun s => by rw [countP_snoc_none (commitsTo_of_wait he), hM]; exact hC.rank s)
        (by rw [hM]; simpa [MmaCond] using hC.cond) hq4
        (by rw [okPolls_snoc, hok, hM]; have := hC.task; simp [taskPos, taskStarted] at this ⊢
            omega)
        (fun h => (h (by simp)).elim)
        (hP := fun _ => ⟨e, p, acq, sc, by simp, by rw [he, respBar_eq]⟩)
  | clcLoad =>
    simp only [FiresAt] at hF
    code_at hc
    subst hc
    have hr : t.regs 851 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by mma_values))
    rcases fires_ldAcquire_kind hfire with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · obtain ⟨ha, hs⟩ := (fires_ldAcquire128 (effAddr_b32 hr (by omega)) hat.2.1 hfire) a bs hk
      simp only [next] at hn
      rw [hk] at hn
      simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      obtain ⟨pe, p, acq, sc, hl, hpe⟩ := hC.polled rfl
      have hS := noCount_of_other hF
      have h0 : ∀ l : Loc, okPoll l e = false := fun l => (hS l).1
      have h0' : ∀ l : Loc, commitsTo l e = false := fun l => (hS l).2
      have hM : mcount L g (pre ++ [e]) = mcount L g pre := mcount_snoc_none fun _ => h0' _
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore (h0 _)) (hAR :=
        accRound_frame hC (by simp) (by simp) rfl (fun j _ => h0' _) hM) hC (fun s => by
          simp [pendingCommit, h0, h0'])
        (fun _ s => by simp [polledFull, past, h0])
        (fun j _ => by simp [holdsAcc, h0, h0']) (fun _ => by simp [holdsAcc, h0])
        (fun s => by rw [countP_snoc_none (h0' _), hM]; exact hC.rank s)
        (by rw [hM]; simpa [MmaCond] using hC.cond) hq4
        (by rw [okPolls_snoc, h0, hM]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            have := hC.task; simp [taskPos, taskStarted] at this ⊢; omega)
        (fun _ _ => ⟨rr, rfl, HeldRead.of_read hl hpe hk ha hs hrr, fun h _ => absurd rfl h,
          fun h => absurd h (by simp [Site.done])⟩)
    · simp only [next] at hn
      rw [hk] at hn
      simp at hn
  | clcStatus =>
    simp only [FiresAt] at hF
    code_at hc
    subst hc
    have hl8 : 975 ∈ Flow.live Site.clcStatus.pc := by table_decide
    obtain ⟨q', r', hk⟩ : ∃ q' r', e.kind = .clcQuery q' r' := by
      cases hk : e.kind with
      | clcQuery q' r' => exact ⟨q', r', rfl⟩
      | _ => simp [next, hk] at hn
    simp only [next, hk, Option.some.injEq] at hn
    subst hn
    have hS := noCount_of_other hF
    have h0 : ∀ l : Loc, okPoll l e = false := fun l => (hS l).1
    have h0' : ∀ l : Loc, commitsTo l e = false := fun l => (hS l).2
    have hM : mcount L g (pre ++ [e]) = mcount L g pre := mcount_snoc_none fun _ => h0' _
    have hpos : 0 < okPolls (respBar L g) pre := by
      have := hC.task
      simp only [taskPos, taskStarted] at this
      omega
    obtain ⟨rr, hr0, hH0, hx0, -⟩ := hC.held (by simp) hpos
    have hr8 : t.regs 975 = some (.clc rr) := (rq8_of_at hat hl8).trans (congrArg some hr0)
    have hpay : r' = rr := fires_clcQuery_value hr8 hfire q' r' hk
    by_cases hfi : r'.firstCta.isSome = true
    · simp only [hfi, ↓reduceIte]
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
        (okPoll_notWait (fun l p ok acq sc => by rw [hk]; simp))) (hAR :=
          accRound_frame hC (by simp) (by simp) rfl (fun j _ => h0' _) hM) hC (fun s => by
            simp [pendingCommit, h0, h0'])
        (fun _ s => by simp [polledFull, past, h0])
        (fun j _ => by simp [holdsAcc, h0, h0']) (fun _ => by simp [holdsAcc, h0])
        (fun s => by rw [countP_snoc_none (h0' _), hM]; exact hC.rank s)
        (by rw [hM]; simpa [MmaCond] using hC.cond) hq4
        (by rw [okPolls_snoc, h0, hM]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            have := hC.task; simp [taskPos, taskStarted] at this ⊢; omega)
        (fun _ _ => ⟨rr, hr0, HeldRead.snoc hH0 (h0 _), fun _ h => absurd rfl h,
          fun h => absurd h (by simp [Site.done])⟩)
    · simp only [hfi]
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
        (okPoll_notWait (fun l p ok acq sc => by rw [hk]; simp))) (hAR :=
          accRound_frame hC (by simp) (by simp) rfl (fun j _ => h0' _) hM) hC (fun s => by
            simp [pendingCommit, h0, h0'])
        (fun _ s => by simp [polledFull, past, h0])
        (fun j _ => by simp [holdsAcc, h0, h0']) (fun _ => by simp [holdsAcc, h0])
        (fun s => by rw [countP_snoc_none (h0' _), hM]; exact hC.rank s)
        (by rw [hM]; simpa [MmaCond] using hC.cond) hq4
        (by rw [okPolls_snoc, h0, hM]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            have := hC.task; simp [taskPos, taskStarted] at this ⊢; omega)
        (fun _ _ => ⟨rr, hr0, HeldRead.snoc hH0 (h0 _), fun _ _ =>
          (firstOf_of_not (hpay ▸ hfi)).symm,
          fun h => absurd h (by simp [Site.done])⟩)
  | clcFirst =>
    simp only [FiresAt] at hF
    code_at hc
    subst hc
    have hl8 : 975 ∈ Flow.live Site.clcFirst.pc := by table_decide
    obtain ⟨q', r', hk⟩ : ∃ q' r', e.kind = .clcQuery q' r' := by
      cases hk : e.kind with
      | clcQuery q' r' => exact ⟨q', r', rfl⟩
      | _ => simp [next, hk] at hn
    simp only [next, hk, Option.some.injEq] at hn
    subst hn
    have hS := noCount_of_other hF
    have h0 : ∀ l : Loc, okPoll l e = false := fun l => (hS l).1
    have h0' : ∀ l : Loc, commitsTo l e = false := fun l => (hS l).2
    have hM : mcount L g (pre ++ [e]) = mcount L g pre := mcount_snoc_none fun _ => h0' _
    have hpos : 0 < okPolls (respBar L g) pre := by
      have := hC.task
      simp only [taskPos, taskStarted] at this
      omega
    obtain ⟨rr, hr0, hH0, -, -⟩ := hC.held (by simp) hpos
    have hr8 : t.regs 975 = some (.clc rr) := (rq8_of_at hat hl8).trans (congrArg some hr0)
    have hpay : r' = rr := fires_clcQuery_value hr8 hfire q' r' hk
    refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
      (okPoll_notWait (fun l p ok acq sc => by rw [hk]; simp))) (hAR :=
        accRound_frame hC (by simp) (by simp) rfl (fun j _ => h0' _) hM) hC (fun s => by
          simp [pendingCommit, h0, h0'])
      (fun _ s => by simp [polledFull, past, h0])
      (fun j _ => by simp [holdsAcc, h0, h0']) (fun _ => by simp [holdsAcc, h0])
      (fun s => by rw [countP_snoc_none (h0' _), hM]; exact hC.rank s)
      (by rw [hM]; simpa [MmaCond] using hC.cond) hq4
      (by rw [okPolls_snoc, h0, hM]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          have := hC.task; simp [taskPos, taskStarted] at this ⊢; omega)
      (fun _ _ => ⟨rr, hr0, HeldRead.snoc hH0 (h0 _), fun _ _ => by rw [hpay]; rfl,
        fun h => absurd h (by simp [Site.done])⟩)
  | clcFence | ack =>
    simp only [FiresAt] at hF
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact Counts.frame hC (noCount_of_other hF) (by simp [hq4])
  | accWait =>
    simp only [FiresAt] at hF
    obtain ⟨ok, acq, sc, he⟩ := hF
    have hR : okPoll (respBar L g) e = false := by
      rw [okPoll_of_wait he, decide_eq_false (accBar_ne_respBar (Nat.mod_lt w (by decide))),
        Bool.and_false]
    simp only [next, he] at hn
    cases ok
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact Counts.frame hC (noCount_of_wait_false he) hq4
    · -- the accumulator is taken: the trip starts at its first slot
      obtain rfl := Option.some.inj (Option.some.inj hn)
      have hq0 : q = 0 := hq (Or.inr rfl)
      have hA : ∀ j, okPoll (accBar L g j false) e = decide (j = w % 2) := fun j => by
        rw [okPoll_of_wait he, Bool.true_and]
        exact decide_eq_decide.mpr (accBar_inj.trans eq_comm)
      have hF0 : ∀ s : Fin 4, okPoll (fullOf L g s) e = false := fun s => by
        rw [okPoll_of_wait he, Bool.true_and]
        exact decide_eq_false (loc_ne (by rw [accBar_eq]; simp only; have := s.isLt; omega))
      have hM : mcount L g (pre ++ [e]) = mcount L g pre :=
        mcount_snoc_none fun _ => commitsTo_of_wait he
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
          (by rw [okPoll_of_wait he, Bool.true_and];
              exact decide_eq_false (loc_ne
                (by rw [respBar_eq, accBar_eq]; simp only; omega))))
            (hAR := accRound_frame hC (by simp) (by simp) rfl (fun j _ =>
              commitsTo_of_wait he) hM) hC (fun s => by simp [pendingCommit, commitsTo_of_wait he,
                hF0 s])
        (fun _ s => by simp [polledFull, past, hF0 s])
        (fun j _ => by simp [holdsAcc, commitsTo_of_wait he, hA j])
        (fun _ => by simp [holdsAcc, hA (w % 2)])
        (fun s => by rw [countP_snoc_none (commitsTo_of_wait he), hM]; exact hC.rank s)
        (by rw [hM]; have hc := hC.cond; simp [MmaCond] at hc ⊢; omega)
        (by show q % 4 = 0; exact hq4)
        (by rw [okPolls_snoc, hR, hM]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            have := hC.task; simp only [taskPos, taskStarted, hq0] at this ⊢; omega)
        (held_keep hC hR)
  | full s0 =>
    simp only [FiresAt] at hF
    obtain ⟨ok, acq, sc, he⟩ := hF
    have hR : okPoll (respBar L g) e = false := by
      rw [okPoll_of_wait he, decide_eq_false (fullOf_ne_respBar s0), Bool.and_false]
    simp only [next, he] at hn
    cases ok
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      exact Counts.frame hC (noCount_of_wait_false he) hq4
    · -- the slot's full poll succeeds: its four MMAs follow
      obtain rfl := Option.some.inj (Option.some.inj hn)
      have hF1 : ∀ s : Fin 4, okPoll (fullOf L g s) e = decide (s0 = s) := fun s => by
        rw [okPoll_of_wait he, Bool.true_and]
        exact decide_eq_decide.mpr fullOf_eq
      have hA0 : ∀ j, j < 2 → okPoll (accBar L g j false) e = false := fun j _ => by
        rw [okPoll_of_wait he, Bool.and_eq_false_iff]
        right
        exact decide_eq_false (loc_ne (by rw [accBar_eq]; simp only; omega))
      have hM : mcount L g (pre ++ [e]) = mcount L g pre :=
        mcount_snoc_none fun _ => commitsTo_of_wait he
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
          (by rw [okPoll_of_wait he, Bool.true_and];
              exact decide_eq_false (fun h => fullOf_ne_respBar s0 h)))
          (hAR := accRound_frame hC (by simp) (by simp) rfl (fun j _ =>
            commitsTo_of_wait he) hM) hC (fun s => by simp [pendingCommit, commitsTo_of_wait he,
              hF1 s])
        (fun _ s => by
          have := s.isLt
          simp [polledFull, past, hF1 s]
          split_ifs <;> omega)
        (fun j hj => by simp [holdsAcc, commitsTo_of_wait he, hA0 j hj])
        (fun _ => by simp [holdsAcc, hA0 (w % 2) (Nat.mod_lt _ (by decide))])
        (fun s => by rw [countP_snoc_none (commitsTo_of_wait he), hM]; exact hC.rank s)
        (by rw [hM]; simpa [MmaCond] using hC.cond) hq4
        (by rw [okPolls_snoc, hR, hM]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            have := hC.task; simp [taskPos, taskStarted] at this ⊢; omega)
        (held_keep hC hR)
  | mma s0 j0 =>
    simp only [FiresAt] at hF
    simp only [next] at hn
    split at hn <;> obtain rfl := Option.some.inj (Option.some.inj hn) <;>
      exact Counts.frame hC (noCount_of_other hF) hq4
  | commit s0 =>
    simp only [FiresAt] at hF
    have h1 : ∀ j, j < 2 → commitsTo (accBar L g j true) e = false := fun j _ => by
      rw [commitsTo_of_kind hF]
      exact decide_eq_false (loc_ne (by
        simp only [commitSpec, accBar, Bar.loc, Bar.off]
        have := s0.isLt
        omega))
    have h2 : ∀ s : Fin 4, okPoll (fullOf L g s) e = false := fun s => okPoll_of_kind hF
    have h3 : ∀ j, j < 2 → okPoll (accBar L g j false) e = false := fun j _ => okPoll_of_kind hF
    have hOk : okPoll (respBar L g) e = false := okPoll_of_kind hF
    have hM : mcount L g (pre ++ [e]) = mcount L g pre + 1 :=
      mcount_snoc (fun s => countP_snoc_commit hF s)
    have hsl := s0.isLt
    have hO : 0 < okPolls (respBar L g) pre := by
      have := hC.task
      simp only [taskPos, taskStarted] at this
      omega
    have hMod : mcount L g pre % 4 = s0.val := by
      have hc := hC.cond
      simp only [MmaCond] at hc
      omega
    have hrank : ∀ s : Fin 4, (pre ++ [e]).countP (commitsTo (emptyAt L g s)) =
        (mcount L g (pre ++ [e]) + 3 - s.val) / 4 := fun s => by
      rw [countP_snoc_commit hF s, hM, hC.rank s]
      exact (rr_succ hMod s).symm
    have hcs : ∀ s : Fin 4, commitsTo (emptyAt L g s) e = decide (s0 = s) := fun s =>
      commitsTo_of_commitSpec hF
    have hA : okPoll (accBar L g (w % 2) false) e = false := h3 _ (Nat.mod_lt _ (by decide))
    simp only [next] at hn
    by_cases hl : s0.val + 1 < 4
    · simp only [hl, ↓reduceDIte] at hn
      obtain rfl := Option.some.inj (Option.some.inj hn)
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
        (okPoll_notWait (fun l p ok acq sc => by simp_all))) (hAR := by
          have hc := hC.cond; have hr := hC.accRound;
          rw [countP_snoc_none (h1 _ (Nat.mod_lt _ (by decide))), hM];
          simp [MmaCond] at hc hr ⊢; omega) hC (fun s => by
              simp [pendingCommit, hcs s, h2 s])
        (fun _ s => by simp [polledFull, past, h2 s])
        (fun j hj => by simp [holdsAcc, h1 j hj, h3 j hj]) (fun _ => by simp [holdsAcc, hA])
        hrank (by rw [hM]; have hc := hC.cond; simp only [MmaCond] at hc ⊢; omega) hq4
        (by rw [okPolls_snoc, hOk, hM]; have := hC.task; simp [taskPos, taskStarted] at this ⊢
            omega)
        (held_keep hC hOk)
    · simp only [hl, ↓reduceDIte] at hn
      have hs3 : s0.val = 3 := by omega
      simp only [endOfTrip] at hn
      split_ifs at hn with hq' <;> obtain rfl := Option.some.inj (Option.some.inj hn) <;>
        refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore
          (okPoll_notWait (fun l p ok acq sc => by simp_all))) (hAR := by
            have hc := hC.cond; have hr := hC.accRound;
            rw [countP_snoc_none (h1 _ (Nat.mod_lt _ (by decide))), hM];
            simp [MmaCond, hs3] at hc hr ⊢; omega) hC (fun s => by
                simp [pendingCommit, hcs s, h2 s]) (fun _ s => by
            have hsle : s.val ≤ 3 := by have := s.isLt; omega
            simp [polledFull, past, h2 s, hs3, hsle]; omega)
          (fun j hj => by simp [holdsAcc, h1 j hj, h3 j hj]) (fun _ => by simp [holdsAcc, hA])
          hrank (by rw [hM]; have hc := hC.cond; simp only [MmaCond] at hc ⊢; omega)
          (by dsimp only; omega)
          (by rw [okPolls_snoc, hOk, hM]; have := hC.task; simp [taskPos, taskStarted] at this ⊢
              omega)
          (held_keep hC hOk)
  | accCommit =>
    simp only [FiresAt] at hF
    have h0 : ∀ s : Fin 4, commitsTo (emptyAt L g s) e = false := fun s => by
      rw [commitsTo_of_kind hF]
      exact decide_eq_false (loc_ne (by
        simp only [accSpec]
        have := s.isLt
        omega))
    have h1 : ∀ j, j < 2 → commitsTo (accBar L g j true) e = decide (j = w % 2) := fun j _ => by
      rw [commitsTo_of_kind hF]
      refine decide_eq_decide.mpr ?_
      simp only [accSpec, accBar, Bar.loc, Bar.off, Loc.mk.injEq, true_and]
      constructor <;> intro h <;> omega
    have h2 : ∀ s : Fin 4, okPoll (fullOf L g s) e = false := fun s => okPoll_of_kind hF
    have h3 : ∀ j, j < 2 → okPoll (accBar L g j false) e = false := fun j _ => okPoll_of_kind hF
    have hOk : okPoll (respBar L g) e = false := okPoll_of_kind hF
    have hM : mcount L g (pre ++ [e]) = mcount L g pre := mcount_snoc_none h0
    have hO : 0 < okPolls (respBar L g) pre := by
      have h4 := hC.task
      have h5 := hC.cond
      simp only [taskPos, taskStarted, MmaCond] at h4 h5
      omega
    have hA : okPoll (accBar L g (w % 2) false) e = false := h3 _ (Nat.mod_lt _ (by decide))
    simp only [next] at hn
    split_ifs at hn with hx
    · -- the first claim is none: the thread exits
      obtain rfl := Option.some.inj (Option.some.inj hn)
      obtain ⟨rr, hr0, hH0, hx0, -⟩ := hC.held (by simp) hO
      refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore hOk) (hAR := by
        have hr := hC.accRound;
        rw [List.countP_append, List.countP_singleton, h1 _ (Nat.mod_lt _ (by decide)), hM];
        simp at hr ⊢; omega) hC (fun s => by simp [pendingCommit, h0 s, h2 s])
        (fun h => by simp [Site.done] at h)
        (fun j hj => by simp [holdsAcc, h1 j hj, h3 j hj]) (fun h => by simp [Site.done] at h)
        (fun s => by rw [countP_snoc_none (h0 s), hM]; exact hC.rank s) trivial hq4
        (by rw [okPolls_snoc, hOk, hM]; have := hC.task; simp [taskPos, taskStarted] at this ⊢
            omega)
        (fun _ _ => ⟨rr, hr0, HeldRead.snoc hH0 hOk, fun _ _ => hx0 (by simp) (by simp),
          fun _ => hx⟩)
        (hE := fun _ => Or.inl (by simpa [okPolls_snoc, hOk] using hO))
    · -- the claim names a CTA: the thread takes the next task
      obtain rfl := Option.some.inj (Option.some.inj hn)
      refine Counts.step (hEX := fun _ _ => hx) (hCB :=
        claimsBefore_snoc_no hC.claimsBefore hOk) (hAR := by
          have hr := hC.accRound;
          rw [List.countP_append, List.countP_singleton, h1 _ (Nat.mod_lt _ (by decide)), hM];
          simp at hr ⊢; omega) hC (fun s => by
              simp [pendingCommit, h0 s, h2 s])
        (fun _ s => by simp [polledFull, past, h2 s])
        (fun j hj => by simp [holdsAcc, h1 j hj, h3 j hj])
        (fun _ => by simp [holdsAcc, hA]; omega)
        (fun s => by rw [countP_snoc_none (h0 s), hM]; exact hC.rank s)
        (by rw [hM]; have hc := hC.cond; simp only [MmaCond] at hc ⊢; omega) hq4
        (by rw [okPolls_snoc, hOk, hM]; have := hC.task; simp [taskPos, taskStarted] at this ⊢
            omega)
        (held_keep hC hOk)
  | exitArrive | exitWait =>
    simp only [FiresAt] at hF
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hS := noCount_of_other hF
    have h0 : ∀ l : Loc, okPoll l e = false := fun l => (hS l).1
    have h0' : ∀ l : Loc, commitsTo l e = false := fun l => (hS l).2
    have hM : mcount L g (pre ++ [e]) = mcount L g pre := mcount_snoc_none fun _ => h0' _
    refine Counts.step (hCB := claimsBefore_snoc_no hC.claimsBefore (h0 _)) (hAR :=
      accRound_frame hC (by simp) (by simp) rfl (fun j _ => h0' _) hM) hC (fun s => by
        simp [pendingCommit, h0, h0'])
      (fun h => by simp [Site.done] at h)
      (fun j _ => by simp [holdsAcc, h0, h0']) (fun h => by simp [Site.done] at h)
      (fun s => by rw [countP_snoc_none (h0' _), hM]; exact hC.rank s) trivial hq4
      (by rw [okPolls_snoc, h0, hM]; have := hC.task; simp [taskPos, taskStarted] at this ⊢
          omega)
      (fun _ hpos => by
        have hpos' : 0 < okPolls (respBar L g) pre := by simpa [okPolls_snoc, h0] using hpos
        obtain ⟨rr, hr0, hH0, hx0, hd0⟩ := hC.held (by simp) hpos'
        exact ⟨rr, hr0, HeldRead.snoc hH0 (h0 _), fun _ _ => hx0 (by simp) (by simp),
          fun _ => hd0 (by simp [Site.done])⟩)
      (hE := fun _ => by
        rcases hC.exitPoll (by simp [Site.done]) with h1 | h1 | ⟨e', he', mask, inst, l, hk, hne⟩
        · exact Or.inl (by simpa [okPolls_snoc, h0] using h1)
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨e', List.mem_append_left _ he', mask, inst, l, hk, hne⟩))
  | exit => simp [next] at hn

end Mma

/-- The MMA warps' first state after the prologue has its K block at 0, and if it has left the task
loop, its CTA is not the leader. -/
theorem prologue_next_mma {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {m : Mma.D}
    (hn : Prologue.next L g p e = some (some (.inr (.mma m)))) :
    m.q = 0 ∧ (m.site = .exitArrive → Loader.leader L g = false) := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.mma.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [Prologue.mmaStart]

/-- Along an MMA thread's event, a commit on `emptyAt s` is its commit to slot `s`. -/
theorem commitsTo_iff_site {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) {m : Mma.D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : At t m.site.pc (Mma.facts L g m))
    (hc : kernel.code[m.site.pc]? = some ins)
    (hfire : Fires m.site.pc (eventTmpl Prod L g t ins.op) e o) (s : Fin 4) :
    commitsTo (emptyAt L g s) e = decide (m.site = .commit s) := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  by_cases hs : site.commits = false
  · rw [commitsTo_of_notCommit (Mma.notCommit_fires site hs hc hfire)]
    cases site <;> first | rfl | simp [Mma.Site.commits] at hs
  · have hs' : site.commits = true := by simpa using hs
    cases site with
    | commit s0 =>
      have hk : e.kind = .tc (.commit (Mma.commitSpec L g s0)) := by
        rw [Mma.commit_event hpre hg s0 rfl hat hc hfire]
      rw [commitsTo_of_commitSpec hk]
      simp
    | accCommit =>
      obtain ⟨sp, hk, hmb⟩ := Mma.accCommit_event hpre hg rfl hat hc hfire
      have hk' : e.kind = .tc (.commit sp) := by rw [hk]
      rw [commitsTo_of_kind hk', hmb, decide_eq_false (accLoc_ne_emptyAt L g w s)]
      simp
    | _ => simp [Mma.Site.commits] at hs'

/-- The counting invariant of a thread's state: a quiet prologue, and `Mma.Counts` for MMA. -/
def ThreadCounts (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Quiet es
  | .inr (.mma m), es => Mma.Counts L g m es
  | _, _ => True

/-- Along a thread's run, every state keeps `ThreadCounts` (`Code.run_inv`). -/
theorem threadCounts_run {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      ThreadCounts L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (ThreadCounts L g) quiet_nil ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · have hq' : Quiet (pre ++ [e]) := Quiet.snoc hq (Prologue.fires_quiet hc hf)
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · exact hq'
    · trivial
    · exact Mma.counts_quiet hq' (by rcases Prologue.next_mma hn with h | h <;> simp [h])
        (by rw [(prologue_next_mma hn).1]) fun hd => by
          rcases Prologue.next_mma hn with h | h
          · simp [h, Mma.Site.done] at hd
          · exact Or.inl ((prologue_next_mma hn).2 h)
    · trivial
    · trivial
  · obtain ⟨l', -, rfl⟩ := next_of_loader hn
    trivial
  · obtain ⟨m', hm, rfl⟩ := next_of_mma hn
    exact Mma.counts_step hpre hg hinv.1 hinv.2.1 hq hat hc hf hm
  · obtain ⟨s', -, rfl⟩ := next_of_sched hn
    trivial
  · obtain ⟨c', -, rfl⟩ := next_of_cons hn
    trivial

/-- The MMA thread at its CLC poll after its run has made 128 commits per successful response poll:
the commits of its completed tasks. -/
theorem mma_clc_count_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.mma m))))
    (hs : m.site = .clcWait) :
    mmaCount L g (X.tr g) = 128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hC : Mma.Counts L g m (X.tr g) := by
    have h := threadCounts_run hpre hg htr (X.tr g).length _
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  have h := hC.task
  simp only [Mma.taskPos, Mma.taskStarted, hs, Mma.respBar] at h
  rw [mmaCount_eq]
  omega

/-- An MMA thread's successful response polls are its completed tasks, plus one when its task has
started: the states from the response poll on count one more task than their commits show, the
states before the response poll, after the accumulator commit and in the exit stage count exactly
their completed tasks. -/
theorem mma_task_count_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.mma m)))) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      mmaCount L g (X.tr g) / 128 + (if m.site = .elect ∨ m.site = .clcWait ∨
        m.site = .accCommit ∨ m.site = .exitArrive ∨ m.site = .exitWait ∨ m.site = .exit then 0
        else 1) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hC : Mma.Counts L g m (X.tr g) := by
    have h := threadCounts_run hpre hg htr (X.tr g).length _
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  have h := hC.task
  have hcond := hC.cond
  rw [mmaCount_eq]
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := m
  cases site <;> simp only [Mma.taskPos, Mma.taskStarted, MmaCond, Mma.respBar, reduceCtorEq,
    or_false, or_true, ↓reduceIte] at h hcond ⊢ <;> omega

/-- An MMA thread's successful response poll that is not its latest is followed by a read of a
response
that claims a CTA: the state's counting invariant gives it along the run. -/
theorem mma_claims_before_fact {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.mma m))))
    (j pc p : Nat) (acq : Bool) (sc : MbarScope)
    (hj : (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hcount : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) :
    ∃ pcr a bs rr, (X.tr g)[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧ a.size = 16 ∧
      Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hC : Mma.Counts L g m (X.tr g) := by
    have h := threadCounts_run hpre hg htr (X.tr g).length _
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  obtain ⟨pcr, a, bs, rr, h1, h2, h3, h4, h5⟩ := hC.claimsBefore j pc p acq sc hj hcount
  exact ⟨pcr, a, bs, rr, h1, h2, h3, h4, h5⟩

/-- **An MMA thread at its response wait has read no non-claiming response after a successful
response poll.** A poll that is not its latest is followed by a claiming read (`claimsBefore`); the
latest one is the held read, whose first CTA is the state's `x`, not none at the wait (`held`,
`entryX`). -/
theorem Mma.fail_wait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.mma m))))
    (hs : m.site = .clcWait) :
    ∀ j pc p acq sc pcr src bs rr, (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ → src.loc = respLoc L g → src.size = 16 →
      Flow.responseOf bs = some rr → Loader.claims rr := by
  intro j pc p acq sc pcr src bs rr hj hr _ _ hrr
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hC : Mma.Counts L g m (X.tr g) := by
    have h := threadCounts_run hpre hg htr (X.tr g).length _
      (by rw [List.take_length]; exact hσ)
    rwa [List.take_length] at h
  have same : ∀ pcr' a bs' rr', (X.tr g)[j + 1]? = some ⟨pcr', .rd a bs'⟩ →
      Flow.responseOf bs' = some rr' → rr' = rr := by
    intro pcr' a bs' rr' h1 h2
    rw [hr] at h1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at h1
    obtain ⟨-, -, rfl⟩ := h1
    exact Option.some.inj (h2.symm.trans hrr)
  have hjl : j + 1 ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hr).1.le
  have h1 := Mma.cbPoll_succ (m := Mma.respBar L g) hj (by simp [okPoll, sourceWaitSuccess])
  have h2 := Mma.cbOkPolls_take_le (Mma.respBar L g) (X.tr g) hjl
  rw [List.take_of_length_le (le_refl _)] at h2
  rcases Nat.lt_or_ge (okPolls (Mma.respBar L g) ((X.tr g).take j) + 1)
      (okPolls (Mma.respBar L g) (X.tr g)) with hlt | hge
  · obtain ⟨pcr', a, bs', rr', h1, -, -, h4, h5⟩ := hC.claimsBefore j pc p acq sc hj hlt
    rwa [same pcr' a bs' rr' h1 h4] at h5
  · have hpos : 0 < okPolls (Mma.respBar L g) (X.tr g) := by omega
    obtain ⟨rr0, -, hH, hx, -⟩ := hC.held (by rw [hs]; simp) hpos
    obtain ⟨j0, pc0, p0, acq0, sc0, pcr0, a0, bs0, hj0, hrd0, -, -, hr0, hc0⟩ := hH
    have hjj := Mma.cbPoll_index_eq (m := Mma.respBar L g) hj (by simp [okPoll,
      sourceWaitSuccess]) hj0
      (by simp [okPoll, sourceWaitSuccess]) (by omega)
    subst hjj
    have := same pcr0 a0 bs0 rr0 hrd0 hr0
    subst this
    have hxne := hC.entryX hs hpos
    rw [hx (by rw [hs]; simp) (by rw [hs]; simp)] at hxne
    exact hxne

namespace InputRing

/-- At a commit to slot `s`, the earlier commits there are fewer than its full polls. -/
theorem commit_budget {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.mma m))))
    {s : Fin 4} {sp : TcCommit.Spec} (hk : e.kind = .tc (.commit sp))
    (hm : sp.mbar = emptyAt L g s) :
    ((X.tr g).take k).countP (commitsTo (emptyAt L g s)) + 1 ≤
      okPolls (Mma.fullOf L g s) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have hcs := commitsTo_iff_site hpre hg hat hc hfire s
  have hcm : commitsTo (emptyAt L g s) e = true := by
    rw [commitsTo_of_kind hk, hm]
    simp
  rw [hcm] at hcs
  have hp : Mma.pendingCommit m s = true := by simp [Mma.pendingCommit, of_decide_eq_true hcs.symm]
  have hC' := hC.commit s
  simp only [hp, ↓reduceIte] at hC'
  omega

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.NotRegister
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.TraceInduction

public section

/-! # Each lane issues one register adjustment at the warpgroup hand-off -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RegisterRequestTrace

open PTX PTX.Flow SetMaxNReg

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}

private def registerSites : List Nat := [Flow.setMaxReg_0, Flow.setMaxReg_1, Flow.setMaxReg_2]

set_option maxRecDepth 100000 in
private theorem register_sites : OpPcsFast kernel.code setMaxRegOp registerSites = true := by
  decide +kernel

local macro "exclude_register" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private theorem request_site {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d ∈ registerSites) : ∃ w, d = .prologue (.handoff w) := by
  cases d with
  | prologue s =>
    change s.pc ∈ registerSites at h
    cases s with
    | handoff w => exact ⟨w, rfl⟩
    | _ => all_goals exfalso; revert h; exclude_register
  | head => exact absurd h (by change 1843 ∉ registerSites; decide)
  | done => exact absurd h (by change 3611 ∉ registerSites; decide)
  | idle s =>
    change s.pc ∈ registerSites at h
    cases s <;> exfalso <;> revert h <;> exclude_register
  | wg0 d | wg2 d | tma d | mma d | index d =>
    all_goals
      exfalso
      change d.site.pc ∈ registerSites at h
      generalize d.site = s at h
      clear d
      cases s <;> revert h <;> exclude_register

private theorem request_role {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o) {inc : Bool} {n inst : Nat}
    (hk : e.kind = .setMaxReg inc n inst) : ∃ w, d = .prologue (.handoff w) := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    rw [congrArg Event.kind hf.1] at hk
    cases hk
  | some ins =>
    rw [hc] at hf
    exact request_site (OpPcsFast.mem register_sites hc (by rw [fires_setMaxReg_op hf hk]; rfl))

/-- The register count selected by each execution warpgroup. -/
def payload (w : Nat) : Bool × Nat :=
  if w = 0 then (true, 224) else if w = 1 then (false, 72) else (true, 208)

theorem payload_valid (w : Fin 3) : validCount (payload w.val).2 = true := by
  fin_cases w <;> decide

theorem handoff_code (w : Fin 3) :
    kernel.code[entryPc w]? = some ⟨none, .setMaxReg (payload w.val).1 (payload w.val).2⟩ := by
  fin_cases w
  · exact Flow.code_setMaxReg_0
  · exact Flow.code_setMaxReg_1
  · exact Flow.code_setMaxReg_2

private theorem handoff_request {w : Fin 3} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.prologue (.handoff w))) e o) :
    ∃ inst, e = ⟨entryPc w, .setMaxReg (payload w.val).1 (payload w.val).2 inst⟩ := by
  obtain ⟨t, hat, hf⟩ := hf
  change Fires t.pc (match kernel.code[entryPc w]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hpc : t.pc = entryPc w := hat.1.1
  rw [hpc, handoff_code] at hf
  change Fires (entryPc w) (eventTmpl Assumptions.all L g t
    (.setMaxReg (payload w.val).1 (payload w.val).2)) e o at hf
  have hv : SetMaxNReg.validCount (payload w.val).2 = true := by fin_cases w <;> decide
  exact fires_of_setMaxReg_op hv hf

private def counts (n : Nat) : Option Machine.ThreadD → Prop
  | none => True
  | some (.prologue _) => n = 0
  | some _ => n = 1

private theorem no_request_of_site {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (h : ∀ w, d ≠ .prologue (.handoff w)) : isRequest e = false := by
  unfold isRequest
  split
  · rename_i inc n inst hk
    obtain ⟨w, hw⟩ := request_role hf hk
    exact (h w hw).elim
  · rfl

private theorem counts_step {d q : Option Machine.ThreadD} {e : Event} {o : Option TState}
    {es : List Event}
    (h : counts (es.countP isRequest) d)
    (hf : (Machine.machine P L g).Fired d e o)
    (hn : (Machine.machine P L g).next d e = some q) :
    counts ((es ++ [e]).countP isRequest) q := by
  simp only [List.countP_append, List.countP_singleton]
  cases d
  case none =>
    change some none = some q at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some q at hn
    cases d
    case prologue s =>
      change es.countP isRequest = 0 at h
      simp only [h, Nat.zero_add]
      by_cases hs : ∃ w, s = .handoff w
      · obtain ⟨w, rfl⟩ := hs
        obtain ⟨_, rfl⟩ := handoff_request hf
        simp only [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
        split_ifs at hn
        · fin_cases w <;> cases hn <;> rfl
        · cases hn
          trivial
      · have hnoreq := no_request_of_site hf (fun w he => hs ⟨w, Machine.ThreadD.prologue.inj he⟩)
        simp only [hnoreq, Bool.false_eq_true, ↓reduceIte]
        simp only [Machine.next] at hn
        split at hn
        · cases hn
          rfl
        · split at hn
          · rename_i w _
            exact (hs ⟨w, rfl⟩).elim
          · cases hn
            trivial
        · cases hn
    all_goals
      rw [no_request_of_site hf (by simp)]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> first | exact h | trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals first | exact h | trivial

private theorem counts_at (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) {e : Event} {d : Machine.ThreadD}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    counts (ordinal X (g, i)) (some d) :=
  (hs.produces (hX.thr g (Frame.lt_of_get hX he))).prefix_induction
    (fun q es => counts (es.countP isRequest) q) rfl
    (fun _ _ _ _ _ => counts_step) i (some d) hd

/-- The lane has issued no register request while its state is still in the prologue. -/
theorem no_request_at_prologue (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads) {s : Site}
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue s))) :
    ∀ j tag inc n inst, ¬ Request X (g, j) tag inc n inst := by
  have hCount : (X.tr g).countP isRequest = 0 := by
    have h := (hs.produces (hX.thr g hg)).prefix_induction
      (fun q es => counts (es.countP isRequest) q) rfl
      (fun _ _ _ _ _ => counts_step) (X.tr g).length (some (.prologue s)) hState
    simpa only [counts, List.take_length] using h
  intro j tag inc n inst hr
  exact List.countP_eq_zero.mp hCount _ (List.mem_of_getElem? hr) rfl

/-- No request in the thread's history gives zero request count. -/
theorem count_eq_zero_of_no_request
    (hNo : ∀ j tag inc n inst, ¬ Request X (g, j) tag inc n inst) :
    (X.tr g).countP isRequest = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨tag, k⟩ := e
  cases k
  case' setMaxReg => exact (hNo j tag _ _ _ hj).elim
  all_goals simp [isRequest]

/-- A followed thread without a request has not passed register hand-off. -/
theorem prologue_of_missing_request (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads) {d : Machine.ThreadD}
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hNo : ∀ j tag inc n inst, ¬ Request X (g, j) tag inc n inst) :
    ∃ s, d = .prologue s := by
  have hCount := count_eq_zero_of_no_request hNo
  have h := (hs.produces (hX.thr g hg)).prefix_induction
    (fun q es => counts (es.countP isRequest) q) rfl
    (fun _ _ _ _ _ => counts_step) (X.tr g).length (some d) hState
  rw [List.take_length, hCount] at h
  cases d <;> first | exact ⟨_, rfl⟩ | cases h

private theorem request_data (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {tag : Nat} {inc : Bool} {n inst : Nat} (hr : Request X (g, i) tag inc n inst) :
    ordinal X (g, i) = 0 ∧ (inc, n) = payload (wgOf L g) ∧
      ∃ w : Fin 3, wgOf L g = w.val ∧ tag = entryPc w := by
  have hg := Frame.lt_of_get hX hr
  obtain ⟨_, _, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht hr (by simp)
  obtain ⟨w, rfl⟩ := request_role hf rfl
  have hw := (PrologueRoleTrace.handoff_source hpre (PTX.len_of_get hr).le hd).1
  obtain ⟨_, hh⟩ := handoff_request hf
  obtain ⟨hI, hN, _⟩ := Kind.setMaxReg.inj (congrArg Event.kind hh)
  exact ⟨counts_at hX (hs g hg).machine hr hd, by rw [hw, hI, hN],
    w, hw, congrArg Event.pc hh⟩

/-- Requests are first in their lane's register history and select their warpgroup's payload. -/
theorem request_payload (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {tag : Nat} {inc : Bool} {n inst : Nat} (hr : Request X (g, i) tag inc n inst) :
    ordinal X (g, i) = 0 ∧ (inc, n) = payload (wgOf L g) :=
  let h := request_data hpre hX hs ht hr
  ⟨h.1, h.2.1⟩

/-- Two requests of one warpgroup are from the same actual instruction. -/
theorem same_source (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {h j tag tag' n n' inst inst' : Nat} {inc inc' : Bool}
    (hr : Request X (g, i) tag inc n inst) (hr' : Request X (h, j) tag' inc' n' inst')
    (hgroup : wgOf L g = wgOf L h) : tag = tag' := by
  obtain ⟨_, _, w, hw, hTag⟩ := request_data hpre hX hs ht hr
  obtain ⟨_, _, w', hw', hTag'⟩ := request_data hpre hX hs ht hr'
  have he : w = w' := Fin.ext (hw.symm.trans (hgroup.trans hw'))
  exact hTag.trans (he ▸ hTag'.symm)

/-- Every actual exit follows the lane's register request. -/
theorem exit_ordinal (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {tag : Nat} (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ordinal X (g, i) = 1 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  have hn := RingGateEvents.exit_after_prologue hf rfl
  have hc := counts_at hX (hs g hg).machine he hd
  cases d
  case prologue s => exact (hn s rfl).elim
  all_goals exact hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RegisterRequestTrace

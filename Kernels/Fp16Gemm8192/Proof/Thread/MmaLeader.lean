-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaUnelected
public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Flow.ElectMask

@[expose] public section

/-! # The MMA leader thread: its election, its tasks, and its end

A leader MMA thread (warp 8 or 9 of a leader CTA) runs the common prologue of its warp (`mmaPath1`
to `mmaPath6`), elects its lane at index 6 of its trace (`elect_index`), and then runs tasks. Its
counting invariant `Mma.Counts` follows the run: the commits and the response polls of the tasks,
the response the thread holds with its read, and the claim of the exit. `mma_leader_thm` reads the
state at the end of the trace from that invariant (`threadCounts_run`): the thread is working; or it
has finished, its exit stage with 32 commits per slot for each response poll and a last read that
claims no CTA; or its machine has stopped at the end of its trace without an exit (a read whose
bytes do not decode, or undefined behaviour). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-! ## Elect events of instructions that are not elections -/

/-- An instruction's own elect event is the only one of its template. -/
theorem fires_notElect_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState}
    (hop : ∀ w : WarpInstr, op = .warp w → w.kind ≠ .elect)
    (hf : Fires pc (eventTmpl A L g t op) e o) : ∀ mask inst leader, e.kind ≠
      .elect mask inst leader := by
  refine fires_notElect (eventTmpl_notElect ?_) hf
  cases op <;> try rfl
  rename_i w
  obtain ⟨k, _, _, _, _⟩ := w
  cases k <;> first | rfl | exact absurd rfl (hop _ rfl)

namespace Mma

/-- Every MMA site other than the exit is an instruction that is not the exit. -/
theorem notExit_site {s : Site} (hs : s ≠ .exit) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : ins.op ≠ .ret := by
  intro h
  cases s with
  | exit => exact hs rfl
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3); cases h
  | clcWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15); cases h
  | clcLoad => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_2); cases h
  | clcStatus => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_4); cases h
  | clcFirst => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_5); cases h
  | clcFence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_3); cases h
  | ack => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11); cases h
  | accWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_16); cases h
  | full s' => obtain rfl := Option.some.inj ((code_full_ops s').symm.trans hc); cases h
  | mma s' j' =>
    obtain ⟨ad, bd, en, hc'⟩ := code_mma s' j'
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    cases h
  | commit s' =>
    obtain ⟨base, mask, hc'⟩ := code_commit s'
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    cases h
  | accCommit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_4); cases h
  | exitArrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1); cases h
  | exitWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1); cases h

end Mma

namespace Mma

/-- Every MMA site other than the election is an instruction that is not an election. -/
theorem notElect_site {s : Site} (hs : s ≠ .elect) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) :
    ∀ w : WarpInstr, ins.op = .warp w → w.kind ≠ .elect := by
  intro w h
  cases s with
  | elect => exact (hs rfl).elim
  | clcWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15); cases h
  | clcLoad => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_2); cases h
  | clcStatus => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_4); cases h
  | clcFirst => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_5); cases h
  | clcFence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_3); cases h
  | ack => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11); cases h
  | accWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_16); cases h
  | full s' => obtain rfl := Option.some.inj ((code_full_ops s').symm.trans hc); cases h
  | mma s' j' =>
    obtain ⟨ad, bd, en, hc'⟩ := code_mma s' j'
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    cases h
  | commit s' =>
    obtain ⟨base, mask, hc'⟩ := code_commit s'
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    cases h
  | accCommit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_4); cases h
  | exitArrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1); cases h
  | exitWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1); cases h
  | exit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0); cases h

end Mma


namespace Prologue

/-- The prologue sites other than the elections are not elections. -/
theorem notElect_site {s : Site} (hs : s ≠ .elect) (hs' : s ≠ .roleElect) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) :
    ∀ w : WarpInstr, ins.op = .warp w → w.kind ≠ .elect := by
  intro w h
  cases s with
  | shfl => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0); cases h; nofun
  | elect => exact (hs rfl).elim
  | init i =>
    rw [code_init_op i] at hc
    obtain rfl := Option.some.inj hc
    cases h
  | alloc => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); cases h
  | allocWrite => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); cases h
  | warpBar => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0); cases h; nofun
  | fence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0); cases h
  | fenceInit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0); cases h
  | arrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0); cases h
  | wait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0); cases h
  | setMaxReg => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0); cases h
  | roleElect => exact (hs' rfl).elim

end Prologue


/-! ## The path of a thread: the prologue up to the MMA election -/

/-- A state's event fired from a prologue state that is not an election is no election. -/
theorem prologue_not_elect {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {p : Prologue.D} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inl p))) (hs : p.site ≠ .elect)
    (hs' : p.site ≠ .roleElect) : ∀ mask inst leader, e.kind ≠ .elect mask inst leader := by
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hf⟩ := Code.fired_site (sound hpre hg) hfo
  exact fires_notElect_op (Prologue.notElect_site hs hs' hc) hf

/-- A state's event fired from an MMA state that is not the election is no election. -/
theorem mma_not_elect {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {m : Mma.D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site ≠ .elect) :
    ∀ mask inst leader, e.kind ≠ .elect mask inst leader := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  exact fires_notElect_op (Mma.notElect_site hs hc) hf

/-- A state's event fired from an MMA state that is not the exit is no exit event. -/
theorem mma_not_exit {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {m : Mma.D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site ≠ .exit) :
    e.kind ≠ .exit := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  exact fun hk => (fires_exit_op hf hk).elim (Mma.notExit_site hs hc) (not_exit hc)

/-- The MMA state's successor. -/
theorem stateAt_mma {L : Launch} {X : Execution} {g k : Nat} {e : Event} {m : Mma.D}
    (he : (X.tr g)[k]? = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) :
    Frame.stateAt (code L) X g (k + 1) = (Mma.next L g m e).map
      (Option.map fun m' => (Sum.inr (Prologue.Role.mma m') : ThreadD)) := by
  rw [Frame.stateAt_succ he, hσ]
  rfl


theorem next_ne_some_none {L : Launch} {g : Nat} (m : Mma.D) (e : Event) :
    Mma.next L g m e ≠ some none := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := m
  cases site <;> simp only [Mma.next] <;> (repeat' split) <;> simp


/-- The quiet tail: from index `K` on, no event counts as a successful response poll or as a commit
to any input empty barrier, so the counts of the whole run are those of its prefix. -/
theorem countP_full_eq_take {X : Execution} {g K : Nat} {p : Event → Bool}
    (htail : ∀ i e, K ≤ i → (X.tr g)[i]? = some e → p e = false) :
    (X.tr g).countP p = ((X.tr g).take K).countP p := by
  conv_lhs => rw [← List.take_append_drop K (X.tr g)]
  rw [List.countP_append]
  have hdrop : (List.drop K (X.tr g)).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_drop] at hn
    rw [htail (K + n) x (by omega) hn]
    simp
  rw [hdrop, Nat.add_zero]




/-- An MMA state whose exit stage is not reached has no exit offset. -/
theorem exitOff_of_not_done {m : Mma.D} (h : m.site.done = false) : Mma.exitOff m = none := by
  obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := m
  cases s <;> simp_all [Mma.exitOff, Mma.Site.done]

/-- The successor of an MMA state is no election state. -/
theorem next_site_ne_elect {L : Launch} {g : Nat} {m m' : Mma.D} {e : Event}
    (hn : Mma.next L g m e = some (some m')) : m'.site ≠ .elect := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  obtain ⟨s', w', q', fp', ap', cp', r', x'⟩ := m'
  cases site <;> simp only [Mma.next, Mma.endOfTrip] at hn <;> (repeat' split at hn) <;>
    (intro h; subst h; simp_all)

/-- The state after the election: the MMA state after the election event at index 6 is the
successor of the election state, which is no election state (or it is dead). -/
theorem stateAt_seven {L : Launch} {X : Execution} {g : Nat} {e6 : Event} {m6 : Mma.D}
    (hs6 : Frame.stateAt (code L) X g 6 = some (some (.inr (.mma m6)))) (he6 : (X.tr g)[6]? =
      some e6) :
    Frame.stateAt (code L) X g 7 = none ∨
      ∃ m7, Frame.stateAt (code L) X g 7 = some (some (.inr (.mma m7))) ∧ m7.site ≠ .elect := by
  rw [stateAt_mma he6 hs6]
  cases hn : Mma.next L g m6 e6 with
  | none => exact Or.inl rfl
  | some o =>
    cases o with
    | none => exact absurd hn (next_ne_some_none m6 e6)
    | some m7 => exact Or.inr ⟨m7, by simp, next_site_ne_elect hn⟩

/-- Along the run from the seventh state on, every state is dead or an MMA state that is no
election: an MMA state moves to an MMA state or to none. -/
theorem mma_run {L : Launch} {X : Execution} {g : Nat}
    (base : Frame.stateAt (code L) X g 7 = none ∨
      ∃ m7, Frame.stateAt (code L) X g 7 = some (some (.inr (.mma m7))) ∧ m7.site ≠ .elect) :
    ∀ n, 7 + n ≤ (X.tr g).length → Frame.stateAt (code L) X g (7 + n) = none ∨
      ∃ m, Frame.stateAt (code L) X g (7 + n) = some (some (.inr (.mma m))) ∧ m.site ≠ .elect := by
  intro n
  induction n with
  | zero => intro _; exact base
  | succ n ih =>
    intro hn
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[7 + n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [show 7 + (n + 1) = 7 + n + 1 by omega]
    rcases ih (by omega) with hnone | ⟨m, hσ, hsite⟩
    · exact Or.inl (by rw [Frame.stateAt_succ he, hnone]; rfl)
    · have hsucc := stateAt_mma he hσ
      cases hn' : Mma.next L g m e with
      | none => exact Or.inl (by rw [hsucc, hn']; rfl)
      | some o =>
        cases o with
        | none => exact absurd hn' (next_ne_some_none m e)
        | some m' => exact Or.inr ⟨m', by rw [hsucc, hn']; rfl, next_site_ne_elect hn'⟩

set_option maxHeartbeats 8000000 in
/-- The election of an MMA warp of a leader CTA: its elect event is at index 6, the only index
whose state is an election; before it the prologue, after it no election. -/
theorem elect_index {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g j pc mask inst leader : Nat}
    (hg : g < L.threads) (hw : g % L.block / 32 = 8 ∨ g % L.block / 32 = 9)
    (hl : g / L.block % 2 = 0) (hj : X.get (g, j) = some ⟨pc, .elect mask inst leader⟩) :
    j = 6 := by
  have hW' : Prologue.warpOf L g = 8 ∨ Prologue.warpOf L g = 9 := hw
  have hleader : Loader.leader L g = true := by simp [Loader.leader, hl]
  have hjlt : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · exfalso
    interval_cases j
    · exact prologue_not_elect hpre hX hg hj (stateAt_zero L X g) (by simp) (by simp)
        mask inst leader rfl
    · exact prologue_not_elect hpre hX hg hj (mmaPath1 hpre hX hg (by omega) (by omega))
        (by simp) (by simp) mask inst leader rfl
    · exact prologue_not_elect hpre hX hg hj (mmaPath2 hpre hX hg (by omega) (by omega))
        (by simp) (by simp) mask inst leader rfl
    · exact prologue_not_elect hpre hX hg hj (mmaPath3 hpre hX hg (by omega) (by omega))
        (by simp) (by simp) mask inst leader rfl
    · exact prologue_not_elect hpre hX hg hj (mmaPath4 hpre hX hg (by omega) (by omega))
        (by simp) (by simp) mask inst leader rfl
    · exact prologue_not_elect hpre hX hg hj (mmaPath5 hpre hX hg (by omega) (by omega) (by omega))
        (by simp) (by simp) mask inst leader rfl
  rcases Nat.eq_or_lt_of_le hj6 with h6 | h7
  · exact h6.symm
  · exfalso
    have hs6 := mmaPath6 hpre hX hg hW' (by omega)
    obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hrun := mma_run (stateAt_seven hs6 he6)
    have hj7 := hrun (j - 7) (by omega)
    rw [show 7 + (j - 7) = j by omega] at hj7
    rcases hj7 with hdead | ⟨m, hσ, hsite⟩
    · rcases Frame.fired (fun _ => sound hpre) hX hj with ⟨τ, -, hτ, -⟩ | ⟨-, pc', f, h⟩
      · rw [hdead] at hτ
        cases hτ
      · cases h
    · exact mma_not_elect hpre hX hj hσ hsite mask inst leader rfl

/-- An exit stage has started no task: its position and its started flag are zero. -/
theorem taskPos_of_done {d : Mma.D} (h : d.site.done = true) : Mma.taskPos d = 0 := by
  obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := d
  cases s <;> simp_all [Mma.taskPos, Mma.Site.done]

theorem taskStarted_of_done {d : Mma.D} (h : d.site.done = true) : Mma.taskStarted d = 0 := by
  obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := d
  cases s <;> simp_all [Mma.taskStarted, Mma.Site.done]

/-- The finished data of the leader, from the counts of its exit stage after the events `take k`:
each slot commits 32 times per response poll, and the last poll's read claims no CTA. -/
theorem finished_of {X : Execution} {L : Launch} {g k : Nat} {m : Mma.D}
    (hk : k ≤ (X.tr g).length) (hC : Mma.Counts L g m ((X.tr g).take k)) (hd : m.site.done = true)
    (hleader : Loader.leader L g = true)
    (hE : ∀ e ∈ X.tr g, ∀ mask inst l, e.kind = .elect mask inst l → l = laneOf L g)
    (htail : ∀ i e, k ≤ i → (X.tr g)[i]? = some e →
      okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) e = false ∧
        ∀ s : Fin 4, commitsTo (emptyAt L g s) e = false) :
    (∀ s : Fin 4, (X.tr g).countP (commitsTo (inputEmpty L (g / L.block) s)) =
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) ∧
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr := by
  -- the tail moves neither the commits nor the response polls
  have hcnt : ∀ s : Fin 4, (X.tr g).countP (commitsTo (emptyAt L g s)) =
      ((X.tr g).take k).countP (commitsTo (emptyAt L g s)) := fun s =>
    countP_full_eq_take (fun i e hi he => (htail i e hi he).2 s)
  have hpol : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) :=
    countP_full_eq_take (p := okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (fun i e hi he => (htail i e hi he).1)
  -- the exit stage has no task running, and its counts are 128 per response poll
  have hT : 128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) =
      mcount L g ((X.tr g).take k) := by
    have h := hC.task
    rw [taskStarted_of_done hd, taskPos_of_done hd] at h
    exact h
  have hpos : 0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) := by
    rcases hC.exitPoll hd with h | h | ⟨e, he, mask, inst, l, hk', hne⟩
    · exact h
    · rw [hleader] at h
      exact absurd h (by simp)
    · exact absurd (hE e (List.mem_of_mem_take he) mask inst l hk') hne
  have hnl : m.site ≠ .clcLoad := fun h => by
    rw [h] at hd
    simp [Mma.Site.done] at hd
  obtain ⟨rr, hr, hH, hx, hdx⟩ := hC.held hnl hpos
  have hfo : Mma.firstOf rr = Loader.none32 := by
    have h1 := hx (fun h => by rw [h] at hd; simp [Mma.Site.done] at hd)
      (fun h => by rw [h] at hd; simp [Mma.Site.done] at hd)
    exact h1.symm.trans (hdx hd)
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, ha, hs, hrr, hcc⟩ := hH
  have hjk : j + 1 < k := by
    have := (List.getElem?_eq_some_iff.mp h2).1
    simp only [List.length_take] at this
    omega
  have htj : (X.tr g).take j = ((X.tr g).take k).take j := by
    rw [List.take_take, min_eq_left (by omega)]
  refine ⟨fun s => ?_, j, pc, p, acq, sc, pcr, a, bs, rr, ?_, ?_, ?_, ⟨ha, hs⟩, hrr,
    fun hc => hc hfo⟩
  · have hM : mcount L g ((X.tr g).take k) = 128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        ((X.tr g).take k) := by
      omega
    have hs4 := s.isLt
    rw [inputEmpty_emptyAt, hcnt s, hpol, hC.rank s, hM]
    omega
  · rw [htj, hpol]
    exact hcc
  · show (X.tr g)[j]? = _
    rw [List.getElem?_take_of_lt (by omega)] at h1
    exact h1
  · show (X.tr g)[j + 1]? = _
    rw [List.getElem?_take_of_lt hjk] at h2
    exact h2

set_option maxHeartbeats 8000000 in
/-- The MMA leader thread: working, finished, or stopped at the end of its trace without an exit. -/
theorem mma_leader_thm {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g j pc mask inst : Nat}, g < L.threads → g / L.block % 2 = 0 →
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) →
    X.Elect (g, j) pc mask inst (laneOf L g) →
    (∃ m, Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) ∧ Mma.exitOff m =
      none ∧
      m.site ≠ .elect) ∨
    ((∀ s : Fin 4, (X.tr g).countP (commitsTo (inputEmpty L (g / L.block) s)) =
        32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) ∧
      ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
          okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
        X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
        X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr) ∨
    (Frame.stateAt (code L) X g (X.tr g).length = none ∧ ∀ pc, (X.tr g).getLast? ≠
      some ⟨pc, .exit⟩) := by
  intro g j pc mask inst hg hl hw hj
  have hj' : X.get (g, j) = some ⟨pc, .elect mask inst (laneOf L g)⟩ := hj
  have hleader : Loader.leader L g = true := by simp [Loader.leader, hl]
  have hW' : Prologue.warpOf L g = 8 ∨ Prologue.warpOf L g = 9 := hw
  -- the election is the sixth event, and every election of the thread is that one
  have hj6 : j = 6 := elect_index hpre hX hg hw hl hj'
  subst hj6
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have he6 : (X.tr g)[6]? = some ⟨pc, .elect mask inst (laneOf L g)⟩ := hj'
  have hlen6 : 6 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he6).1
  have hs6 := mmaPath6 hpre hX hg hW' (by omega)
  have hrun := mma_run (stateAt_seven hs6 he6)
  have hE : ∀ e ∈ X.tr g, ∀ mask' inst' l, e.kind = .elect mask' inst' l → l = laneOf L g := by
    intro e he mask' inst' l hk
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
    have hgi : X.get (g, i) = some e := by
      show (X.tr g)[i]? = some e
      rw [List.getElem?_eq_getElem hi, hie]
    have hei : e = ⟨e.pc, .elect mask' inst' l⟩ := by
      obtain ⟨p, k⟩ := e
      simp only at hk ⊢
      rw [hk]
    rw [hei] at hgi
    have hi6 : i = 6 := elect_index hpre hX hg hw hl hgi
    subst hi6
    have h := Option.some.inj (he6.symm.trans hgi)
    simp only [Event.mk.injEq, Kind.elect.injEq] at h
    exact h.2.2.2.symm
  have hN : 7 + ((X.tr g).length - 7) = (X.tr g).length := by omega
  have hend := hrun ((X.tr g).length - 7) (by omega)
  rw [hN] at hend
  rcases hend with hdead | ⟨m, hσ, hsite⟩
  · by_cases hexit : ∃ pc', (X.tr g).getLast? = some ⟨pc', .exit⟩
    · -- the thread exited: its last event leaves the exit stage, which counts the trace
      obtain ⟨pcx, hlast⟩ := hexit
      have hget : (X.tr g)[(X.tr g).length - 1]? = some ⟨pcx, .exit⟩ := by
        rw [← List.getLast?_eq_getElem?]
        exact hlast
      have hk1 : 7 ≤ (X.tr g).length - 1 := by
        by_contra hlt
        have h6eq : (X.tr g).length - 1 = 6 := by omega
        rw [h6eq, he6] at hget
        simp at hget
      have hk := hrun ((X.tr g).length - 1 - 7) (by omega)
      rw [show 7 + ((X.tr g).length - 1 - 7) = (X.tr g).length - 1 by omega] at hk
      rcases hk with hnone | ⟨m', hσ', hsite'⟩
      · exfalso
        rcases Frame.fired (fun _ => sound hpre) hX hget with ⟨τ, -, hτ, -⟩ | ⟨-, pc', f, h⟩
        · rw [hnone] at hτ
          cases hτ
        · cases h
      · have hdone : m'.site.done = true := by
          by_contra hnd
          have hnd' : m'.site.done = false := by simpa using hnd
          have hne : m'.site ≠ .exit := by
            intro h
            rw [h] at hnd'
            simp [Mma.Site.done] at hnd'
          exact mma_not_exit hpre hX hget hσ' hne rfl
        have hC' : Mma.Counts L g m' ((X.tr g).take ((X.tr g).length - 1)) :=
          threadCounts_run hpre hg htr _ _ hσ'
        have htail : ∀ i e, (X.tr g).length - 1 ≤ i → (X.tr g)[i]? = some e →
            okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) e = false ∧
              ∀ s : Fin 4, commitsTo (emptyAt L g s) e = false := by
          intro i e hi he
          rcases Nat.eq_or_lt_of_le hi with h | h
          · subst h
            have hee : e = ⟨pcx, .exit⟩ := Option.some.inj (he.symm.trans hget)
            subst hee
            exact ⟨okPoll_notWait (fun l p ok acq sc h => by simp at h),
              fun s => commitsTo_of_notCommit (fun sp h => by simp at h)⟩
          · exfalso
            rw [List.getElem?_eq_none (by omega)] at he
            cases he
        exact Or.inr (Or.inl (finished_of (by omega) hC' hdone hleader hE htail))
    · exact Or.inr (Or.inr ⟨hdead, fun pc' h => hexit ⟨pc', h⟩⟩)
  · by_cases hd : m.site.done = true
    · have hC : Mma.Counts L g m ((X.tr g).take (X.tr g).length) :=
        threadCounts_run hpre hg htr _ _ hσ
      refine Or.inr (Or.inl (finished_of (le_refl _) hC hd hleader hE ?_))
      intro i e hi he
      exfalso
      rw [List.getElem?_eq_none hi] at he
      cases he
    · exact Or.inl ⟨m, hσ, exitOff_of_not_done (by simpa using hd), hsite⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof

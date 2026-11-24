-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaEvents
public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderExec

@[expose] public section

/-!
# The MMA warp's handshake counts along a run

* `mma_count`: the one counting theorem. Along a run of the MMA warp that keeps `Mma.Inv`, the
  count of a class of events `p` is the change of a measure `μ` of the abstract state, if each step
  of the machine changes `μ` by one exactly at the events `p` counts (`Ring.count_trace`).
* `mma_pPolls`, `mma_sCommits`, `mma_oCommits`, `mma_fCommits`: the four instances.
* `mma_pwait`: **the poll of `p_ready`**. At the `pWait` site, in a run from the start of the loop,
  the event is the poll of `p_ready ((i - 1) % 2)` with parity `fullParity (i - 1)`, it is for the
  warp's `n`-th block of that buffer (`i - 1 = blockB b n`, `n` the polls of that barrier made
  before), and its parity is `n % 2`: the alternation of a poller whose `n`-th poll waits for
  phase `n`.
* `mma_qkcommit`: the QK commit to `s_ready (i % 2)` at `qkCommit` is for block `i`, the `n`-th
  commit to that barrier: `i = blockB b n`.
* `mma_ocommit`: the second PV commit, to `o_done`, at `pvCommit2` is the `n`-th commit and is for
  block `i - 1 = n`.
* `mma_fcommit`: the commit to `o_final` at `finCommit` is the first (no earlier commit to it).

As for the KV ring, a run starts at a state of the loop and stays in the role; that the thread's
whole trace is one such run is the role-table protocol (`Ring.lean`, `hin`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW LeadRun MmRun count_trace)
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape mma_shape sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}

/-- **The counting theorem along an MMA run.** `E` is a property of the events of the run (that
each election returned the thread's lane), `p` the count, `μ` the measure. -/
theorem mma_count {P : Loader.Pro} {d0 : Mma.D} {es : List Event}
    (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es)
    (p : Event → Bool) (μ : Mma.D → Nat) (E : Event → Prop) (hE : ∀ e ∈ es, E e)
    (hstep : ∀ (d1 d' : Mma.D) (e : Event), Mma.Inv d1 → d1.site ≠ .setMaxRegInc → E e →
      ((∃ u, (WComp.code L g Q).toMachine.Fired (some (.mma d1 P)) e (some u)) ∨ Ends e) →
      Mma.next L g d1 e = some (some d') → μ d' = μ d1 + if p e = true then 1 else 0)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P))) :
    es.countP p + μ d0 = μ d := by
  have h := count_trace (M := (WComp.code L g Q).toMachine) p
    (fun σ => match σ with | some (.mma d _) => μ d | _ => 0)
    (fun σ => ∃ d, σ = some (.mma d P) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    E (some (.mma d P)) ?_ hT hE ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne⟩ hEe hev hn hσ'
    have hn' : WComp.next L g (.mma d1 P) e = some σ' := hn
    rw [EvW.next_mma_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      exact hstep d1 a e hin1 hne hEe hev ha
  · intro j hj
    obtain ⟨d1, h1, h2, h3⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3⟩

/-! ### The four counts -/

/-- **The `p_ready` polls along a run.** -/
theorem mma_pPolls (hpre : Pre Q L mem0) (hg : g < L.threads) {P : Loader.Pro} {d0 : Mma.D}
    {es : List Event} (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P)))
    {b : Nat} (hb : b < 2) :
    okPolls (pReady L (g / L.block) b) es + below2 b (Mm.pPolled d0) =
      below2 b (Mm.pPolled d) := by
  refine mma_count hT (okPoll (pReady L (g / L.block) b)) (fun d => below2 b (Mm.pPolled d))
    (fun _ => True) (fun _ _ => trivial) ?_ hin hd
  intro d1 d' e hin1 hne _ hev hn
  have hpol := mm_next_pPolled hin1 hne hn
  have hokp := mm_okPoll_p_step hpre hg hev hb
  rw [hokp, hpol]
  by_cases hw : d1.site = .pWait
  · have hp : Mm.pPolled d1 = d1.i - 1 := by simp [Mm.pPolled, hw]
    by_cases hok : okW e = true
    · by_cases hm : (d1.i - 1) % 2 = b
      · simp [hw, hok, hm, hp, below2_succ hb]
      · simp [hw, hok, hm, hp, below2_succ hb]
    · simp [hw, hok]
  · simp [hw]

variable (hpre : Pre Q L mem0) (hg : g < L.threads) {P : Loader.Pro} {d0 : Mma.D} {es : List Event}
    (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es) (hE : ∀ e ∈ es, MmRun L g e)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc) {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P)))
include hpre hg hT hE hin hd

/-- **The QK commits to `s_ready` along a run, when every election returns the thread's lane.** -/
theorem mma_sCommits {b : Nat} (hb : b < 2) :
    es.countP (commitsTo (sReady L (g / L.block) b)) + below2 b (Mm.qkDone d0) =
      below2 b (Mm.qkDone d) := by
  refine mma_count hT (commitsTo (sReady L (g / L.block) b))
    (fun d => below2 b (Mm.qkDone d)) (MmRun L g) hE ?_ hin hd
  intro d1 d' e hin1 hne hlr hev hn
  obtain ⟨u, hF⟩ := hev.resolve_right hlr.1.1
  have hdone := mm_next_qkDone hin1 hne hlr.1.2 hlr.2 hn
  have hcm := mm_commitsTo_s hpre hg hF hb
  rw [hcm, hdone]
  by_cases hw : d1.site = .qkCommit
  · have hp : Mm.qkDone d1 = d1.i := by simp [Mm.qkDone, hw]
    by_cases hm : d1.i % 2 = b
    · simp [hw, hm, hp, below2_succ hb]
    · simp [hw, hm, hp, below2_succ hb]
  · simp [hw]

/-- **The second PV commits, to `o_done`, along a run, when every election returns the thread's
lane.** -/
theorem mma_oCommits :
    es.countP (commitsTo (oDone L (g / L.block))) + Mm.oDoneC d0 = Mm.oDoneC d := by
  refine mma_count hT (commitsTo (oDone L (g / L.block))) Mm.oDoneC (MmRun L g) hE ?_ hin hd
  intro d1 d' e hin1 hne hlr hev hn
  obtain ⟨u, hF⟩ := hev.resolve_right hlr.1.1
  have hdone := mm_next_oDoneC hin1 hne hlr.1.2 hlr.2 hn
  have hcm := mm_commitsTo_o hpre hg hF
  rw [hcm, hdone]
  simp

/-- **The commits to `o_final` along a run, when every election returns the thread's lane.** -/
theorem mma_fCommits :
    es.countP (commitsTo (oFinal L (g / L.block))) + Mm.finDone d0 = Mm.finDone d := by
  refine mma_count hT (commitsTo (oFinal L (g / L.block))) Mm.finDone (MmRun L g) hE ?_
    hin hd
  intro d1 d' e hin1 hne hlr hev hn
  obtain ⟨u, hF⟩ := hev.resolve_right hlr.1.1
  have hdone := mm_next_finDone hin1 hne hlr.1.2 hn
  have hcm := mm_commitsTo_f hpre hg hF
  rw [hcm, hdone]
  simp

end
end PTX.Kernels.InklingRelDecode.Proof.SO

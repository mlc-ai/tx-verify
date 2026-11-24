-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingExec
public import Lemmas.Flow.ElectLead

@[expose] public section

/-!
# The MMA warp's PV commits to `kv_empty`, counted along its run

In iteration `i ≥ 1` the MMA warp's elected lane issues the PV MMAs of block `i - 1` and then
commits to `kv_empty ((i - 1) % 3)` (`MmShape.pvCommit1`): the commit completes, once all the
MMAs the thread issued before it have completed, one phase of that barrier. The warp's other
lanes skip the PV half (`Mma.next` at `pvElect`), so whether a thread commits depends on which
lane the election returns; the statements are for a thread all of whose elections return its lane
(`ElectLead`, `LeadRun`), the thread that commits every iteration.

* `Mm.done d`: the PV halves whose commit has been issued at state `d` (the blocks `0 … done - 1`).
* `mm_next_done`, `mm_commitsTo`, `mma_commits`: along a run, the commits to `kv_empty s` number
  `below s (done d) - below s (done d₀)`.
* `mma_commit_exec`: on an execution, the commit to `kv_empty s` at event `k` is for block `i - 1`
  of iteration `i` (state `pvCommit1`), and it is the thread's `n`-th commit to that barrier
  with block `i - 1 = blockOf s n`: the PV commit for block `3 n + s` is the `n`-th notification
  of `kv_empty s`, so it completes the phase `n` that the loader's poll for block `3 (n + 1) + s`
  waits for (`loader_poll_phase`, `use d.i = n + [s < np]`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvEmpty MmShape mma_shape)

noncomputable section
set_option maxRecDepth 100000

/-- The PV commits to `kv_empty` issued at state `d`, when every election returns the thread's
lane: one per completed PV half. -/
def Mm.done (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => d.i - 1
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 => d.i - 1
  | .pvCommit2 | .pvSkip => d.i
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => if d.i = 0 then 0 else d.n

/-- Every election of the run returned the thread's lane, and no event ends the thread. -/
def LeadRun (L : Launch) (g : Nat) (e : Event) : Prop :=
  ¬ Ends e ∧ ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g

open PTX.Kernels.InklingRelDecode.Proof.Mma (BcastRun MmaBcast)

/-- An event of an MMA run whose elections return the thread's lane (`LeadRun`) and whose
broadcasts receive 7 (`Mma.BcastOk`). -/
def MmRun (L : Launch) (g : Nat) (e : Event) : Prop := LeadRun L g e ∧ Mma.BcastOk e

/-- **A step of the MMA warp, for the commits.** -/
theorem mm_next_done {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc)
    (hE : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g) (hB : Mma.BcastOk e)
    (h : Mma.next L g d e = some (some d')) :
    Mm.done d' = Mm.done d + if d.site = .pvCommit1 then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  have hk := fun hs => Mma.next_not_skip hB hs h
  clear hB
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.done, Mma.Site.isSkip]

theorem sReady_ne_kvEmpty {L : Launch} {c b s : Nat} (hs : s < 3) :
    EvW.sReady L c b ≠ kvEmpty L c s := by
  simp only [EvW.sReady, kvEmpty, EvW.barLoc, EvW.sReadyOff, EvW.kvEmptyOff, ne_eq, Loc.mk.injEq]
  omega

theorem oDone_ne_kvEmpty {L : Launch} {c s : Nat} (hs : s < 3) :
    EvW.oDone L c ≠ kvEmpty L c s := by
  simp only [EvW.oDone, kvEmpty, EvW.barLoc, EvW.oDoneOff, EvW.kvEmptyOff, ne_eq, Loc.mk.injEq]
  omega

theorem oFinal_ne_kvEmpty {L : Launch} {c s : Nat} (hs : s < 3) :
    EvW.oFinal L c ≠ kvEmpty L c s := by
  simp only [EvW.oFinal, kvEmpty, EvW.barLoc, EvW.oFinalOff, EvW.kvEmptyOff, ne_eq, Loc.mk.injEq]
  omega

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}

/-- **The event of an MMA state, as a count of commits.** -/
theorem mm_commitsTo (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) {s : Nat}
    (hs : s < 3) :
    commitsTo (kvEmpty L (g / L.block) s) e =
      decide (d.site = .pvCommit1 ∧ (d.i - 1) % 3 = s) := by
  have hsh := mma_shape hpre hg hF
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  case pvCommit1 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, kvEmpty_eq_iff]
  case qkCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, sReady_ne_kvEmpty hs]
  case pvCommit2 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, oDone_ne_kvEmpty hs]
  case finCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, oFinal_ne_kvEmpty hs]
  all_goals first
    | obtain ⟨_, _, rfl, -⟩ := hsh
    | obtain ⟨_, _, rfl⟩ := hsh
    | obtain ⟨_, rfl⟩ := hsh
    | obtain rfl := hsh
    | obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh
  all_goals simp [commitsTo]

/-- **The PV commits along a run, when every election returns the thread's lane.** -/
theorem mma_commits (hpre : Pre Q L mem0) (hg : g < L.threads) {P : Loader.Pro} {d0 : Mma.D}
    {es : List Event} (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es)
    (hE : ∀ e ∈ es, MmRun L g e)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P)))
    {s : Nat} (hs : s < 3) :
    es.countP (commitsTo (kvEmpty L (g / L.block) s)) + below s (Mm.done d0) =
      below s (Mm.done d) := by
  have h := count_trace (M := (WComp.code L g Q).toMachine)
    (commitsTo (kvEmpty L (g / L.block) s))
    (fun σ => match σ with | some (.mma d _) => below s (Mm.done d) | _ => 0)
    (fun σ => ∃ d, σ = some (.mma d P) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    (MmRun L g) (some (.mma d P)) ?_ hT hE ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne⟩ hlr hev hn hσ'
    have hn' : WComp.next L g (.mma d1 P) e = some σ' := hn
    rw [EvW.next_mma_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      obtain ⟨u, hF⟩ := hev.resolve_right hlr.1.1
      have hdone := mm_next_done hin1 hne hlr.1.2 hlr.2 ha
      have hcm := mm_commitsTo hpre hg hF hs
      show below s (Mm.done a) = below s (Mm.done d1) + if commitsTo _ e = true then 1 else 0
      rw [hcm, hdone]
      by_cases hw : d1.site = .pvCommit1
      · have hp : Mm.done d1 = d1.i - 1 := by simp [Mm.done, hw]
        by_cases hm : (d1.i - 1) % 3 = s
        · simp [hw, hm, hp, below_succ hs]
        · simp [hw, hm, hp, below_succ hs]
      · simp [hw]
  · intro j hj
    obtain ⟨d1, h1, h2, h3⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3⟩

variable {X : Execution}

/-- No event before the last of a thread's trace ends the thread. -/
theorem not_ends_take (hg : g < L.threads) (hX : Consistent L kernel WComp.asms mem0 X) {k : Nat}
    (hk : k < (X.tr g).length) : ∀ e ∈ (X.tr g).take k, ¬ Ends e := by
  intro e he hend
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hj
  obtain ⟨o, hr⟩ := hX.thr g hg
  have hj' : (X.tr g)[j]? = some ((X.tr g).take k)[j] := by
    rw [List.getElem_take]
    exact List.getElem?_eq_getElem (by omega)
  have := Run.end_last hr hj' hend
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring

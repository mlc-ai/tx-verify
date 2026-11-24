-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingCommit

@[expose] public section

/-!
# The loader's arrivals and copies on `kv_ready`, counted along its run

Per block `i` the loader issues, on `kv_ready (i % 3)`:

* **one `mbarrier.arrive.expect_tx` of 65536 bytes (count 1) by lane 0** (the `arrive` site, taken
  only by the thread whose lane is 0: `Loader.D.ln`), after its successful poll of `kv_empty`;
* **eight tensor copies of 8192 bytes** (`cp0a … cp3b`: K and V boxes of slabs 0 and 1, four
  elected-lane sites with two copies each), by the thread an election returned its lane to.

`Ld.arrIters d` is the number of iterations whose arrival site lies behind `d`, `Ld.cpMu s d` the
number of copies on `kv_ready s` a thread that wins every election has issued at `d`.
Both are measures of the abstract state that change exactly by the event's contribution:

* `loader_arrives`: along a run of the loader machine, the arrivals on `kv_ready s` number
  `below s (arrIters d) - below s (arrIters d₀)` for a lane-0 thread and none for another lane
  (`arrCnt`).
* `loader_copies`: along a run all of whose elections returned the thread's lane (`LeadRun`), the
  copies completing on `kv_ready s` number `cpMu s d - cpMu s d₀`.
* `loader_copies_nonlead`: along a run none of whose elections returned the thread's lane, there
  is no copy.

The run is relative to a loop state (an anchor), as for the polls (`RingLoader`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty LdShape MapReg loader_shape)

noncomputable section
set_option maxRecDepth 100000

/-! ### The measures -/

/-- The sites of an iteration after its arrival site. -/
def Ld.afterArrive : Loader.Site → Bool
  | .ldb0 | .wb1 | .el0 | .cp0a | .cp0b | .wb2 | .el1 | .cp1a | .cp1b | .ldb1 | .wb3 | .el2
  | .cp2a | .cp2b | .wb4 | .el3 | .cp3a | .cp3b => true
  | _ => false

/-- The iterations whose arrival site lies behind state `d`. -/
def Ld.arrIters (d : Loader.D) : Nat := d.i + if Ld.afterArrive d.site then 1 else 0

/-- The arrivals a thread has made at state `d`: its iterations' if it is lane 0, none else. -/
def Ld.arrCnt (d : Loader.D) : Nat := if d.ln then Ld.arrIters d else 0

/-- The copy sites. -/
def Ld.isCp : Loader.Site → Bool
  | .cp0a | .cp0b | .cp1a | .cp1b | .cp2a | .cp2b | .cp3a | .cp3b => true
  | _ => false

/-- The copies of the current iteration a thread that wins every election has issued before
the site. -/
def Ld.cpIn : Loader.Site → Nat
  | .cp0b => 1
  | .wb2 | .el1 | .cp1a => 2
  | .cp1b => 3
  | .ldb1 | .wb3 | .el2 | .cp2a => 4
  | .cp2b => 5
  | .wb4 | .el3 | .cp3a => 6
  | .cp3b => 7
  | _ => 0

/-- The copies on `kv_ready s` that a thread winning every election has issued at state `d`. -/
def Ld.cpMu (s : Nat) (d : Loader.D) : Nat :=
  8 * below s d.i + if d.i % 3 = s then Ld.cpIn d.site else 0

/-! ### A step -/

/-- The elections of the run returned the thread's lane. -/
def ElectsLane (L : Launch) (g : Nat) (e : Event) : Prop :=
  ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g

/-- **A step of the loader changes the arrival measure.** -/
theorem ld_next_arr {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event} (hd : Ld.InLoop d)
    (hl : d.site = .arrive → d.ln = true) (h : Loader.next L g d e = some (some d')) :
    Ld.InLoop d' ∧ d'.ln = d.ln ∧ (d'.site = .arrive → d'.ln = true) ∧
      Ld.arrCnt d' = Ld.arrCnt d + if d.site = .arrive then 1 else 0 := by
  refine ⟨Ld.inLoop_next hd h, ?_⟩
  have hm := Ld.mod_of_loop hd
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨h1, h2, h3, -⟩ := hd
  simp only at h1 h2 h3 hl hm
  cases site
  case setMaxDec => exact absurd rfl h1
  case ld0 => exact absurd rfl h2
  case ld1 => exact absurd rfl h3
  all_goals
    try simp only [Loader.Site.inLoop, forall_const] at hm
    simp only [Loader.next, Loader.afterIter, hm] at h
    (repeat' split at h)
    all_goals first
      | (obtain rfl := Option.some.inj (Option.some.inj h)
         simp_all [Ld.arrCnt, Ld.arrIters, Ld.afterArrive])
      | cases h

/-- **A step of the loader changes the copy measure.** `i` changes only at the last copy, where
it moves on by one. -/
theorem ld_next_cp {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event} (hd : Ld.InLoop d)
    (hE : ElectsLane L g e) (h : Loader.next L g d e = some (some d')) :
    Ld.InLoop d' ∧
      ((d.site = .cp3b ∧ d'.i = d.i + 1 ∧ Ld.cpIn d'.site = 0) ∨
        (d.site ≠ .cp3b ∧ d'.i = d.i ∧ Ld.cpIn d'.site =
          Ld.cpIn d.site + if Ld.isCp d.site then 1 else 0)) := by
  refine ⟨Ld.inLoop_next hd h, ?_⟩
  have hm := Ld.mod_of_loop hd
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨h1, h2, h3, -⟩ := hd
  simp only at h1 h2 h3 hm
  cases site
  case setMaxDec => exact absurd rfl h1
  case ld0 => exact absurd rfl h2
  case ld1 => exact absurd rfl h3
  all_goals
    try simp only [Loader.Site.inLoop, forall_const] at hm
    simp only [Loader.next, Loader.afterIter, hm] at h
    (repeat' split at h)
    all_goals first
      | (obtain rfl := Option.some.inj (Option.some.inj h)
         simp_all [Ld.cpIn, Ld.isCp, ElectsLane])
      | cases h

/-! ### The events at a state -/

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}

theorem ld_okArr (hpre : Pre Q L mem0) {d : Loader.D} {P : Loader.Pro} (hmap : MapReg P)
    (hrg : Loader.Rng d)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) (s : Nat) :
    arrivesOn (kvReady L (g / L.block) s) e = decide (d.site = .arrive ∧ d.i % 3 = s) := by
  have hsh := loader_shape hpre hmap hrg hF
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  cases site <;> simp only [LdShape] at hsh
  case arrive =>
    subst hsh
    simp [arrivesOn_arrive rfl, kvReady_eq_iff, eq_comm]
  all_goals first
    | (obtain ⟨_, rfl⟩ := hsh; simp [arrivesOn, sourceArrive])
    | (obtain ⟨_, _, rfl, -⟩ := hsh; simp [arrivesOn, sourceArrive])

/-- The copy of a loader state completes on the `kv_ready` barrier of its ring slot. -/
theorem ldCopy_mbar (d : Loader.D) (b : Bool × Nat × Nat) :
    (EvW.ldCopy Q L g d b).mbar = kvReady L (g / L.block) (d.i % 3) := rfl

/-- The tensor issues of the loader's copy sites complete on the `kv_ready` of its slot. -/
theorem ld_okIssue (hpre : Pre Q L mem0) {d : Loader.D} {P : Loader.Pro} (hmap : MapReg P)
    (hrg : Loader.Rng d)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) (s : Nat) :
    issuesTo (kvReady L (g / L.block) s) e = decide (Ld.isCp d.site ∧ d.i % 3 = s) := by
  have hsh := loader_shape hpre hmap hrg hF
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  cases site <;> simp only [LdShape] at hsh
  all_goals first
    | (obtain ⟨b, -, rfl⟩ := hsh
       simp [issuesTo, ldCopy_mbar, Ld.isCp, kvReady_eq_iff, eq_comm])
    | (obtain ⟨_, rfl⟩ := hsh)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; simp [issuesTo, Ld.isCp])

/-- The arrivals on `kv_ready s` a thread has made at state `d`. -/
def Ld.arrMu (s : Nat) (d : Loader.D) : Nat := if d.ln then below s (Ld.arrIters d) else 0

variable {es : List Event}

variable (hpre : Pre Q L mem0) {P : Loader.Pro} (hmap : MapReg P) {d0 : Loader.D}
    (hT : (WComp.code L g Q).toMachine.Trace (some (.loader d0 P)) es)
include hpre hmap hT

/-- **The loader's arrivals along a run.** Along a run of the loader machine from a loop state
`d₀` that stays in the loop and in which no event ends the thread, the arrivals on `kv_ready s`
(of any size) are exactly the thread's `arrive` sites of slot `s`: they number
`arrMu s d - arrMu s d₀`, which is `below s (arrIters d) - below s (arrIters d₀)` for lane 0 and
zero for every other lane. -/
theorem loader_arrives (hnE : ∀ e ∈ es, ¬ Ends e)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.loader d0 P))
      (es.take j) = some (some (.loader d P)) ∧ Ld.InLoop d ∧ d.site ≠ .setMaxInc ∧
      (d.site = .arrive → d.ln = true)) {d : Loader.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.loader d0 P)) es = some (some (.loader d P)))
    (s : Nat) (hs : s < 3) :
    es.countP (arrivesOn (kvReady L (g / L.block) s)) + Ld.arrMu s d0 = Ld.arrMu s d := by
  have h := count_trace (M := (WComp.code L g Q).toMachine)
    (arrivesOn (kvReady L (g / L.block) s))
    (fun σ => match σ with | some (.loader d _) => Ld.arrMu s d | _ => 0)
    (fun σ => ∃ d, σ = some (.loader d P) ∧ Ld.InLoop d ∧ d.site ≠ .setMaxInc ∧
      (d.site = .arrive → d.ln = true))
    (fun e => ¬ Ends e) (some (.loader d P)) ?_ hT hnE ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne, hl1⟩ hnend hev hn hσ'
    have hn' : WComp.next L g (.loader d1 P) e = some σ' := hn
    rw [EvW.next_loader_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      obtain ⟨u, hF⟩ := hev.resolve_right hnend
      obtain ⟨-, hln, -, hcnt⟩ := ld_next_arr hin1 hl1 ha
      have hok := ld_okArr hpre hmap hin1.2.2.2 hF s
      show Ld.arrMu s a = Ld.arrMu s d1 + if arrivesOn _ e = true then 1 else 0
      rw [hok]
      by_cases hl : d1.ln = true
      · have hc : Ld.arrIters a = Ld.arrIters d1 + if d1.site = .arrive then 1 else 0 := by
          simp only [Ld.arrCnt, hln, hl, ite_true] at hcnt
          omega
        simp only [Ld.arrMu, hln, hl, ite_true, hc]
        by_cases hw : d1.site = .arrive
        · have hai : Ld.arrIters d1 = d1.i := by simp [Ld.arrIters, Ld.afterArrive, hw]
          by_cases hm : d1.i % 3 = s <;> simp [hw, hm, hai, below_succ hs]
        · simp [hw]
      · have hw : d1.site ≠ .arrive := fun h => hl (hl1 h)
        simp [Ld.arrMu, hln, hl, hw]
  · intro j hj
    obtain ⟨d1, h1, h2, h3, h4⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3, h4⟩

/-- **The loader's copies along a run, for the thread that wins every election.** Along a run from
a loop state `d₀` that stays in the loop, in which no event ends the thread and every election
returns the thread's lane, the copies completing on `kv_ready s` number `cpMu s d - cpMu s d₀`:
eight per block of slot `s` the run has passed. -/
theorem loader_copies (hE : ∀ e ∈ es, LeadRun L g e)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.loader d0 P))
      (es.take j) = some (some (.loader d P)) ∧ Ld.InLoop d ∧ d.site ≠ .setMaxInc) {d : Loader.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.loader d0 P)) es = some (some (.loader d P)))
    (s : Nat) (hs : s < 3) :
    es.countP (issuesTo (kvReady L (g / L.block) s)) + Ld.cpMu s d0 = Ld.cpMu s d := by
  have h := count_trace (M := (WComp.code L g Q).toMachine)
    (issuesTo (kvReady L (g / L.block) s))
    (fun σ => match σ with | some (.loader d _) => Ld.cpMu s d | _ => 0)
    (fun σ => ∃ d, σ = some (.loader d P) ∧ Ld.InLoop d ∧ d.site ≠ .setMaxInc)
    (LeadRun L g) (some (.loader d P)) ?_ hT hE ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne⟩ hlr hev hn hσ'
    have hn' : WComp.next L g (.loader d1 P) e = some σ' := hn
    rw [EvW.next_loader_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      obtain ⟨u, hF⟩ := hev.resolve_right hlr.1
      obtain ⟨-, hstep⟩ := ld_next_cp hin1 hlr.2 ha
      have hok := ld_okIssue hpre hmap hin1.2.2.2 hF s
      show Ld.cpMu s a = Ld.cpMu s d1 + if issuesTo _ e = true then 1 else 0
      rw [hok]
      rcases hstep with ⟨h3, hi, hc⟩ | ⟨h3, hi, hc⟩
      · have hcp : Ld.cpIn d1.site = 7 := by simp [h3, Ld.cpIn]
        have hisCp : Ld.isCp d1.site = true := by simp [h3, Ld.isCp]
        simp only [Ld.cpMu, hi, hc, hcp, hisCp, below_succ hs, true_and]
        by_cases hm : d1.i % 3 = s
        · simp [hm]
          omega
        · simp [hm]
      · simp only [Ld.cpMu, hi, hc]
        by_cases hm : d1.i % 3 = s
        · simp [hm]
          omega
        · simp [hm]
  · intro j hj
    obtain ⟨d1, h1, h2, h3⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Ring

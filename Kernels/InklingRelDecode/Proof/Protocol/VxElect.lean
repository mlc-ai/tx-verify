-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsPkg
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-!
# The elections of the MMA warp, and `Mbar.Route.lane_commit`

* `elects`: the number of elections an MMA-warp thread made along its run from the entry of the
  role (`setMaxReg`) to a state, a function of the state (`next_elects`, `elect_cnt`). The
  elections before the entry (the worker dispatch's roles, the loader's) are not counted here;
  they are the count at the entry, which the proof compares between two lanes.
* `elect_site_state`: an event at the position of one of the three elections of the MMA role is
  fired from an MMA-warp state at that site (the other machines have no such position).
* `laneCommit_of`: `Hs.LaneCommit`. The committing lane's commit to `s_ready b` at the QK commit of
  iteration `I` follows its election at `qkElect` of `I`. Lane `h`'s election of the same instance
  is at the same position, so at `qkElect` of an iteration `I'` of its own run. The two elections
  have one ordinal (`electOrdinal`, the masks are full). So does the committing lane's first
  election in its run with its partner in `h`, which gives that `h` made at most as many
  elections before its entry as the committing lane; hence `I' ≥ I`, and at `qkElect` of `I'`
  lane `h` has polled `p_ready b` at least `below2 b (I - 1)` times, more than `j`. The poll's
  return precedes the election (a spinning poll), which precedes the commit (`elect_depStep`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Vx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal commitSpec)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The count of elections along the MMA role -/

/-- The three election sites of the MMA role. -/
def elSite : Mma.Site → Bool
  | .qkElect | .pvElect | .finElect => true
  | _ => false

/-- The elections made from the entry of the role to state `d`: one per QK half and one per PV
half that reached its election, and the final one. -/
def elects (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect => d.i + (d.i - 1)
  | .qk _ | .qkCommit => d.i + (d.i - 1) + 1
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .qkSkip => min (d.i + 1) d.n + (d.i - 1)
  | .pv _ | .pvCommit1 | .pvCommit2 | .pvSkip => min (d.i + 1) d.n + (d.i - 1) + 1
  | .finBar | .finElect => if d.i = 0 then 0 else d.n + d.n
  | .finCommit | .bar1 | .setMaxRegInc => (if d.i = 0 then 0 else d.n + d.n) + 1

set_option linter.unusedTactic false in
/-- **A step of the MMA warp, for the elections.** -/
theorem next_elects {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc) (hB : Mma.BcastOk e) (h : Mma.next L g d e = some (some d')) :
    elects d' = elects d + if elSite d.site then 1 else 0 := by
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
    all_goals simp_all [elects, elSite, Mma.Site.isSkip]
    all_goals omega

/-- At an election site a step is an election. -/
theorem next_elect_kind {d d' : Mma.D} {e : Event} (hs : elSite d.site = true)
    (h : Mma.next L g d e = some (some d')) : isElectEv e = true := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  obtain ⟨pc, k⟩ := e
  cases site <;> simp only [elSite, Bool.false_eq_true] at hs
  all_goals
    simp only [Mma.next] at h
    cases k <;> simp_all [isElectEv]

/-- The event of a state is an election exactly at the election sites. -/
theorem shape_isElect {d : Mma.D} {e : Event} (hsh : EvW.MmShape L g d e) :
    isElectEv e = elSite d.site := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [EvW.MmShape, EvW.QkIssue, EvW.PvIssue] at hsh
  all_goals first
    | (subst hsh; rfl)
    | (obtain ⟨_, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; rfl)
    | (obtain ⟨_, _, -, -, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, _, -, -, -, rfl⟩ := hsh; rfl)

/-- **The elections of an MMA-warp thread at a state**: those before the entry of its run, plus
`elects` of the state. -/
theorem elect_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : Mma.MmaBcast L X)
    (hg : g < L.threads) {k : Nat}
    {d : Mma.D} {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧ St Q L X g k0 = some (some (.w (.mma d0 P))) ∧
      d0.site = .setMaxReg ∧ elections X g k = elections X g k0 + elects d ∧
      ∀ j, k0 ≤ j → j < k → ∃ dj, St Q L X g j = some (some (.w (.mma dj P))) := by
  have hw : 4 ≤ WComp.warpOf L g := (Rd.mma_anchor hpre hX hf hR hg hk hσ).1
  obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := Rd.mma_back hX hf k hk hσ
  have h0w : wAt Q L X g k0 = some (some (.mma d0 P)) := Rd.wAt_of_st k0 (by omega) h0
  have hdw : wAt Q L X g k = some (some (.mma d P)) := Rd.wAt_of_st k (by omega) hσ
  have hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc := by
    intro j hj1 hj2
    obtain ⟨dj, hdj, hI, hne⟩ := hch j hj1 hj2
    exact ⟨dj, Rd.wAt_of_st j (by omega) hdj, hI, hne⟩
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0w hdw hin
  have hc := SO.mma_count hT isElectEv elects Mma.BcastOk
    (fun e he => hB g hg (by
      simpa [RoleWarp, Ledger.roleWarp] using roleWarp_inv hf.roleWarp k _ hk.le hσ) e
      (List.mem_of_mem_drop (List.mem_of_mem_take he))) ?_ hin' hend
  · have hz : elects d0 = 0 := by simp [elects, hs0]
    refine ⟨k0, d0, hk0, h0, hs0, ?_, fun j h1 h2 => ?_⟩
    · unfold elections
      rw [Ring.countP_take_split _ _ hk0, ← hc, hz, Nat.add_zero]
    · obtain ⟨dj, hdj, -, -⟩ := hch j h1 h2
      exact ⟨dj, hdj⟩
  · intro d1 d' e hin1 hne hb hev hn
    rw [next_elects hin1 hne hb hn]
    have hk : isElectEv e = elSite d1.site := by
      rcases hev with ⟨u, hF⟩ | hend
      · exact shape_isElect (EvW.mma_shape hpre hg hF)
      · cases hs : elSite d1.site
        · obtain ⟨pc, k⟩ := e
          rcases hend with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;> rfl
        · have := next_elect_kind hs hn
          obtain ⟨pc, k⟩ := e
          rcases hend with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;>
            simp [isElectEv] at this
    rw [hk]

/-! ### The states at the election positions -/

/-- The positions of the MMA role's elections. -/
def elPcs : List Nat := [Mma.Site.qkElect.pc, Mma.Site.pvElect.pc, Mma.Site.finElect.pc]

theorem dstart_pc_notEl (s : DStart.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals decide +kernel

theorem pro_pc_notEl (s : ProA.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals decide +kernel

theorem sm_pc_notEl (s : Sm.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem epi_pc_notEl (s : Epi.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_notEl (s : Worker.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals decide +kernel

theorem idle_pc_notEl (s : Worker.Idle.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_notEl (s : Loader.Site) : s.pc ∉ elPcs := by
  cases s
  all_goals decide +kernel

theorem exit_pc_notEl (s : WComp.ExitSite) : s.pc ∉ elPcs := by
  cases s
  all_goals decide +kernel

/-- An MMA site at the position of an election is that election. -/
theorem mma_site_of_pc (s t : Mma.Site) (ht : elSite t = true) (h : s.pc = t.pc) : s = t := by
  cases t <;> simp only [elSite, Bool.false_eq_true] at ht
  all_goals
    revert h
    cases s
    all_goals try (rename_i j; revert j)
    all_goals decide +kernel

/-- **A state at the position of an MMA election is an MMA warp state.** -/
theorem el_state {s : TSt} (h : TSt.pc s ∈ elPcs) : ∃ d P, s = .w (.mma d P) := by
  cases s with
  | d s =>
    cases s with
    | dstart d => exact absurd h (dstart_pc_notEl d.site)
    | pro d => exact absurd h (pro_pc_notEl d.site)
    | sm d => exact absurd h (sm_pc_notEl d.site)
    | epi d => exact absurd h (epi_pc_notEl d.site)
  | w s =>
    cases s with
    | worker w => exact absurd h (worker_pc_notEl w.site)
    | idle d => exact absurd h (idle_pc_notEl d.site)
    | loader d _ => exact absurd h (loader_pc_notEl d.site)
    | mma d P => exact ⟨d, P, rfl⟩
    | exit x => exact absurd h (exit_pc_notEl x.site)

/-- The event of an MMA-warp state that is an election is at an election site. -/
theorem elect_at_site (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc mask inst l : Nat} {d : Mma.D} {P : Loader.Pro}
    (he : X.Elect (g, k) pc mask inst l)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    elSite d.site = true ∧ pc = d.site.pc := by
  have hg : g < L.threads := event_thread_lt hX he
  have he' : (X.tr g)[k]? = some ⟨pc, .elect mask inst l⟩ := he
  have hpc := Frame.event_pc hf.sound hX he hσ
  obtain ⟨o', hF⟩ := (Frame.trace hf.sound hX hg).fired_at he' hσ
  cases o' with
  | none =>
    exfalso
    obtain ⟨t', -, hf'⟩ := hF
    rcases fires_none_ends hf' with ⟨f, hf''⟩ | hx <;> simp_all
  | some u =>
    obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
    have hsh := EvW.mma_shape hpre hg (d := d) (P := P) ⟨t', ⟨ha, hi.2⟩, hf'⟩
    have := shape_isElect hsh
    simp only [isElectEv] at this
    exact ⟨this.symm, hpc⟩

/-- **An election at the position of an MMA election** is fired from an MMA-warp state at that
site. -/
theorem elect_site_state (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k pc mask inst l : Nat} {t : Mma.Site} (ht : elSite t = true)
    (he : X.Elect (g, k) pc mask inst l) (hpc : pc = t.pc) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧ d.site = t := by
  have hget : X.get (g, k) = some ⟨pc, .elect mask inst l⟩ := he
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked hget (by intro _ _ h; cases h)
  have hp := Frame.event_pc hf.sound hX hget hσ
  have hmem : TSt.pc s ∈ elPcs := by
    have : TSt.pc s = t.pc := by rw [← hpc]; exact hp.symm
    rw [this]
    cases t <;> simp [elSite] at ht <;> simp [elPcs]
  obtain ⟨d, P, rfl⟩ := el_state hmem
  refine ⟨d, P, hσ, mma_site_of_pc _ _ ht ?_⟩
  rw [← hpc]
  exact hp.symm

end
end PTX.Kernels.InklingRelDecode.Proof.Vx

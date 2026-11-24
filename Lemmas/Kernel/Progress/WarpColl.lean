-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Warp
public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # Progress at a warp collective, with a kernel's next-event classification

A proof tool, generic over the kernel (promoted from FA4's `Proof/Progress/WarpColl.lean`). The
progress interface gains one parameter: the kernel's classification of the machine states whose
next event is a warp collective (`AtColl g d`: a shuffle, an election, a vote or a warp barrier
site of the role tables). With the facts `WarpCollFacts` about those states, a released pending
thread at such a state steps (`Sched.warpColl_steps`):

* no lane of its warp has made more warp collectives (`Sched.no_ahead`, from the recorded static
  parts `shape`, every mask full, no mode vote in the code);
* a lane that has made at most as many and is not at the same collective is earlier (`lag`) and has
  not exited (`exit`): it is a pending thread of smaller rank;
* otherwise every lane is at the collective and released (`last`: the lanes' last events are
  unblocking, or one register request or one warp-collective `tcgen05` event of the warp), and
  either some lane's run reaches undefined behaviour, which performs it (`hub`), or all lanes fire
  templates of one static part at one position (`shape`) and the warp performs one instance
  (`Sched.coll_batch`).

The facts are the kernel's: its role tables (which sites are collectives, their static parts in
order), its ledgers (the collective counts at the exit) and its time table (`lag`). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

/-- **The facts of a kernel's warp collectives**, for the states classified as at a collective
(`AtColl`), with the lanes' warp key `key`. -/
structure WarpCollFacts (M : Timed K A L) (X : Execution) (key : Nat → κ)
    (AtColl : ∀ g, (M.code g).D → Prop) : Prop where
  /-- The static part of a lane's `n`-th warp collective and the position of its next one are a
  function of the warp and `n`; every mask names the whole warp. -/
  shape : ∃ F : κ → Nat → Nat × CollShape,
    (∀ c n, (F c n).2.Full) ∧
    (∀ {g k : Nat} {e : Event} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some e →
      isWarpColl e = true →
      kindShape e.kind = some (F (key g) (((X.tr g).take k).countP isWarpColl)).2) ∧
    (∀ {g : Nat} {d : (M.code g).D} {t : TState} {m : Tmpl}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
      (M.code g).AtD d t → out K A L g t = .ev m → (∃ f, m = .ub f) ∨
        (t.pc = (F (key g) ((X.tr g).countP isWarpColl)).1 ∧
          tmplShape m = some (F (key g) ((X.tr g).countP isWarpColl)).2))
  /-- The last event before a lane's `n`-th warp collective never blocks, or it is the lane's
  first register request with operands fixed by the warp and `n`, or a warp-collective `tcgen05`
  event other than a paired Tensor Memory operation, of an ordinal fixed by the warp and `n`. -/
  last : ∃ R : κ → Nat → Option ((Nat × Bool × Nat) ⊕ Nat),
    ∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
      match R (key g) ((X.tr g).countP isWarpColl) with
      | none => ∀ q, X.get (g, (X.tr g).length - 1) = some q → Unblocking q.kind
      | some (.inl (pc, inc, n)) => ∃ inst,
        X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
          SetMaxNReg.ordinal X (g, (X.tr g).length - 1) = 0
      | some (.inr k) => X.TcK (g, (X.tr g).length - 1) k ∧
        ∀ pc grp dst act, X.get (g, (X.tr g).length - 1) ≠ some ⟨pc, .tc (.resource grp dst act)⟩
  /-- A lane exits after a number of warp collectives fixed by its warp, more than a lane at a
  warp collective has made. -/
  exit : ∃ T : κ → Nat,
    (∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
      (X.tr g).countP isWarpColl < T (key g)) ∧
    (∀ {g k pc : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some ⟨pc, .exit⟩ →
      T (key g) ≤ ((X.tr g).take k).countP isWarpColl)
  /-- A lane of the warp of a thread at its `n`-th warp collective that has made at most `n` of
  them and is not at its `n`-th is earlier. -/
  lag : ∀ {g h : Nat} {d : (M.code g).D}, g < L.threads → h < L.threads → SameWarp L g h →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
    (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl →
    ¬ ((X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl ∧
      ∃ d', Frame.stateAt M.code X h (X.tr h).length = some (some d') ∧ AtColl h d') →
    threadTime M X h < M.time g d

variable {key : Nat → κ} {AtColl : ∀ g, (M.code g).D → Prop}

/-- The recorded static parts of the warp collectives. -/
theorem WarpCollFacts.warpRec (hw : WarpCollFacts M X key AtColl) : WarpRec M.code X key := by
  obtain ⟨F, hfull, hrec, -⟩ := hw.shape
  exact ⟨fun c n => (F c n).2, hfull, hrec⟩

/-- **A lane at the warp collective of a released lane is released**, both having made equally
many warp collectives. -/
theorem WarpCollFacts.lane_released (hw : WarpCollFacts M X key AtColl)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h) {g h : Nat} (hg : g < L.threads)
    (hs : SameWarp L g h) {d : (M.code g).D} {dh : (M.code h).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hσh : Frame.stateAt M.code X h (X.tr h).length = some (some dh)) (hkh : AtColl h dh)
    (hn : (X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl)
    (hrel : Step.Released L X g) : Step.Released L X h := by
  obtain ⟨R, hR⟩ := hw.last
  have hlg := hR hg hσ hk
  have hlh := hR hs.1.2.1 hσh hkh
  rw [hn, ← hkey hs] at hlh
  revert hlg hlh
  cases R (key g) ((X.tr g).countP isWarpColl) with
  | none =>
    intro _ hlh
    cases hq : X.get (h, (X.tr h).length - 1) with
    | none =>
      have h0 : X.tr h = [] := by
        by_contra hne
        have hlt : (X.tr h).length - 1 < (X.tr h).length := by
          have := List.length_pos_of_ne_nil hne
          omega
        have : X.get (h, (X.tr h).length - 1) ≠ none := by
          simp [Execution.get, List.getElem?_eq_getElem hlt]
        exact this hq
      exact released_nil h0
    | some q => exact released_of_unblocking hq (hlh q hq)
  | some r =>
    rcases r with ⟨pc, inc, n⟩ | k
    · rintro ⟨ig, hqg, hog⟩ ⟨ih, hqh, hoh⟩
      exact released_of_reg hqg hrel ⟨hs, hog.trans hoh.symm, pc, inc, n, ig, ih, hqg, hqh⟩
    · rintro ⟨hKg, -⟩ ⟨hKh, hres⟩
      exact released_of_tc hs hrel hKg hKh hres

/-- **A lane of the warp of a lane at a warp collective has not exited** when it has made at most
as many warp collectives. -/
theorem WarpCollFacts.lane_noExit (hw : WarpCollFacts M X key AtColl)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (htr : Frame.Tracked M.code X)
    (hub : ¬ HasUb X) (hcl : ∀ h, ¬ ClcCanceled L X h) {g h : Nat} {d : (M.code g).D}
    (hg : g < L.threads) (hs : SameWarp L g h)
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hle : (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl) :
    Frame.Pending L X h := by
  obtain ⟨T, hT1, hT2⟩ := hw.exit
  refine ⟨hs.1.2.1, hcl h, fun pc hl => ?_⟩
  have hex := exit_get hl
  obtain ⟨dx, hdx⟩ := Frame.state_of_noUb hsound hX htr hub hex
  have h1 := hT1 hg hσ hk
  have h2 := hT2 hs.1.2.1 hdx hex
  have h3 := Flow.countP_take_mono isWarpColl (X.tr h) (Nat.sub_le (X.tr h).length 1)
  rw [List.take_length] at h3
  rw [← hkey hs] at h2
  omega

/-- **Progress at a warp collective.** A released pending thread whose state at its trace's end
is at a warp collective steps. -/
theorem warpColl_steps (hK : K.code.all (fun ins => !voteModeOp ins.op) = true)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hw : WarpCollFacts M X key AtColl)
    (hb : L.block % 32 = 0) (hlaunch : ∀ h, Step.Launched L X h)
    (hcl : ∀ h, ¬ ClcCanceled L X h)
    (happ : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hrel : Step.Released L X g) : Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := safe_noUb (hs.2 X hX)
  obtain ⟨tg, hrg⟩ := Frame.run_some hX hub hp
  have hle : ∀ h, SameWarp L g h → (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl :=
    fun h hsw => Nat.le_of_not_lt fun hlt =>
      no_ahead hK hkey hX hsound htr hub hw.warpRec hg hsw hrg hlt
  obtain ⟨F, hfullF, -, hshape⟩ := hw.shape
  by_cases hall : ∀ h, SameWarp L g h →
      (X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl ∧
      ∃ dh, Frame.stateAt M.code X h (X.tr h).length = some (some dh) ∧ AtColl h dh
  · -- every lane at the collective
    have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hsw => by
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      exact hw.lane_released hkey hg hsw hσ hk hσh hkh hn hrel
    have hfire : ∀ h, SameWarp L g h → ∃ t t1 m, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev m ∧
        ((∃ f, m = .ub f) ∨ (t1.pc = (F (key g) ((X.tr g).countP isWarpColl)).1 ∧
          tmplShape m = some (F (key g) ((X.tr g).countP isWarpColl)).2)) := by
      intro h hsw
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      have hh := hsw.1.2.1
      obtain ⟨t, hr⟩ := Frame.run_some hX hub
        (hw.lane_noExit hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw))
      obtain ⟨t1, ins, hτ, hat, -, -, hout⟩ := Frame.end_at hsound hh hr hσh
      have hsh := hshape hh hσh hkh hat hout
      rw [hn, ← hkey hsw] at hsh
      exact ⟨t, t1, _, hr, hτ, hout, hsh⟩
    by_cases hubl : ∃ h, SameWarp L g h ∧ ∃ t t1 f, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev (.ub f)
    · obtain ⟨h, hsw, t, t1, f, hr, hτ, hout⟩ := hubl
      exact .inl (hubx hsw.1.2.1 (hrels h hsw) hr hτ hout)
    · push Not at hubl
      refine .inl (coll_batch hX hb hg (pc := (F (key g) ((X.tr g).countP isWarpColl)).1)
        (hfullF (key g) ((X.tr g).countP isWarpColl)) (fun h hsw => ?_)
        (fun h _ => .inr (hlaunch h)) happ hrels)
      obtain ⟨t, t1, m, hr, hτ, hout, hm⟩ := hfire h hsw
      rcases hm with ⟨f, rfl⟩ | ⟨hpc, hsh⟩
      · exact (hubl h hsw t t1 f hr hτ hout).elim
      · exact ⟨t, t1, m, hr, hτ, hout, hpc, hsh⟩
  · -- a lane not at the collective is earlier
    push Not at hall
    obtain ⟨h, hsw, hnot⟩ := hall
    have hlag := hw.lag hg hsw.1.2.1 hsw hσ hk (hle h hsw) fun ⟨hn, dh, hσh, hkh⟩ =>
      hnot hn dh hσh hkh
    have hph := hw.lane_noExit hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw)
    have htime : threadTime M X h < threadTime M X g := by
      rw [threadTime_of hσ]
      exact hlag
    refine .inr ⟨X, .thread h, hmax, hph, ?_⟩
    rw [rank_released hrel]
    exact rank_lt_of_time_lt htime

end

end PTX.Sched

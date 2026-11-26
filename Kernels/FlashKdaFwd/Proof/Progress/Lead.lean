-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpCollRel
public import Lemmas.Kernel.Progress.Matrix

@[expose] public section

/-! # Warp collectives when an assumption constrains elections

Kernel-independent proof tools (candidates for `Lemmas/Kernel/Progress/`). They are the
library's progress template for a shuffle or an election, restated for a kernel one of whose
assumptions constrains the leader an election returns.

Why the library's own templates do not fit such a kernel. `Sched.warpColl_steps` and
`Sched.warpColl_steps_rel` ask that the assumptions' execution constraints (`Assumption.wf`)
survive the append of *any* events that read no memory (`happ`). An assumption "every full-mask
election elects lane 0" does not survive the append of an election with another leader, so that
premise is false for it. And `Sched.coll_batch` takes the leader of a first election from
`Step.exists_leader`, which picks the lane of the pending thread, not the lane the assumption
demands.

What is here instead.

* `QuietFor lead k`: the event kind `k` reads no memory, and if it is an election its leader is
  `lead`. These are the events the constraint of such an assumption survives.
* `coll_batch_lead`: the lanes of a warp, all released and all at one shuffle or one election,
  perform one instance; an election elects `lead`. It calls the per-kind extension lemmas
  (`Step.shfl_counted_extension_with_assumptions`, `Step.elect_counted_extension`), which ask
  for the assumptions' constraints of the one extension they build.
* `CollLead`, `warpColl_steps_lead`: the progress step of a released pending thread at a warp
  collective (the counterpart of `Sched.warpColl_steps_rel`).
* `quietFor_matrixBatch`: the matrix events of a warp matrix instance are quiet. The library's
  template for them, `Sched.matrix_steps`, asks for the constraints of one matrix instance
  only, so it applies as it is.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Step

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

/-- The event kind reads no memory, and an election among such kinds elects `lead`. -/
def QuietFor (lead : Nat) (k : Kind) : Prop :=
  k.readsMem = false ∧ ∀ mask inst l, k = .elect mask inst l → l = lead

/-- A kind that reads no memory and is no election is quiet for every leader. -/
theorem QuietFor.of_not_elect {lead : Nat} {k : Kind} (hr : k.readsMem = false)
    (he : ∀ mask inst l, k ≠ .elect mask inst l) : QuietFor lead k :=
  ⟨hr, fun mask inst l h => (he mask inst l h).elim⟩

/-- **The warp performs one instance of a shuffle or of an election that elects `lead`**: a
counted extension. `lead` is a lane, and the leader of every earlier full-mask election of the
warp (`hdet`). The assumptions keep their constraints when events that are quiet for `lead` are
appended to the warp (`hasm`). -/
theorem coll_batch_lead (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {g pc lead : Nat}
    {s : CollShape} (hg : g < L.threads) (hfull : s.Full) (hse : s.tag ≤ 1)
    (hl : LanesAt K A L X g pc s)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Step.Launched L X h)
    (hlead : electMember 4294967295 lead)
    (hdet : ∀ e pc' inst l, SameWarp L g e.1 → X.Elect e pc' 4294967295 inst l → l = lead)
    (hasm : ∀ ev : Nat → Event, (∀ x, QuietFor lead (ev x).kind) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev))
    (hrels : ∀ h, SameWarp L g h → Step.Released L X h) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hmem : ∀ h, electMember 4294967295 (laneOf L h) := fun h =>
    full_member (Nat.mod_lt _ (by decide))
  cases s with
  | shfl md b c =>
    have hex : ∀ h, ∃ a : Value, SameWarp L g h → ∃ t t1 k, Run K A L h {} (X.tr h)
        (some t) ∧ Relation.ReflTransGen (Tau K A L h) t t1 ∧
        out K A L h t1 = .ev (.shfl md a b c k) ∧ t1.pc = pc := by
      intro h
      obtain ⟨t, t1, m, -, -, -, -, hm⟩ := hl g ⟨⟨hg, hg, rfl⟩, rfl⟩
      obtain ⟨a0, -, -⟩ := tmplShape_shfl hm
      by_cases hs : SameWarp L g h
      · obtain ⟨t, t1, m, hr, hτ, hout, hpc, hm⟩ := hl h hs
        obtain ⟨a, k, rfl⟩ := tmplShape_shfl hm
        exact ⟨a, fun _ => ⟨t, t1, k, hr, hτ, hout, hpc⟩⟩
      · exact ⟨a0, fun h' => (hs h').elim⟩
    choose a ha using hex
    refine Step.shfl_counted_extension_with_assumptions hX hb (pc := pc) (m := md) a
      (fun _ => b) (fun _ => c) hg hst hrels (fun h hs recv ok => ?_)
      (hasm _ fun _ => ⟨rfl, fun _ _ _ h => by cases h⟩)
    obtain ⟨t, t1, k, hr, hτ, hout, hpc⟩ := ha h hs
    exact ⟨t, t1, _, hr, hτ, _, hout, recv, ok, by rw [hpc], rfl⟩
  | elect mask =>
    have hm : mask = 4294967295 := hfull
    subst hm
    refine Step.elect_counted_extension hX (pc := pc) hg
      (fun lane hl => Step.warp_full hb hg hl.1) (fun h _ => hmem h) hlead hdet hst hrels
      (fun h hs inst => ?_)
      (fun inst => hasm _ fun _ => ⟨rfl, fun _ _ _ h => by cases h; rfl⟩)
    obtain ⟨t, t1, m, hr, hτ, hout, hpc, hm⟩ := hl h hs
    obtain ⟨k, rfl⟩ := tmplShape_elect hm
    exact ⟨t, t1, _, hr, hτ, _, hout, inst, lead, by rw [hpc], rfl⟩
  | warpBar mask => simp [CollShape.tag] at hse
  | vote mask => simp [CollShape.tag] at hse

/-- **The facts of a kernel's warp collectives, all of them shuffles and elections.** The
library's facts with the lanes' release as a premise (`Sched.WarpCollRel`), and: a template
fired at a state classified as at a collective is a shuffle or an election (`kind`). -/
structure CollLead (mem0 : Mem0) (M : Timed K A L) (X : Execution) (key : Nat → κ)
    (AtColl : ∀ g, (M.code g).D → Prop) : Prop where
  /-- Shapes in order, the lanes' release, the exit count and the lag of a lane behind. -/
  rel : WarpCollRel mem0 M X key AtColl
  /-- The template at a collective state is a shuffle (tag 0) or an election (tag 1). -/
  kind : ∀ {g : Nat} {d : (M.code g).D} {t : TState} {m : Tmpl} {s : CollShape},
    g < L.threads → Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
    (M.code g).AtD d t → (M.code g).inv d → out K A L g t = .ev m → tmplShape m = some s →
    s.tag ≤ 1

variable {key : Nat → κ} {AtColl : ∀ g, (M.code g).D → Prop}

/-- **Progress at a warp collective, with the elected lane fixed by an assumption.** A released
pending thread whose state at its trace's end is at a shuffle or an election steps: the
execution has a counted consistent extension (the warp's instance with leader `lead`, or the
undefined behaviour of a lane), or a lane of its warp is a pending thread of smaller rank. -/
theorem warpColl_steps_lead (hK : K.code.all (fun ins => !voteModeOp ins.op) = true)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hw : CollLead mem0 M X key AtColl)
    (hb : L.block % 32 = 0) (hlaunch : ∀ h, Step.Launched L X h)
    (hcl : ∀ h, ¬ ClcCanceled L X h) {lead : Nat} (hlead : electMember 4294967295 lead)
    (hdet : ∀ e pc inst l, X.Elect e pc 4294967295 inst l → l = lead)
    (happ : ∀ (g : Nat) (ev : Nat → Event), (∀ x, QuietFor lead (ev x).kind) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hrel : Step.Released L X g) : Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := safe_noUb (hs.2 X hX)
  have hwrec : WarpRec M.code X key := by
    obtain ⟨F, hfull, hrec, -⟩ := hw.rel.shape
    exact ⟨fun c n => (F c n).2, hfull, hrec⟩
  obtain ⟨tg, hrg⟩ := Frame.run_some hX hub hp
  have hle : ∀ h, SameWarp L g h → (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl :=
    fun h hsw => Nat.le_of_not_lt fun hlt =>
      no_ahead hK hkey hX hsound htr hub hwrec hg hsw hrg hlt
  obtain ⟨F, hfullF, -, hshape⟩ := hw.rel.shape
  by_cases hall : ∀ h, SameWarp L g h →
      (X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl ∧
      ∃ dh, Frame.stateAt M.code X h (X.tr h).length = some (some dh) ∧ AtColl h dh
  · -- every lane at the collective
    by_cases hext : ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L
    · exact .inl hext
    have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hsw => by
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      exact (hw.rel.released hg hsw hσ hk hσh hkh hn hrel).resolve_right hext
    have hfire : ∀ h, SameWarp L g h → ∃ t t1 m, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev m ∧
        ((∃ f, m = .ub f) ∨ (t1.pc = (F (key g) ((X.tr g).countP isWarpColl)).1 ∧
          tmplShape m = some (F (key g) ((X.tr g).countP isWarpColl)).2)) := by
      intro h hsw
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      have hh := hsw.1.2.1
      obtain ⟨t, hr⟩ := Frame.run_some hX hub
        (hw.rel.lane_noExit hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw))
      obtain ⟨t1, ins, hτ, hat, hinv, -, hout⟩ := Frame.end_at hsound hh hr hσh
      have hsh := hshape hh hσh hkh hat hinv hout
      rw [hn, ← hkey hsw] at hsh
      exact ⟨t, t1, _, hr, hτ, hout, hsh⟩
    by_cases hubl : ∃ h, SameWarp L g h ∧ ∃ t t1 f, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev (.ub f)
    · obtain ⟨h, hsw, t, t1, f, hr, hτ, hout⟩ := hubl
      exact .inl (hubx hsw.1.2.1 (hrels h hsw) hr hτ hout)
    · push Not at hubl
      -- the thread's own template gives the kind of the collective
      have htag : (F (key g) ((X.tr g).countP isWarpColl)).2.tag ≤ 1 := by
        obtain ⟨t1, ins, hτ, hat, hinv, -, hout⟩ := Frame.end_at hsound hg hrg hσ
        rcases hshape hg hσ hk hat hinv hout with ⟨f, hf⟩ | ⟨-, hsh⟩
        · rw [hf] at hout
          exact (hubl g ⟨⟨hg, hg, rfl⟩, rfl⟩ tg t1 f hrg hτ hout).elim
        · exact hw.kind hg hσ hk hat hinv hout hsh
      refine .inl (coll_batch_lead hX hb hg (pc := (F (key g) ((X.tr g).countP isWarpColl)).1)
        (hfullF (key g) ((X.tr g).countP isWarpColl)) htag (fun h hsw => ?_)
        (fun h _ => .inr (hlaunch h)) hlead (fun e pc' inst l _ he => hdet e pc' inst l he)
        (happ g) hrels)
      obtain ⟨t, t1, m, hr, hτ, hout, hm⟩ := hfire h hsw
      rcases hm with ⟨f, rfl⟩ | ⟨hpc, hsh⟩
      · exact (hubl h hsw t t1 f hr hτ hout).elim
      · exact ⟨t, t1, m, hr, hτ, hout, hpc, hsh⟩
  · -- a lane not at the collective is earlier
    push Not at hall
    obtain ⟨h, hsw, hnot⟩ := hall
    have hph := hw.rel.lane_noExit hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw)
    by_cases hnone : Frame.stateAt M.code X h (X.tr h).length = none
    · obtain ⟨t, hr⟩ := Frame.run_some hX hub hph
      obtain ⟨t1, f, hτ, hout⟩ := Frame.end_dead hsound hph.1 hr hnone
      exact .inl (hubx hph.1 (hw.rel.dead hph hnone) hr hτ hout)
    have hlag := hw.rel.lag hg hsw.1.2.1 hsw hσ hk (hle h hsw) (fun ⟨hn, dh, hσh, hkh⟩ =>
      hnot hn dh hσh hkh) hnone
    have htime : threadTime M X h < threadTime M X g := by
      rw [threadTime_of hσ]
      exact hlag
    refine .inr ⟨X, .thread h, hmax, hph, ?_⟩
    rw [rank_released hrel]
    exact rank_lt_of_time_lt htime

/-! ### Warp matrix instructions -/

/-- The events of a matrix instance are quiet for every leader: the premise `happ` of the
library's `Sched.matrix_steps` (`Lemmas/Kernel/Progress/Matrix.lean`) follows from the
constraints of quiet events. -/
theorem quietFor_matrixBatch {lead pc : Nat} {op : MatrixOp}
    {parts recv : Nat → List (Option Byte)} (x : Nat) :
    QuietFor lead (matrixBatch L pc op parts recv x).kind :=
  ⟨rfl, fun _ _ _ h => by cases h⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpColl
public import Lemmas.Step.WarpMatrix

@[expose] public section

/-! # Progress at a warp-level matrix instruction

A proof tool, generic over the kernel: the counterpart of `Sched.warpColl_steps`
(`Lemmas/Kernel/Progress/WarpColl.lean`) for the warp-level matrix instructions (`ldmatrix`,
`stmatrix`, `movmatrix`, `mma.sync`), to be used next to it by a kernel that has shuffles or
elections as well. A lane's matrix event exists only with the matrix events of the same ordinal
of the 32 lanes of its warp (DEP-ORDER, DEP-WARP-MATRIX), so the warp performs an instance at
once. The matrix events of a thread are counted by Core's `isMatrix`.

The kernel classifies the machine states whose next event is a matrix event (`AtMatrix g d`).
With the facts `MatrixFacts` about those states, a released pending thread at such a state steps
(`Sched.matrix_steps`):

* no lane of its warp has made more matrix events (`Step.matrix_count_le`: the event would wait
  for the thread's own, DEP-ORDER; no recorded static parts are needed, unlike the shuffles);
* a lane that has made at most as many and is not at the same matrix event is earlier (`lag`) and
  has not exited (`exit`): it is a pending thread of smaller rank;
* otherwise every lane is at the matrix event and released (`last`), and either some lane's run
  reaches undefined behaviour, which performs it (`hubx`), or all lanes fire matrix templates of
  one operation at one position (`shape`) and the warp performs one instance
  (`Sched.matrix_batch`, from `Step.matrix_counted_extension_with_assumptions`).

The assumptions' execution constraints are asked of the extension by one matrix instance only
(`happ`), not of the append of arbitrary events that read no memory: a kernel whose assumption
constrains another warp collective (the leader of an election, say) can still prove it.

No hypothesis asks that the lanes' results are defined: when `matrixRecv` fails for a lane, the
instance is appended with arbitrary bytes for that lane and the extension is `MatrixUnsafe`.

In the two-event forms only the matrix event is a state of `AtMatrix`: the row read of an
`ldmatrix` lane before it and the row write of an `stmatrix` lane after it are ordinary events of
one lane (`Step.read_source_counted_extension`, `Step.plain_counted_extension`). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

/-- The lanes of `g`'s warp reach, by local steps, matrix templates of operation `op` at `pc`. -/
abbrev MatrixLanesAt (K : Kernel) (A : List Assumption) (L : Launch) (X : Execution)
    (g pc : Nat) (op : MatrixOp) : Prop :=
  ∀ h, SameWarp L g h → ∃ t t1 own k, Run K A L h {} (X.tr h) (some t) ∧
    Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev (.matrix op own k) ∧
    t1.pc = pc

/-- **The warp performs one instance of the matrix instruction**: a counted extension. The
assumptions keep their constraints when the matrix events of an instance are appended to the
warp (`hasm`). The premise is about these events only, not about every event that reads no
memory, so that a kernel whose assumptions constrain other events of that class (for example the
leader an election returns) can prove it. -/
theorem matrix_batch (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {g pc : Nat}
    {op : MatrixOp} (hg : g < L.threads) (hop : op.LaneClosed)
    (hl : MatrixLanesAt K A L X g pc op)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Step.Launched L X h)
    (hasm : ∀ (parts recv : Nat → List (Option Byte)), ∀ a ∈ A, a.wf L mem0
      (X.appendLanes (Step.warpThreads L g) (Step.matrixBatch L pc op parts recv)))
    (hrels : ∀ h, SameWarp L g h → Step.Released L X h) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hex : ∀ h, ∃ own : List (Option Byte), SameWarp L g h → ∃ t t1 k,
      Run K A L h {} (X.tr h) (some t) ∧ Relation.ReflTransGen (Tau K A L h) t t1 ∧
      out K A L h t1 = .ev (.matrix op own k) ∧ t1.pc = pc := by
    intro h
    by_cases hs : SameWarp L g h
    · obtain ⟨t, t1, own, k, hr, hτ, hout, hpc⟩ := hl h hs
      exact ⟨own, fun _ => ⟨t, t1, k, hr, hτ, hout, hpc⟩⟩
    · exact ⟨[], fun h' => (hs h').elim⟩
  choose own hown using hex
  refine Step.matrix_counted_extension_with_assumptions hX hb (pc := pc) hop own hg hst hrels
    (fun h hs recv => ?_) (fun recv _ => hasm _ recv)
  obtain ⟨t, t1, k, hr, hτ, hout, hpc⟩ := hown h hs
  exact ⟨t, t1, _, hr, hτ, hpc ▸ Step.estep_matrix hout recv⟩

/-- **The facts of a kernel's warp-level matrix instructions**, for the states classified as at
a matrix event (`AtMatrix`), with the lanes' warp key `key`. The counterpart of
`Sched.WarpCollFacts`; the ordinals count the thread's matrix events (`isMatrix`). -/
structure MatrixFacts (M : Timed K A L) (X : Execution) (key : Nat → κ)
    (AtMatrix : ∀ g, (M.code g).D → Prop) : Prop where
  /-- The position and the operation of a lane's `n`-th matrix event are a function of the warp
  and `n`, and the operation's results read the 32 lanes only (`MatrixOp.LaneClosed`: every
  supported form but an MMA with sparsity metadata; decidable for a given operation). A lane at
  the event fires that matrix template, or reaches undefined behaviour. -/
  shape : ∃ F : κ → Nat → Nat × MatrixOp,
    (∀ c n, (F c n).2.LaneClosed) ∧
    (∀ {g : Nat} {d : (M.code g).D} {t : TState} {m : Tmpl}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtMatrix g d →
      (M.code g).AtD d t → out K A L g t = .ev m → (∃ f, m = .ub f) ∨
        (t.pc = (F (key g) ((X.tr g).countP isMatrix)).1 ∧
          ∃ own k, m = .matrix (F (key g) ((X.tr g).countP isMatrix)).2 own k))
  /-- The last event before a lane's `n`-th matrix event never blocks, or it is the lane's first
  register request with operands fixed by the warp and `n`, or a warp-collective `tcgen05` event
  other than a paired Tensor Memory operation, of an ordinal fixed by the warp and `n`. -/
  last : ∃ R : κ → Nat → Option ((Nat × Bool × Nat) ⊕ Nat),
    ∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtMatrix g d →
      match R (key g) ((X.tr g).countP isMatrix) with
      | none => ∀ q, X.get (g, (X.tr g).length - 1) = some q → Unblocking q.kind
      | some (.inl (pc, inc, n)) => ∃ inst,
        X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
          SetMaxNReg.ordinal X (g, (X.tr g).length - 1) = 0
      | some (.inr k) => X.TcK (g, (X.tr g).length - 1) k ∧
        ∀ pc grp dst act, X.get (g, (X.tr g).length - 1) ≠ some ⟨pc, .tc (.resource grp dst act)⟩
  /-- A lane exits after a number of matrix events fixed by its warp, more than a lane at a
  matrix event has made. -/
  exit : ∃ T : κ → Nat,
    (∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtMatrix g d →
      (X.tr g).countP isMatrix < T (key g)) ∧
    (∀ {g k pc : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some ⟨pc, .exit⟩ →
      T (key g) ≤ ((X.tr g).take k).countP isMatrix)
  /-- A lane of the warp of a thread at its `n`-th matrix event that has made at most `n` of
  them and is not at its `n`-th is earlier. -/
  lag : ∀ {g h : Nat} {d : (M.code g).D}, g < L.threads → h < L.threads → SameWarp L g h →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtMatrix g d →
    (X.tr h).countP isMatrix ≤ (X.tr g).countP isMatrix →
    ¬ ((X.tr h).countP isMatrix = (X.tr g).countP isMatrix ∧
      ∃ d', Frame.stateAt M.code X h (X.tr h).length = some (some d') ∧ AtMatrix h d') →
    threadTime M X h < M.time g d

variable {key : Nat → κ} {AtMatrix : ∀ g, (M.code g).D → Prop}

/-- **A lane at the matrix event of a released lane is released**, both having made equally many
matrix events. -/
theorem MatrixFacts.lane_released (hw : MatrixFacts M X key AtMatrix)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h) {g h : Nat} (hg : g < L.threads)
    (hs : SameWarp L g h) {d : (M.code g).D} {dh : (M.code h).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtMatrix g d)
    (hσh : Frame.stateAt M.code X h (X.tr h).length = some (some dh)) (hkh : AtMatrix h dh)
    (hn : (X.tr h).countP isMatrix = (X.tr g).countP isMatrix)
    (hrel : Step.Released L X g) : Step.Released L X h := by
  obtain ⟨R, hR⟩ := hw.last
  have hlg := hR hg hσ hk
  have hlh := hR hs.1.2.1 hσh hkh
  rw [hn, ← hkey hs] at hlh
  revert hlg hlh
  cases R (key g) ((X.tr g).countP isMatrix) with
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

/-- **A lane of the warp of a lane at a matrix event has not exited** when it has made at most
as many matrix events. -/
theorem MatrixFacts.lane_noExit (hw : MatrixFacts M X key AtMatrix)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (htr : Frame.Tracked M.code X)
    (hub : ¬ HasUb X) (hcl : ∀ h, ¬ ClcCanceled L X h) {g h : Nat} {d : (M.code g).D}
    (hg : g < L.threads) (hs : SameWarp L g h)
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtMatrix g d)
    (hle : (X.tr h).countP isMatrix ≤ (X.tr g).countP isMatrix) :
    Frame.Pending L X h := by
  obtain ⟨T, hT1, hT2⟩ := hw.exit
  refine ⟨hs.1.2.1, hcl h, fun pc hl => ?_⟩
  have hex := exit_get hl
  obtain ⟨dx, hdx⟩ := Frame.state_of_noUb hsound hX htr hub hex
  have h1 := hT1 hg hσ hk
  have h2 := hT2 hs.1.2.1 hdx hex
  have h3 := Flow.countP_take_mono isMatrix (X.tr h) (Nat.sub_le (X.tr h).length 1)
  rw [List.take_length] at h3
  rw [← hkey hs] at h2
  omega

/-- **Progress at a warp-level matrix instruction.** A released pending thread whose state at
its trace's end is at a matrix event steps: the execution has a counted consistent extension (the
warp's instance, or the undefined behaviour of a lane), or a lane of its warp is a pending thread
of smaller rank. In a maximal execution only the second holds, so no warp stays with all its
lanes at one matrix instruction. -/
theorem matrix_steps (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hw : MatrixFacts M X key AtMatrix)
    (hb : L.block % 32 = 0) (hlaunch : ∀ h, Step.Launched L X h)
    (hcl : ∀ h, ¬ ClcCanceled L X h)
    (happ : ∀ (g pc : Nat) (op : MatrixOp) (parts recv : Nat → List (Option Byte)), ∀ a ∈ A,
      a.wf L mem0 (X.appendLanes (Step.warpThreads L g) (Step.matrixBatch L pc op parts recv)))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtMatrix g d)
    (hrel : Step.Released L X g) : Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := safe_noUb (hs.2 X hX)
  obtain ⟨tg, hrg⟩ := Frame.run_some hX hub hp
  have hle : ∀ h, SameWarp L g h → (X.tr h).countP isMatrix ≤ (X.tr g).countP isMatrix :=
    fun h hsw => Step.matrix_count_le hX hsw fun _ _ => hrg.no_exit
  obtain ⟨F, hclosed, hshape⟩ := hw.shape
  by_cases hall : ∀ h, SameWarp L g h →
      (X.tr h).countP isMatrix = (X.tr g).countP isMatrix ∧
      ∃ dh, Frame.stateAt M.code X h (X.tr h).length = some (some dh) ∧ AtMatrix h dh
  · -- every lane at the matrix event
    have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hsw => by
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      exact hw.lane_released hkey hg hsw hσ hk hσh hkh hn hrel
    have hfire : ∀ h, SameWarp L g h → ∃ t t1 m, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev m ∧
        ((∃ f, m = .ub f) ∨ (t1.pc = (F (key g) ((X.tr g).countP isMatrix)).1 ∧
          ∃ own k, m = .matrix (F (key g) ((X.tr g).countP isMatrix)).2 own k)) := by
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
      refine .inl (matrix_batch hX hb hg (pc := (F (key g) ((X.tr g).countP isMatrix)).1)
        (hclosed (key g) ((X.tr g).countP isMatrix)) (fun h hsw => ?_)
        (fun h _ => .inr (hlaunch h)) (happ g _ _) hrels)
      obtain ⟨t, t1, m, hr, hτ, hout, hm⟩ := hfire h hsw
      rcases hm with ⟨f, rfl⟩ | ⟨hpc, own, k, rfl⟩
      · exact (hubl h hsw t t1 f hr hτ hout).elim
      · exact ⟨t, t1, own, k, hr, hτ, hout, hpc⟩
  · -- a lane not at the matrix event is earlier
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

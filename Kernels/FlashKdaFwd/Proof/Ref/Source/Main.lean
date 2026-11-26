-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Source.Sources
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Direct

@[expose] public section

/-! # The source side of the tensor loads: the theorems the other layers use

The files of this directory prove where the kernel's tensor loads read, that those bytes are
launch inputs that nothing writes, and what the loads therefore put into shared memory. This
file states the results in the shapes of their consumers.

**From the precondition alone**

* `stateSource : StateSource P L` (`Ref/Startup/Direct.lean`): the hypothesis of the startup
  phase's `globalReadFrame_startup` and `loadBounds_startup`.
* `tileSource : TileSource P L mem0` (`Ref/Producer/Direct.lean`): the hypothesis of the
  Producer phase's `globalReadFrame_producer`.

**For a consistent execution** (`Sources.lean`): `tensorSources` (the progress premise
`TensorSources L mem0 X`, from `WriteFrame P X` and `LoadShapes P L X`), `loads_readFrame`,
`loads_fill`, `loads_bounds`.

**The content of the loads**, in the shape of the read-back theorems of the protocol layer
(`Proof/Protocol/ReadBack.lean`):

* `stage_content`: its conclusion is, word for word, the hypothesis `hsb` of
  `UnionFacts.stage_read` with the content
  `sb := Values.stageByte P mem0 (c % P.sequences) (c / P.sequences) (3 * u + s)`: every
  offset of input stage `s` of block `c` outside the 64-byte hole has a position `p < 70` and a
  slot such that the load leader's load with `70 u + p` earlier loads on the stage's "full"
  mbarrier has that slot at the byte, and its record, once notified, holds the content byte,
  which is defined. `c % P.sequences` and `c / P.sequences` are the sequence and the head of
  block `c`, and `3 u + s` is the tile whose loads these are (the `u`-th use of stage `s`).
* `init_content`: its conclusion is, word for word, the hypothesis `hic` of
  `UnionFacts.early_read` with the content `ic := Values.Ends.initBuf P L c` (it is also the
  value layer's `Values.Ends.InitContent P L X c`): every offset of the FP32 state buffer has a
  load number `q < 16` and a slot such that the load leader's load with `q` earlier loads on
  the state mbarrier has that slot at the byte, and its record, once notified, holds the
  content byte, which is defined.

Both take `hpre`, `hX`, the hypothesis `WriteFrame P X` and one hypothesis that links a count on
an mbarrier to a copy:

* `TileIssues P L X`: a tensor load issue of the load leader of block `c` that completes on the
  "full" mbarrier of stage `s`, with `n` earlier issues on that mbarrier, is the copy
  `tileLoad P L g (3 (n / 70) + s) (n % 70)`, and that tile is a tile of the block's sequence.
* `StateIssues P L X`: a tensor load issue of the load leader of block `c` that completes on
  the state mbarrier, with `n` earlier issues on it, is the copy `stateSpec P L g n`, and
  `n < 16`.

Each follows from the exports of the phase that issues these loads at a followed state of that
phase: `tileIssues_of_producer` (from `Producer.event_at` and `Producer.issue_shape`) and
`stateIssues_of_startup` (from `Startup.state_issue_spec` and `Startup.state_issue_startup`)
reduce them to "the load leader is in that phase at the issue", which the assembly supplies.
`loadShapes_of_phases` does the same for the hypothesis `LoadShapes P L X` of `tensorSources`
(from `Startup.issue_startup`, `Producer.event_at` and `Producer.issue_shape`).

Words: the *load leader* of a block is its thread 128; a *record* of a load is what the model
has observed of it so far, *notified* once it has signalled its mbarrier (only then has it
written every byte); the *window* of a block is its shared memory from `shared_mem`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (stateSpec StateSource)
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer (tileLoad tilesOf TileSource stage)
open PTX.Kernels.FlashKdaFwd.Protocol (Bar loadLeader)
open PTX.Kernels.FlashKdaFwd.Proof.Values (stageByte)
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (initBuf)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### From the precondition -/

/-- **`StateSource P L`**: a load of the initial state selects no element outside the array, and
every byte it reads is a byte of the initial-state array. -/
theorem stateSource (hpre : Pre P L mem0) : StateSource P L := stateSpec_source hpre

/-- **`TileSource P L mem0`**: every global byte a tile load reads is allocated in the launch
memory and is no output byte and no byte of the final state. -/
theorem tileSource (hpre : Pre P L mem0) : TileSource P L mem0 :=
  fun _ hg _ htt _ hi _ _ _ _ h => (tileLoad_input hpre hg htt hi h).frame

/-! ### Which copy an issue is -/

/-- **The tile loads by their count**: a tensor load issue of the load leader of block `c` that
completes on the "full" mbarrier of stage `s`, with `n` earlier issues on that mbarrier, is the
load at position `n % 70` of tile `3 (n / 70) + s`, and that tile is a tile of the block's
sequence. -/
def TileIssues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ (c : Nat) (s : Fin 3) (i pc al : Nat) (sp : TensorCopy.Spec),
    X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩ →
    sp.mbar = (Bar.loadFull s).loc L c →
    3 * (((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70) +
        s.val < tilesOf P (loadLeader L c) ∧
      sp = tileLoad P L (loadLeader L c)
        (3 * (((X.tr (loadLeader L c)).take i).countP
          (issuesTo ((Bar.loadFull s).loc L c)) / 70) + s.val)
        (((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) % 70)

/-- **The loads of the initial state by their count**: a tensor load issue of the load leader
of block `c` that completes on the state mbarrier, with `n` earlier issues on it, is the
`n`-th load of the initial state, and `n < 16`. -/
def StateIssues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ (c i pc al : Nat) (sp : TensorCopy.Spec),
    X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩ →
    sp.mbar = Bar.state.loc L c →
    ((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c)) < 16 ∧
      sp = stateSpec P L (loadLeader L c)
        (((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c)))

/-- The load leader of a block: its block, its sequence, its head. -/
theorem leader_block (hpre : Pre P L mem0) (c : Nat) :
    loadLeader L c / L.block = c ∧ seqOf P (loadLeader L c) = c % P.sequences ∧
      headOf P (loadLeader L c) = c / P.sequences := by
  have hb := hpre.block
  have hdiv : loadLeader L c / L.block = c := Protocol.thr_div hb (by decide)
  rw [hb] at hdiv
  refine ⟨by rw [hb]; exact hdiv, ?_, ?_⟩
  · show loadLeader L c / 192 % P.sequences = c % P.sequences
    rw [hdiv]
  · show loadLeader L c / 192 / P.sequences = c / P.sequences
    rw [hdiv]

/-- **`TileIssues` from the Producer phase**: it holds when every issue of a load leader that
completes on a "full" mbarrier is fired inside the Producer phase (the leader entered the phase
at or before the issue, its machine follows it there, and it has not left the phase). -/
theorem tileIssues_of_producer (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hin : ∀ (c : Nat) (s : Fin 3) (i pc al : Nat) (sp : TensorCopy.Spec),
      X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩ →
      sp.mbar = (Bar.loadFull s).loc L c →
      ∃ k0 ≤ i, Producer.Entered P L X (loadLeader L c) k0 ∧
        (∃ st, Frame.stateAt (code L) X (loadLeader L c) i = some (some st)) ∧
        ¬ Producer.Left P L X (loadLeader L c) i) : TileIssues P L X := by
  intro c s i pc al sp hiss hm
  obtain ⟨k0, hk0, hen, ⟨st, hσ⟩, hnl⟩ := hin c s i pc al sp hiss hm
  have hg := Frame.lt_of_get hX hiss
  obtain ⟨hdiv, -, -⟩ := leader_block (P := P) hpre c
  have hw : warp (loadLeader L c) = 4 := by
    have hb := hpre.block
    unfold warp loadLeader Protocol.thr
    rw [hb]
    omega
  rcases Producer.event_at hpre hX hg hw hen hk0 hiss hσ with ⟨pos, hr, hl, hev, -⟩ | h
  · obtain ⟨tt, p, htt, hp, -, -, rfl, -, hc, -⟩ := Producer.issue_shape hr hl hev
    rw [hdiv] at hc
    have hmb : (tileLoad P L (loadLeader L c) tt p).mbar = (Bar.loadFull (stage tt)).loc L c := by
      rw [tileLoad, loadSpec_mbar, Producer.fullLoc_eq hpre, hdiv]
    obtain rfl : stage tt = s := by
      have := (Bar.loc_inj (hmb.symm.trans hm)).1
      simpa using this
    have hc' : ((X.tr (loadLeader L c)).take i).countP
        (issuesTo ((Bar.loadFull (stage tt)).loc L c)) = 70 * (tt / 3) + p := hc
    have h3 : (stage tt).val = tt % 3 := rfl
    rw [hc', show (70 * (tt / 3) + p) / 70 = tt / 3 by omega,
      show (70 * (tt / 3) + p) % 70 = p by omega, h3,
      show 3 * (tt / 3) + tt % 3 = tt by omega]
    exact ⟨htt, rfl⟩
  · exact absurd h hnl

/-- **`StateIssues` from the startup phase**: it holds when every issue of a load leader that
completes on the state mbarrier is fired inside the startup phase (its machine follows it
there and it has not left the phase). -/
theorem stateIssues_of_startup (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hin : ∀ (c i pc al : Nat) (sp : TensorCopy.Spec),
      X.get (loadLeader L c, i) = some ⟨pc, .tensorIssue al sp⟩ →
      sp.mbar = Bar.state.loc L c →
      (∃ st, Frame.stateAt (code L) X (loadLeader L c) i = some (some st)) ∧
        ¬ Startup.Left P L X (loadLeader L c) i) : StateIssues P L X := by
  intro c i pc al sp hiss hm
  obtain ⟨⟨st, hσ⟩, hnl⟩ := hin c i pc al sp hiss hm
  have hg := Frame.lt_of_get hX hiss
  rcases Startup.state_issue_startup hpre hX hg hiss hm hσ with ⟨-, -, hlt⟩ | h
  · rcases Startup.state_issue_spec hpre hX hg hiss hm hσ with ⟨-, hsp⟩ | h
    · exact ⟨hlt, hsp⟩
    · exact absurd h hnl
  · exact absurd h hnl

/-- **`LoadShapes` from the two phases that issue loads**: it holds when every tensor load
issue is fired at a followed state inside the startup phase (the thread has not left it) or
inside the Producer phase (a thread of the load warp that entered the phase at or before the
issue and has not left it). -/
theorem loadShapes_of_phases (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hin : ∀ (g i pc al : Nat) (sp : TensorCopy.Spec),
      X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩ →
      ∃ st, Frame.stateAt (code L) X g i = some (some st) ∧
        (¬ Startup.Left P L X g i ∨
          (warp g = 4 ∧ ∃ k0 ≤ i, Producer.Entered P L X g k0 ∧ ¬ Producer.Left P L X g i))) :
    LoadShapes P L X := by
  rintro ⟨g, i⟩ al sp ⟨pc, hiss⟩
  have hg := Frame.lt_of_get hX hiss
  obtain ⟨st, hσ, hph⟩ := hin g i pc al sp hiss
  rcases hph with hnl | ⟨hw, k0, hk0, hen, hnl⟩
  · rcases Startup.issue_startup hpre hX hg hiss hσ with ⟨j, -, -, rfl, -, -⟩ | h
    · exact .inl ⟨j.val, j.isLt, rfl⟩
    · exact absurd h hnl
  · rcases Producer.event_at hpre hX hg hw hen hk0 hiss hσ with ⟨pos, hr, hl, hev, -⟩ | h
    · obtain ⟨tt, p, htt, hp, -, -, rfl, -⟩ := Producer.issue_shape hr hl hev
      exact .inr ⟨tt, htt, p, hp, rfl⟩
    · exact absurd h hnl

/-! ### The content of the loads -/

/-- **The content of an input stage**: the hypothesis `hsb` of `UnionFacts.stage_read`
(`Proof/Protocol/ReadBack.lean`) for the content
`Values.stageByte P mem0 (c % P.sequences) (c / P.sequences) (3 * u + s)`. -/
theorem stage_content (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hT : TileIssues P L X) (hW : WriteFrame P X) (c : Nat) (s : Fin 3) (u : Nat) :
    ∀ o', o' < 18048 → (o' < 4160 ∨ 4224 ≤ o') → ∃ p < 70, ∃ x y z,
      ∀ i pci al sp, X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩ →
        sp.mbar = (Bar.loadFull s).loc L c →
        ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) =
          70 * u + p →
        TensorCopy.writeLoc sp x y z =
            some ⟨.shared, c, L.sharedBase + (32768 + 18048 * s.val + o')⟩ ∧
          ∀ rec, X.tensor (loadLeader L c, i) = some rec → rec.effects.notified = true →
            TensorCopy.writeByte rec x y z =
                stageByte P mem0 (c % P.sequences) (c / P.sequences) (3 * u + s.val) o' ∧
              (stageByte P mem0 (c % P.sequences) (c / P.sequences) (3 * u + s.val) o').isSome
    := by
  intro o ho hfree
  have hp := pieceOf_lt ho
  refine ⟨Producer.pieceOf o, hp, tileX o, tileY o, tileK o,
    fun i pci al sp hiss hm hcnt => ?_⟩
  have hg := Frame.lt_of_get hX hiss
  obtain ⟨hdiv, hseq, hhead⟩ := leader_block (P := P) hpre c
  obtain ⟨h1, h2⟩ := hT c s i pci al sp hiss hm
  rw [hcnt, show (70 * u + Producer.pieceOf o) / 70 = u by omega] at h1 h2
  rw [show (70 * u + Producer.pieceOf o) % 70 = Producer.pieceOf o by omega] at h2
  subst h2
  obtain ⟨hwl, hcont⟩ := tile_load_content hpre hX hW hg h1 ho hfree
  have hs := s.isLt
  rw [hdiv, show (3 * u + s.val) % 3 = s.val by omega] at hwl
  rw [hseq, hhead] at hcont
  exact ⟨hwl, fun rec hrec hn => hcont _ rec hrec (spec_of_issue hX hiss hrec) hn⟩

/-- **The content of the FP32 state buffer**: the hypothesis `hic` of `UnionFacts.early_read`
(`Proof/Protocol/ReadBack.lean`) for the content `Values.Ends.initBuf P L c`; it is the value
layer's `Values.Ends.InitContent P L X c`. -/
theorem init_content (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hS : StateIssues P L X) (hW : WriteFrame P X) (c : Nat) :
    ∀ o', o' < 65536 → ∃ q < 16, ∃ x y z,
      ∀ i pci al sp, X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩ →
        sp.mbar = Bar.state.loc L c →
        ((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c)) = q →
        TensorCopy.writeLoc sp x y z = some ⟨.shared, c, L.sharedBase + (32768 + o')⟩ ∧
          ∀ rec, X.tensor (loadLeader L c, i) = some rec → rec.effects.notified = true →
            TensorCopy.writeByte rec x y z = initBuf P L c o' ∧ (initBuf P L c o').isSome := by
  intro o ho
  have hq : stateQ L o < 16 := by
    have := (unswz_spec hpre ho).1
    unfold stateQ
    omega
  refine ⟨stateQ L o, hq, stateX L o, stateY L o, stateK L o,
    fun i pci al sp hiss hm hcnt => ?_⟩
  have hg := Frame.lt_of_get hX hiss
  obtain ⟨hdiv, -, -⟩ := leader_block (P := P) hpre c
  obtain ⟨-, h2⟩ := hS c i pci al sp hiss hm
  rw [hcnt] at h2
  subst h2
  obtain ⟨-, hwl, hcont⟩ := state_load_content hpre hX hW hg ho
  rw [hdiv] at hwl hcont
  exact ⟨hwl, fun rec hrec hn => hcont _ rec hrec (spec_of_issue hX hiss hrec) hn⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotCommit
public import Lemmas.Order.WarpBarOrdinal

@[expose] public section

/-! # What the thread layer exports for the score handoff and the P-ready objects

Each CTA pair's Tensor Memory holds, per stage `st < 2`, the scores `S` in columns
`128 st … 128 st + 127` (`InS`), the probabilities `P` (f16 pairs) over the upper half of them,
columns `128 st + 64 …` (`InP`), and the output accumulator `O` in columns
`256 + 128 st …` (`InO`). One thread of the pair (the elected lane of warp 12 of the leader CTA)
issues every MMA and commit (`cta_group::2`: an MMA writes the cells of both CTAs):

* the QK MMAs of stage `st`, score tile `u` (global over the items), write `S` with `u` earlier
  commits to the stage's S-full object (`sCommits`) and come after the MMA thread's polls of
  P-ready phases before `u` of both P-ready objects (`qk_polls`);
* the PV MMAs of stage `st` read `P` from Tensor Memory and accumulate into `O`; the PV MMAs of
  tile `u` follow the thread's poll of phase `u` of the P-ready object (`pPolls = u + 1`), and those
  reading columns `112 …` also the poll of phase `u` of the second object (`pv_polls`).

The softmax thread of stage `st` and row `ρ` polls the stage's S-full object of its CTA once per
tile (`sPolls = u + 1` in tile `u`). In tile `u` it loads its row of `S` (`tcgen05.ld`, followed by
the implicit `tcgen05.wait::ld` of the kernel's assumption `fa4-fwd-tcld-dataflow`, at the next
index), stores its row of `P` (`tcgen05.st`), each store followed by a `tcgen05.wait::st` in the
tile, and arrives on the leader's P-ready object once (`pArr`): after the waits of its stores of
columns below `112` and before those of columns `112 …`, which the warp's elected lane publishes
through the second P-ready object. Its arrival count before a load of tile `u` is `u`.

An execution's trace of a thread may stop at any event, so a later event is stated only where
the trace has it: the `wait::ld` after a load when the trace goes on past the load, and the
`wait::st` after a store before every later event of the thread that is neither a `tcgen05`
event nor undefined behaviour (`NonTcAfter`: a thread whose machine stopped may perform an
undefined-behaviour event anywhere).

The fields are event-level facts of single threads from the run invariants of the MMA thread
(`Mma.Counts`) and of the softmax (`Softmax.Counts`, its sites' Tensor Memory addresses), and two
facts of the MMA warp: one lane issues every MMA and commit (DEP-WARP-ELECT, as in GEMM), and the
accumulators of one region agree (the instruction descriptors and `tmem_acc` constants). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The leader CTA of `c`'s pair. -/
def leadCta (c : Nat) : Nat := c / 2 * 2

/-- Stage `st`'s S-full object in CTA `c`. -/
def sFullBar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (128 + 8 * st)⟩

/-- Stage `st`'s P-ready object in CTA `c` (used in leader CTAs). -/
def pReadyBar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (144 + 8 * st)⟩

/-- Stage `st`'s second P-ready object in CTA `c` (used in leader CTAs). -/
def pReady2Bar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (160 + 8 * st)⟩

theorem sFullBar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    sFullBar L c st = FBar.loc L c (.sFull st) := rfl

theorem pReadyBar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    pReadyBar L c st = FBar.loc L c (.pReady st) := rfl

theorem pReady2Bar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    pReady2Bar L c st = FBar.loc L c (.pReady2 st) := rfl

/-- A Tensor Memory cell of stage `st`'s scores. -/
def InS (st : Nat) (cell : Cell) : Prop :=
  128 * st ≤ cell.column ∧ cell.column < 128 * st + 128

/-- A Tensor Memory cell of stage `st`'s probabilities (the upper half of its scores). -/
def InP (st : Nat) (cell : Cell) : Prop :=
  128 * st + 64 ≤ cell.column ∧ cell.column < 128 * st + 128

/-- A Tensor Memory cell of stage `st`'s output accumulator. -/
def InO (st : Nat) (cell : Cell) : Prop :=
  256 + 128 * st ≤ cell.column ∧ cell.column < 384 + 128 * st

/-- A cell of the probabilities published through the second P-ready object (columns `112 …`). -/
def InPHigh (st : Nat) (cell : Cell) : Prop := 128 * st + 112 ≤ cell.column

/-- Commits of thread `g` to stage `st`'s S-full object of its CTA before its event `i`. -/
def sCommits (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  ((X.tr g).take i).countP (commitsTo (sFullBar L (ctaOf L g) st))

/-- Successful polls of thread `g` of stage `st`'s P-ready object of its CTA before event `i`. -/
def pPolls (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  okPolls (pReadyBar L (ctaOf L g) st) ((X.tr g).take i)

/-- The same for the second P-ready object. -/
def p2Polls (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  okPolls (pReady2Bar L (ctaOf L g) st) ((X.tr g).take i)

/-- Successful polls of thread `g` of stage `st`'s S-full object of its CTA before event `i`. -/
def sPolls (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  okPolls (sFullBar L (ctaOf L g) st) ((X.tr g).take i)

/-- Arrivals of thread `g` on stage `st`'s P-ready object of its pair's leader before event
`i`. -/
def pArr (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  arrivals (pReadyBar L (leadCta (ctaOf L g)) st) ((X.tr g).take i)

/-- Event `e` of thread `h` comes after its event `i` and is neither a `tcgen05` event nor
undefined behaviour. -/
def NonTcAfter (X : Execution) (h i e : Nat) : Prop :=
  i < e ∧ ∃ ev, X.get (h, e) = some ev ∧ (∀ tk, ev.kind ≠ .tc tk) ∧ ∀ f, ev.kind ≠ .ub f

/-- An MMA issue. -/
def IsMma (X : Execution) (i : EvId) : Prop := ∃ d s acc mask, X.MmaIssue i d s acc mask

/-- The thread layer's facts for the score handoff and the P-ready objects. -/
structure ScoreFacts (L : Launch) (X : Execution) : Prop where
  /-- The kernel has no `tcgen05.cp`. -/
  no_cp : ∀ e c, ¬ X.CpIssue e c
  /-- The kernel has no `tcgen05.shift`. -/
  no_shift : ∀ e s, ¬ X.ShiftIssue e s
  /-- An MMA is issued by warp 12 of a leader CTA; its result cells are all in one stage's scores
  or all in one stage's output accumulator, in the issuer's pair. -/
  mma_cells : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → i.1 < L.threads ∧ warpOf L i.1 = 12 ∧
      leadCta (ctaOf L i.1) = ctaOf L i.1 ∧ ∃ st < 2,
        (∀ cell, X.MmaCell i cell → InS st cell ∧ leadCta cell.cta = ctaOf L i.1) ∨
          (∀ cell, X.MmaCell i cell → InO st cell ∧ leadCta cell.cta = ctaOf L i.1)
  /-- One thread of a pair issues its MMAs and commits. -/
  tc_one : ∀ {i i' : EvId}, IsMma X i → (IsMma X i' ∨ ∃ s, X.Commit i' s) →
    leadCta (ctaOf L i.1) = leadCta (ctaOf L i'.1) → i.1 = i'.1
  /-- MMAs writing one stage's scores, or one stage's accumulator, of one CTA pair use the same
  accumulator. -/
  mma_acc : ∀ {i i' : EvId} {d d' st : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell cell' : Cell}, X.MmaIssue i d s acc mask →
    X.MmaIssue i' d' s' acc' mask' → X.MmaCell i cell → X.MmaCell i' cell' →
    leadCta cell.cta = leadCta cell'.cta →
    (InS st cell ∧ InS st cell') ∨ (InO st cell ∧ InO st cell') → SameAccumulator d s d' s'
  /-- A QK MMA of score tile `u` follows the MMA thread's polls of phases `0 … u - 1` of both
  P-ready objects. -/
  qk_polls : ∀ {i : EvId} {cell : Cell} {st : Nat}, IsMma X i → X.MmaCell i cell → InS st cell →
    sCommits L X i.1 st i.2 ≤ pPolls L X i.1 st i.2 ∧
      sCommits L X i.1 st i.2 ≤ p2Polls L X i.1 st i.2
  /-- A PV MMA of tile `u` (`pPolls = u + 1`) reads its A operand from Tensor Memory, in its
  stage's probabilities in its pair, and when it reads columns `112 …` it follows the poll of
  phase `u` of the second object; it comes before the commit of score tile `u + 1`. -/
  pv_polls : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {cell : Cell} {st : Nat}, X.MmaIssue i d s acc mask → X.MmaCell i cell → InO st cell →
    1 ≤ pPolls L X i.1 st i.2 ∧ sCommits L X i.1 st i.2 ≤ pPolls L X i.1 st i.2 ∧
      s.aTmem.isSome ∧ ∀ index c pos, aCell s index = some (c, pos) →
        InP st c ∧ leadCta c.cta = ctaOf L i.1 ∧
          (InPHigh st c → p2Polls L X i.1 st i.2 = pPolls L X i.1 st i.2)
  /-- The PV MMAs of tile `u` come before the QK MMAs of later score tiles. -/
  pv_qk : ∀ {i i' : EvId} {cell cell' : Cell} {st : Nat}, IsMma X i → IsMma X i' →
    i.1 = i'.1 → X.MmaCell i cell → InO st cell → X.MmaCell i' cell' → InS st cell' →
    pPolls L X i.1 st i.2 ≤ sCommits L X i'.1 st i'.2 → i.2 < i'.2
  /-- Tensor Memory loads and stores are made by softmax and correction threads. -/
  tc_role : ∀ {g i a : Nat} {vals : List Value} {sh : TcShape},
    (X.TLd (g, i) a vals sh ∨ X.TSt (g, i) a vals sh) → g < L.threads ∧ warpOf L g < 12
  /-- Tensor Memory loads and stores have the shape `.32x32b`. -/
  tc_shape : ∀ {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape},
    (X.TLd e a vals sh ∨ X.TSt e a vals sh) → sh = .s32x32b
  /-- A softmax load of tile `u` reads its row of its stage's scores, after `u + 1` polls of the
  S-full object and `u` arrivals on the P-ready object; the implicit `wait::ld` is the thread's
  next event, if it has one. -/
  soft_ld : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → warpOf L h < 8 →
    X.TLd (h, i) a vals .s32x32b →
      (∀ j < vals.length, InS (warpOf L h / 4) (tcDataCell32 L h a j)) ∧
      (i + 1 < (X.tr h).length → ∃ pc, X.get (h, i + 1) = some ⟨pc, .tc .waitLd⟩) ∧
      pArr L X h (warpOf L h / 4) i + 1 = sPolls L X h (warpOf L h / 4) i
  /-- A softmax store of tile `u` writes its row of its stage's probabilities, either all below
  or all from column `112`, after the warp barriers of the tiles before `u` and, for the columns
  below `112`, before the tile's arrival on the P-ready object; every later event of the thread
  that is not a `tcgen05` event comes after a `wait::st` of the tile that follows the store. -/
  soft_st : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → warpOf L h < 8 →
    X.TSt (h, i) a vals .s32x32b →
      (∀ j < vals.length, InP (warpOf L h / 4) (tcDataCell32 L h a j)) ∧
      ((∀ j < vals.length, ¬ InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) ∨
        ∀ j < vals.length, InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) ∧
      1 ≤ sPolls L X h (warpOf L h / 4) i ∧
      warpBars X h i + 1 = sPolls L X h (warpOf L h / 4) i ∧
      ((∀ j < vals.length, InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) ∨
        pArr L X h (warpOf L h / 4) i + 1 = sPolls L X h (warpOf L h / 4) i) ∧
      ∀ e, NonTcAfter X h i e →
      ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
        sPolls L X h (warpOf L h / 4) w = sPolls L X h (warpOf L h / 4) i
  /-- A softmax thread's loads of a tile come before its stores of the tile. -/
  soft_ld_st : ∀ {h i i' a a' : Nat} {vals vals' : List Value}, h < L.threads →
    warpOf L h < 8 → X.TLd (h, i) a vals .s32x32b → X.TSt (h, i') a' vals' .s32x32b →
    sPolls L X h (warpOf L h / 4) i = sPolls L X h (warpOf L h / 4) i' → i < i'
  /-- A softmax thread stores each cell once per tile. -/
  soft_st_one : ∀ {h i i' a a' j j' : Nat} {vals vals' : List Value}, h < L.threads →
    warpOf L h < 8 → X.TSt (h, i) a vals .s32x32b → X.TSt (h, i') a' vals' .s32x32b →
    j < vals.length →
    j' < vals'.length → tcDataCell32 L h a j = tcDataCell32 L h a' j' →
    sPolls L X h (warpOf L h / 4) i = sPolls L X h (warpOf L h / 4) i' → i = i'

namespace ScoreFacts

variable {L : Launch} {X : Execution}

/-- A load's cell, with the load's shape `.32x32b` (`tc_shape`). -/
theorem loadCell (ht : ScoreFacts L X) {load : EvId} {j : Nat} {cell : Cell}
    (h : LoadCell L X load j cell) :
    ∃ a vals, X.TLd load a vals .s32x32b ∧ j < vals.length ∧ cell = tcDataCell32 L load.1 a j := by
  obtain ⟨a, vals, sh, hl, hj, rfl⟩ := h
  obtain rfl := ht.tc_shape (.inl hl)
  exact ⟨a, vals, hl, hj, tcDataCell_s32x32b _ _ _ _⟩

/-- A store's cell, with the store's shape `.32x32b` (`tc_shape`). -/
theorem storeCell (ht : ScoreFacts L X) {st : EvId} {cell : Cell} (h : StoreCell L X st cell) :
    ∃ a vals j, X.TSt st a vals .s32x32b ∧ j < vals.length ∧ cell = tcDataCell32 L st.1 a j := by
  obtain ⟨a, vals, sh, j, hs, hj, rfl⟩ := h
  obtain rfl := ht.tc_shape (.inr hs)
  exact ⟨a, vals, j, hs, hj, tcDataCell_s32x32b _ _ _ _⟩

/-- A store's value, with the store's shape `.32x32b` (`tc_shape`). -/
theorem storeValue (ht : ScoreFacts L X) {st : EvId} {cell : Cell} {value : Value}
    (h : StoreValue L X st cell value) :
    ∃ a vals j, X.TSt st a vals .s32x32b ∧ vals[j]? = some value ∧
      cell = tcDataCell32 L st.1 a j := by
  obtain ⟨a, vals, sh, j, hs, hj, rfl⟩ := h
  obtain rfl := ht.tc_shape (.inr hs)
  exact ⟨a, vals, j, hs, hj, tcDataCell_s32x32b _ _ _ _⟩

end ScoreFacts

/-- A `.32x32b` load's cell. -/
theorem loadCell32 {L : Launch} {X : Execution} {e : EvId} {a j : Nat} {vals : List Value}
    (h : X.TLd e a vals .s32x32b) (hj : j < vals.length) :
    LoadCell L X e j (tcDataCell32 L e.1 a j) :=
  ⟨a, vals, .s32x32b, h, hj, (tcDataCell_s32x32b _ _ _ _).symm⟩

/-- A `.32x32b` store's cell. -/
theorem storeCell32 {L : Launch} {X : Execution} {e : EvId} {a j : Nat} {vals : List Value}
    (h : X.TSt e a vals .s32x32b) (hj : j < vals.length) :
    StoreCell L X e (tcDataCell32 L e.1 a j) :=
  ⟨a, vals, .s32x32b, j, h, hj, (tcDataCell_s32x32b _ _ _ _).symm⟩

/-- The thread layer's facts for the P-ready objects as mbarrier objects: who arrives on them and
who polls them, from the run invariants of the softmax (`Softmax.Counts`), the correction
(`Correction.Counts`) and the MMA warp (`Mma.Counts`), and the commit targets and copy barriers of
the kernel's sites. -/
structure PReadyFacts (L : Launch) (X : Execution) : Prop where
  /-- An arrival on stage `st`'s P-ready object of CTA `c` is a softmax thread's of the stage or a
  correction thread's, of the pair led by `c`: one unit without transaction bytes, a release at
  cluster scope. -/
  p_arrive : ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads → st < 2 →
    X.get (g, i) = some ⟨pc, .arrive (pReadyBar L c st) tx cnt rel sc⟩ →
      leadCta (ctaOf L g) = c ∧
        ((warpOf L g < 8 ∧ warpOf L g / 4 = st) ∨ (8 ≤ warpOf L g ∧ warpOf L g < 12)) ∧
        tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cluster
  /-- A poll of stage `st`'s P-ready object of CTA `c` is a thread's of warp 12 of `c`, with the
  parity of its earlier successful polls of the object; a successful one acquires at cluster
  scope. -/
  p_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads → st < 2 →
    X.get (g, i) = some ⟨pc, .wait (pReadyBar L c st) p ok acq sc⟩ →
      ctaOf L g = c ∧ warpOf L g = 12 ∧
        p % 2 = okPolls (pReadyBar L c st) ((X.tr g).take i) % 2 ∧
        (ok = true → acq = true ∧ sc = .cluster)
  /-- No tensor copy completes on a P-ready object. -/
  p_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ pReadyBar L c st
  /-- No commit arrives on a P-ready object. -/
  p_commit : ∀ {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}, st < 2 →
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp rank ≠ some (pReadyBar L c st)

/-- The thread layer's facts for the S-full objects as mbarrier objects: only the MMA thread's
commits arrive on them (no thread arrives, no copy completes on them), and a poll of one is a
softmax thread's of its stage and CTA, with the parity of its earlier successful polls of the
object; a successful one acquires at cluster scope. A commit notifying stage `st`'s object of
CTA `c` is the elected lane's of warp 12 of `c`'s pair leader and names the stage's object of
its own CTA (`s_commit`, from the MMA warp's run invariant `Mma.Counts` and its commit sites). -/
structure SFullFacts (L : Launch) (X : Execution) : Prop where
  s_arrive : ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, st < 2 →
    X.get (g, i) ≠ some ⟨pc, .arrive (sFullBar L c st) tx cnt rel sc⟩
  s_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ sFullBar L c st
  s_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads → st < 2 →
    X.get (g, i) = some ⟨pc, .wait (sFullBar L c st) p ok acq sc⟩ →
      ctaOf L g = c ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st ∧
        p % 2 = okPolls (sFullBar L c st) ((X.tr g).take i) % 2 ∧
        (ok = true → acq = true ∧ sc = .cluster)
  s_commit : ∀ {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}, g < L.threads → st < 2 →
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (sFullBar L c st) →
      warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
        sp.mbar = sFullBar L (ctaOf L g) st

end
end PTX.Kernels.FlashAttn4Fwd.Proof

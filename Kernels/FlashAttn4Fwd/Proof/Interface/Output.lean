-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats

@[expose] public section

/-! # What the thread layer exports for the output staging ring

Each CTA stages the normalized output `O / l` of stage `st` in 32768 bytes of shared memory from
offset `3072 + 32768 st` (`InStage`): two halves of 16384 bytes (head columns 0-63 and 64-127),
each 128 rows of 128 bytes, 128B-swizzled within a row's line. The correction thread of row `ρ`
(`rowOf`) writes exactly its two lines of the stage (`InLine`, offset
`3072 + 32768 st + 16384 hh + 128 ρ`), with generic `st.shared.v4` stores, then fences the proxies
(`fence.proxy.async.shared::cta`) and arrives on the stage's staged barrier (`stagedBar`, offset
`256 + 8 st`, count 128). Each of the 32 lanes of the store warp (warp 13) polls it, issues the
stage's two tensor stores (TMA) from the staging buffer, waits for their source reads
(`cp.async.bulk.wait_group.read`) and arrives on the stage's free barrier (`freeBar`, offset
`272 + 8 st`, count 32), which the correction polls before it writes the stage again; its first
poll passes on the fresh barrier.

The fields are event-level facts of single threads, from the run invariants of the correction
(`Correction.Counts`) and of the store warp (`Store.Counts`): the item of a correction write is the
number of its staged arrivals of the stage before it, the item of a tensor store the number of its
lane's free arrivals of the stage before it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- Stage `st`'s staged barrier in CTA `c`. -/
def stagedBar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (256 + 8 * st)⟩

/-- Stage `st`'s free barrier in CTA `c`. -/
def freeBar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (272 + 8 * st)⟩

theorem stagedBar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    stagedBar L c st = FBar.loc L c (.oStaged st) := rfl

theorem freeBar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    freeBar L c st = FBar.loc L c (.oFree st) := rfl

/-- A byte of stage `st`'s staging buffer in CTA `c`. -/
def InStage (L : Launch) (c st : Nat) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = c ∧ L.sharedBase + (3072 + 32768 * st) ≤ l.addr ∧
    l.addr < L.sharedBase + (35840 + 32768 * st)

/-- A byte of the staging buffers of either stage, in some CTA. -/
def InStaging (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 3072 ≤ l.addr ∧ l.addr < L.sharedBase + 68608

/-- The first byte of row `ρ`'s line in half `hh` of stage `st`. -/
def lineBase (L : Launch) (st hh ρ : Nat) : Nat :=
  L.sharedBase + (3072 + 32768 * st + 16384 * hh + 128 * ρ)

/-- Access `a` lies in row `ρ`'s line of half `hh` of stage `st` in CTA `c`. -/
def InLine (L : Launch) (c st hh ρ : Nat) (a : Acc) : Prop :=
  a.loc.space = .shared ∧ a.loc.cta = c ∧ lineBase L st hh ρ ≤ a.loc.addr ∧
    a.loc.addr + a.size ≤ lineBase L st hh ρ + 128

/-- A correction thread's write of stage `st`'s staging buffer: in one of its row's two lines, after
one more successful poll of the stage's free barrier than its staged arrivals of the stage; every
later staged arrival of the stage by the thread comes after a proxy fence that follows the write
with no staged arrival of the stage between. -/
def CorrStage (L : Launch) (X : Execution) (g i : Nat) (a : Acc) (st : Nat) : Prop :=
  (∃ hh < 2, InLine L (ctaOf L g) st hh (rowOf L g) a) ∧
    okPolls (freeBar L (ctaOf L g) st) ((X.tr g).take i) =
      arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take i) + 1 ∧
    ∀ e pce tx cnt rel sc, i < e →
      X.get (g, e) = some ⟨pce, .arrive (stagedBar L (ctaOf L g) st) tx cnt rel sc⟩ →
      ∃ f pc, i < f ∧ f < e ∧
        X.get (g, f) = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
        arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take f) =
          arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take i)

/-- A store lane's tensor store at `pc` of stage `st`: a copy (no reduction) whose source bytes are
in the stage's staging buffer of the lane's CTA; after one more successful poll of the stage's
staged barrier than its free arrivals of the stage, which number the earlier executions of the
instruction; and every later free arrival of the stage and the exit of the lane come after a
`.read` bulk-group wait covering it, with no free arrival of the stage between. -/
def StoreSrc (L : Launch) (X : Execution) (g i pc : Nat) (s : TensorStore.Spec) (st : Nat) :
    Prop :=
  s.reduce = none ∧
    (∀ x y k l, TensorStore.readLoc s x y k = some l → InStage L (ctaOf L g) st l) ∧
    okPolls (stagedBar L (ctaOf L g) st) ((X.tr g).take i) =
      arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take i) + 1 ∧
    ((X.tr g).take i).countP (·.pc == pc) = arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take i) ∧
    ∀ e pce, i < e →
      (X.get (g, e) = some ⟨pce, .exit⟩ ∨ ∃ tx cnt rel sc,
        X.get (g, e) = some ⟨pce, .arrive (freeBar L (ctaOf L g) st) tx cnt rel sc⟩) →
      ∃ w, i < w ∧ w < e ∧ BulkWaitsFor X .read (g, i) (g, w) ∧
        arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take w) =
          arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take i)

/-- The thread layer's facts for the output staging ring. -/
structure OutputFacts (L : Launch) (X : Execution) : Prop where
  /-- Every generic access of a staging byte is a correction thread's write of a stage. -/
  staging_access : ∀ {g i : Nat} {a : Acc} {w : Bool} {l : Loc}, g < L.threads →
    X.Access (g, i) a w → a.Covers l → InStaging L l →
      8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ w = true ∧ ∃ st < 2, CorrStage L X g i a st
  /-- Every tensor store is a store lane's, of a stage. -/
  store_tma : ∀ {g i pc addr : Nat} {s : TensorStore.Spec}, g < L.threads →
    X.get (g, i) = some ⟨pc, .tensorStore addr s⟩ →
      warpOf L g = 13 ∧ ∃ st < 2, StoreSrc L X g i pc s st
  /-- An arrival on a staged barrier is a correction thread's of the barrier's CTA: one release
  arrival without transaction bytes, after more successful polls of the stage's free barrier than
  its earlier staged arrivals of the stage. -/
  staged_arrive : ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, i) = some ⟨pc, .arrive (stagedBar L c st) tx cnt rel sc⟩ →
      8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals (stagedBar L c st) ((X.tr g).take i) + 1 ≤
        okPolls (freeBar L c st) ((X.tr g).take i)
  /-- A poll of a staged barrier is a store lane's of the barrier's CTA, with the parity of its
  earlier successful polls of the barrier; a successful one acquires. -/
  staged_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, i) = some ⟨pc, .wait (stagedBar L c st) p ok acq sc⟩ →
      warpOf L g = 13 ∧ c = ctaOf L g ∧
      p % 2 = okPolls (stagedBar L c st) ((X.tr g).take i) % 2 ∧ (ok = true → acq = true)
  /-- An arrival on a free barrier is a store lane's of the barrier's CTA: one release arrival
  without transaction bytes, after more successful polls of the stage's staged barrier than its
  earlier free arrivals of the stage. -/
  free_arrive : ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, i) = some ⟨pc, .arrive (freeBar L c st) tx cnt rel sc⟩ →
      warpOf L g = 13 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals (freeBar L c st) ((X.tr g).take i) + 1 ≤
        okPolls (stagedBar L c st) ((X.tr g).take i)
  /-- A poll of a free barrier is a correction thread's of the barrier's CTA, with the parity of
  its earlier successful polls of the barrier plus one; a successful one acquires. -/
  free_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, i) = some ⟨pc, .wait (freeBar L c st) p ok acq sc⟩ →
      8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧
      p % 2 = (okPolls (freeBar L c st) ((X.tr g).take i) + 1) % 2 ∧ (ok = true → acq = true)
  /-- No tensor copy completes on a staged or free barrier. -/
  stage_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ stagedBar L c st ∧ sp.mbar ≠ freeBar L c st
  /-- No commit arrives on a staged or free barrier. -/
  stage_commit : ∀ {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}, st < 2 →
    X.get i = some ⟨pc, .tc (.commit sp)⟩ →
      TcCommit.target sp rank ≠ some (stagedBar L c st) ∧
        TcCommit.target sp rank ≠ some (freeBar L c st)
  /-- At its staged arrival of a stage, a correction thread has written every byte of its row's
  two lines of the stage since its previous staged arrival of the stage. -/
  corr_cover : ∀ {g x pc tx cnt st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    8 ≤ warpOf L g → warpOf L g < 12 → st < 2 →
    X.get (g, x) = some ⟨pc, .arrive (stagedBar L (ctaOf L g) st) tx cnt rel sc⟩ →
    ∀ hh < 2, ∀ l : Loc, l.space = .shared → l.cta = ctaOf L g →
      lineBase L st hh (rowOf L g) ≤ l.addr → l.addr < lineBase L st hh (rowOf L g) + 128 →
      ∃ i a bs, i < x ∧ X.Writes (g, i) a bs ∧ a.Covers l ∧
        arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take i) =
          arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take x)

end
end PTX.Kernels.FlashAttn4Fwd.Proof

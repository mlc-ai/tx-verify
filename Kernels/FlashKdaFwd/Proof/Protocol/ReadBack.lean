-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.StoreCover
public import Lemmas.Order.GuardObserver
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # Which write a read of the union region returns

The order half of the value layer's memory contract (`Proof/Values/Contract.lean`, `ReadBack`),
per byte, for two classes of reads. The statements say which performed write the read returns;
what that write contains is a hypothesis (the witness has a byte `b`), to be supplied by the
layer that knows the load's box.

* `UnionFacts.input_read_byte`: a compute thread's read of a byte of input buffer `s` in the
  tile loop returns the byte written by the load of the use that the thread polled last
  (`q / 70 + 1` = the thread's successful polls of `loadFull s`, for a load with `q` earlier
  ones on that barrier) whose slot is at the byte.
* `UnionFacts.early_read_byte`: a read of a byte of the union region with at most five
  `bar.sync 0` before it (the conversion loop's `ld.b32`, the carry loads) returns the byte
  written by the initial-state load whose slot is at the byte.

Both are `ConflictsOrdered.read_byte` (`Lemmas/Protocol/RegionOrder.lean`) on the order of the
union region (`UnionFacts.ordered`): the witness write is visible to the read
(`load_before_thread`, `init_before_thread`), and every other performed write of the byte that
is visible to the read is the witness or is visible to it. The other writers are found by the
classification: a load of an earlier use of the stage and an initial-state load are visible to
the witness (`load_before_load`, `init_before_async`); a load of the same use is the witness
(the same piece, so the same load, so the same slot); the read is visible to a load of a later
use, to a tile load (for an early read) and to a thread write of a later phase, so these are
not visible to the read.

**Hypotheses beyond the contracts**: consistency and `SyncGuarded L K X`. The latter is used
once, for "visibility at a byte is asymmetric" (`modelCausality_asymm`,
`Lemmas/Order/GuardObserver.lean`; `GuardOk` and `DepStepAcyclic` follow from consistency). For
the kernel `Proof/Progress/Guard.lean: syncGuarded` gives it from consistency and safety.

**Definedness.** A read returns a byte of a *performed* write. For a thread write that is
`write_defined`; for a load it is the hypothesis `hbyte` (`TensorCopy.writeByte o x y z = some
b`): the load has written a defined byte at the slot. When the launch byte that a load copies
is undefined the load performs no write of that slot in the sense of the memory model, and the
read returns the byte of an earlier write.

## The list forms

`UnionFacts.stage_read` (A) and `UnionFacts.early_read` (C) state the same for a whole read
event, with the content as a parameter: `bs = (List.range a.size).map fun i => content (o + i)`.
Their one extra hypothesis is the coverage and content of the loads, on issue events and
records: every offset has a slot of a named load (the load with `70 u + p` earlier ones on
`loadFull s`, resp. with `q` earlier ones on the state barrier) whose record holds the defined
content byte. That the issue event and its record exist is derived from the reading thread's
poll (`LoadFacts.full_observes_copy`, `StateFacts.observes_load`, then
`WaitObserves.load_mbar` and `load_notified`).

`stage_read` names the use of the stage by the reading thread's polls (`u + 1` successful polls
of `loadFull s`; the tile is `3 u + s`) and asks that the read does not meet the 64 bytes at
offsets 4160 to 4224 of the stage, which no tile load writes (a read of one of them returns
the initial-state load's byte).

`StateAccFacts.acc_read` (B) is the list form for a 16-byte read of a row of `state_acc` in the
tile loop: the bytes of the lane's own last 16-byte write of the row, or, when it has made
none, `accInit`. (A lane's own 2-byte conversion store can be at the address of a row it reads
in the first tile, so the alternatives speak of 16-byte writes.) Its hypotheses beyond
`StateAccFacts` were tested on the simulator (all 192 threads; 0, 16, 37 tokens): a tile-loop
access of `state_acc` is 16 bytes at a multiple of 16; a conversion write is 2 bytes; a thread
writes a byte at most once in the conversion loop; every byte of `state_acc` has a conversion
write.

## Not written

* **D, the output buffers** (the store leader's generic reads and the tensor stores' source
  reads): the witness is the owner's last write of the byte before its arrival on `storeFull`
  (`StoreCover.out_cover` gives one since the previous arrival; "last" as a hypothesis on the
  witness). Same pattern as `input_read_byte`, with `StoreFacts.publish_output`,
  `output_before_leader` for visibility and `StoreFacts.release_output`,
  `leader_before_output`, `release_of_bar`, `bar_before` for the later writers. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat} {O : Owners}

/-- **A compute thread's read of a byte of an input buffer returns the byte that the tile's
load wrote there.** The read is event `k` of compute thread `ga`; the witness is a byte write of
a load of the load leader on `loadFull s` whose use (`q / 70`, for `q` earlier loads on the
barrier) is the one the thread polled last (`huse`), with a slot at the byte (`hwl`) and a
performed, defined byte `b` (`ho`, `hbyte`). Every other writer of the byte is that write, is
visible to it, or is not visible to the read. -/
theorem UnionFacts.input_read_byte (U : UnionFacts L X T O) (hF : LifeFacts L X T)
    (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X)
    (hB : BarFacts L X T) (hN : NoEvents K X) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) (hg : SyncGuarded L K X) {c : Nat} (hc : c < L.grid) {ga : Fin 128}
    {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hrd : X.get (computeThread L c ga, k) = some ⟨pc, .rd a bs⟩) {j : Nat} (hj : j < a.size)
    {s : Fin 3} (hl : InInput L c s.val (a.loc.at j)) {i pci al x y z : Nat}
    {sp : TensorCopy.Spec} {o : TensorCopy.Observation} {b : Byte}
    (hiss : X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩)
    (hm : sp.mbar = (Bar.loadFull s).loc L c)
    (huse : ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70
        + 1 = okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c ga)).take k))
    (hwl : TensorCopy.writeLoc sp x y z = some (a.loc.at j))
    (ho : X.tensor (loadLeader L c, i) = some o)
    (hbyte : TensorCopy.writeByte o x y z = some b) : bs[j]? = some (some b) := by
  have hl' : InUnion L c (a.loc.at j) := hl.union s.isLt
  have hacc : X.Access (computeThread L c ga, k) a false := .inl ⟨bs, ⟨pc, hrd⟩, rfl⟩
  have ha : a.Covers (a.loc.at j) := ⟨rfl, rfl, Nat.le_add_right _ _, by
    simp only [Loc.at]
    omega⟩
  have hcov := load_covers hiss hwl
  have hgk := computeThread_lt hb hc ga
  have hgdiv : computeThread L c ga / L.block = c := computeThread_div hb ga
  have hldiv : loadLeader L c / L.block = c := thr_div hb (by decide)
  have hgl := Frame.lt_of_get hX hiss
  have hk : k < (X.tr (computeThread L c ga)).length := (List.getElem?_eq_some_iff.mp hrd).1
  have hil : i < (X.tr (loadLeader L c)).length := (List.getElem?_eq_some_iff.mp hiss).1
  have asym : ∀ {w' : Ref},
      modelCausality L X (a.loc.at j) w' (.thread (computeThread L c ga, k)) →
      modelCausality L X (a.loc.at j) (.thread (computeThread L c ga, k)) w' → False :=
    fun h h' => modelCausality_asymm hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk
      (show X.RefPresent (.thread (computeThread L c ga, k)) from ⟨_, hrd⟩) h h'
  -- the load is a tile load of stage `s`
  obtain ⟨hbarL, hpieceL, hpollL⟩ : bar0Before X (loadLeader L c, i) = 6 ∧
      O.piece (a.loc.at j) = ((X.tr (loadLeader L c)).take i).countP
        (issuesTo ((Bar.loadFull s).loc L c)) % 70 ∧
      1 ≤ okPolls (Bar.state.loc L c) ((X.tr (loadLeader L c)).take i) := by
    rcases U.load hiss hwl hl' with ⟨hm', -⟩ | ⟨s', hm', h1, -, h3, h4⟩
    · exact absurd (Bar.loc_inj (hm.symm.trans hm')).1 (by simp)
    · obtain rfl : s = s' := by
        have := (Bar.loc_inj (hm.symm.trans hm')).1
        simpa using this
      exact ⟨h1, h3, h4⟩
  obtain ⟨-, -, hgeL, -⟩ := hLd.full_issue hgl hiss hm
  have hv : modelCausality L X (a.loc.at j) (.async (loadLeader L c, i) (.write (.load x y z)))
      (.thread (computeThread L c ga, k)) :=
    load_before_thread hLd hI hB hN hX hb hc s hiss hm ga hk huse.le hcov
  -- the read is of class `input`
  obtain ⟨hbarR, hgateR⟩ : bar0Before X (computeThread L c ga, k) ≤ 6 ∧
      arrivals ((Bar.loadEmpty s).loc L c) ((X.tr (computeThread L c ga)).take k) + 1 ≤
        okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c ga)).take k) := by
    obtain ⟨-, -, hcls⟩ := U.thread hacc ha hl'
    rcases hcls with ⟨-, hb2⟩ | ⟨a2, s2, hg2, -, hb2, hl2, hgt2⟩ | ⟨_, _, _, hw2, -⟩ |
      ⟨o2, hg2, -⟩ | ⟨_, _, hw2, -⟩
    · -- an early read is visible to the load, which is visible to the read
      obtain ⟨f, pcf, hif, hfget, hlt⟩ := U.fence_before hB hX hb hacc (.inl rfl) hb2
        (hgdiv.trans hldiv.symm) hil (by omega)
      exact (asym hv (publish_of_bar (hB.handoff0 hX hb) hif hfget
        ⟨hgk, hgl, hgdiv.trans hldiv.symm⟩ hil hlt hl'.1 (hl'.2.1.trans hgdiv.symm) hcov)).elim
    · obtain rfl : s = s2 := Fin.ext (input_stage_unique hl hl2)
      exact ⟨hb2.le, hgt2⟩
    · cases hw2
    · exfalso
      unfold computeThread storeLeader thr at hg2
      have := ga.isLt
      omega
    · cases hw2
  have he : X.MemReads (.thread (computeThread L c ga, k)) a bs := .inl ⟨pc, hrd⟩
  have hspec : o.spec = sp := by
    obtain ⟨a', pc', hio⟩ := (hX.effectValidity.tensor _ o ho).1
    rw [hiss] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  have hw : X.MemWrites (.async (loadLeader L c, i) (.write (.load x y z)))
      { loc := a.loc.at j, size := 1 } [b] :=
    ⟨o, al, b, ho, ⟨pci, hspec ▸ hiss⟩, hspec ▸ hwl, hbyte, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hres := ConflictsOrdered.read_byte hX
    (U.ordered hF hLd hSt hS hI hB hN hX hb c) he hj
    (by
      rintro i' acc old new ⟨h1, pc', h2⟩
      cases h1
      rw [hrd] at h2
      cases h2)
    hl' hw ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩ hv (by
      intro w' dst' bytes hw' hcov' hvis
      rcases intent_cases hN hw'.intent hcov' hl' with ⟨g1, i1, rfl, hacc1⟩ |
        ⟨g1, i1, pc1, al1, sp1, x1, y1, z1, rfl, -, hiss1, hwl1⟩ |
        ⟨_, _, _, _, _, _, _, _, -, hfalse, -⟩
      · -- a thread write: only a final-state write covers the byte, and the read precedes it
        obtain ⟨hgc1, -, hcls1⟩ := U.thread hacc1 hcov' hl'
        obtain ⟨ev1, hev1, -, -⟩ := access_kind hacc1
        have hg1 := Frame.lt_of_get hX hev1
        have hk1 : i1 < (X.tr g1).length := (List.getElem?_eq_some_iff.mp hev1).1
        rcases hcls1 with ⟨hw1, -⟩ | ⟨_, _, _, hw1, -⟩ | ⟨a1, o1, hg1', hw1, hb1, hl1, -⟩ |
          ⟨_, _, hw1, -⟩ | ⟨a1, hg1', hw1, hb1, hown1⟩
        · cases hw1
        · cases hw1
        · exact (input_output_apart s.isLt hl hl1).elim
        · cases hw1
        · exact (asym hvis (bar_before hB hX hb ⟨hgk, hg1, hgdiv.trans hgc1.symm⟩ hk1
            (by rw [bar0UpTo_of_access hacc]; omega))).elim
      · -- a byte write of a load
        have hcov1 := load_covers hiss1 hwl1
        have hg1 := Frame.lt_of_get hX hiss1
        have hk1 : i1 < (X.tr g1).length := (List.getElem?_eq_some_iff.mp hiss1).1
        rcases U.load hiss1 hwl1 hl' with ⟨hm1, -⟩ | ⟨s1, hm1, hbar1, hl1, hpiece1, hpoll1⟩
        · obtain ⟨rfl, -, -⟩ := hS.issue hg1 hiss1 hm1
          obtain ⟨jj, pcw, par, acq, sc, hjk, hwp, -⟩ :=
            MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpollL
          exact .inr (init_before_async hS hI hB hN hX hb hc hiss1 hm1 hwp hjk hil hcov1 hcov)
        · obtain rfl : s = s1 := Fin.ext (input_stage_unique hl hl1)
          obtain ⟨rfl, -, hge1, -⟩ := hLd.full_issue hg1 hiss1 hm1
          rcases Nat.lt_trichotomy
              (((X.tr (loadLeader L c)).take i1).countP
                (issuesTo ((Bar.loadFull s).loc L c)) / 70)
              (((X.tr (loadLeader L c)).take i).countP
                (issuesTo ((Bar.loadFull s).loc L c)) / 70) with hlt | heq | hgt
          · exact .inr (load_before_load hLd hI hB hN hX hb hc s hiss1 hm1 hil (by omega)
              hcov1 hcov)
          · -- the same use: the same piece, so the same load, so the same stage
            have hp := hpiece1.symm.trans hpieceL
            obtain rfl : i1 = i := nthEv_unique (p := issuesTo ((Bar.loadFull s).loc L c))
              hiss1 (by simp [issuesTo, hm1]) hiss (by simp [issuesTo, hm]) (by omega)
            rw [hiss] at hiss1
            simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hiss1
            obtain ⟨-, -, rfl⟩ := hiss1
            exact .inl (same_load hwl1 hwl)
          · -- a later use: the read is visible to the load
            exact (asym hvis (hLd.publish_input hI hB hN hX hb hc s ga hacc ha hl le_rfl hk1
              (by omega) hcov1)).elim
      · cases hfalse)
  rw [hres]
  simp [wbyte]

/-- **A read of a byte of the union region before the sixth `bar.sync 0` returns the byte that
the initial-state load wrote there** (the conversion loop's reads and the carry loads). The
witness is a byte write of a load of the load leader on the state barrier with a slot at the
byte and a performed, defined byte `b`. Every other writer of the byte is that write or is not
visible to the read. -/
theorem UnionFacts.early_read_byte (U : UnionFacts L X T O) (hF : LifeFacts L X T)
    (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X)
    (hB : BarFacts L X T) (hN : NoEvents K X) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) (hg : SyncGuarded L K X) {c g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (hrd : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hbar : bar0Before X (g, k) ≤ 5) {j : Nat} (hj : j < a.size)
    (hl : InUnion L c (a.loc.at j)) {i pci al x y z : Nat} {sp : TensorCopy.Spec}
    {o : TensorCopy.Observation} {b : Byte}
    (hiss : X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩)
    (hm : sp.mbar = Bar.state.loc L c)
    (hwl : TensorCopy.writeLoc sp x y z = some (a.loc.at j))
    (ho : X.tensor (loadLeader L c, i) = some o)
    (hbyte : TensorCopy.writeByte o x y z = some b) : bs[j]? = some (some b) := by
  have hacc : X.Access (g, k) a false := .inl ⟨bs, ⟨pc, hrd⟩, rfl⟩
  have ha : a.Covers (a.loc.at j) := ⟨rfl, rfl, Nat.le_add_right _ _, by
    simp only [Loc.at]
    omega⟩
  have hcov := load_covers hiss hwl
  obtain ⟨hgc, hpoll, -⟩ := U.thread hacc ha hl
  have hgk := Frame.lt_of_get hX hrd
  have hc : c < L.grid := hgc ▸ cta_lt hb hgk
  have hldiv : loadLeader L c / L.block = c := thr_div hb (by decide)
  have hgl := Frame.lt_of_get hX hiss
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hrd).1
  have asym : ∀ {w' : Ref}, modelCausality L X (a.loc.at j) w' (.thread (g, k)) →
      modelCausality L X (a.loc.at j) (.thread (g, k)) w' → False :=
    fun h h' => modelCausality_asymm hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk
      (show X.RefPresent (.thread (g, k)) from ⟨_, hrd⟩) h h'
  have hblock : O.block (a.loc.at j) =
      ((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c)) := by
    rcases U.load hiss hwl hl with ⟨-, h1⟩ | ⟨s', hm', -⟩
    · exact h1
    · exact absurd (Bar.loc_inj (hm.symm.trans hm')).1 (by simp)
  obtain ⟨jj, pcw, par, acq, sc, hjk, hwp, -⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpoll
  have hv : modelCausality L X (a.loc.at j) (.async (loadLeader L c, i) (.write (.load x y z)))
      (.thread (g, k)) := init_before_thread hS hI hB hN hX hb hc hiss hm hwp hjk hk hcov
  have he : X.MemReads (.thread (g, k)) a bs := .inl ⟨pc, hrd⟩
  have hspec : o.spec = sp := by
    obtain ⟨a', pc', hio⟩ := (hX.effectValidity.tensor _ o ho).1
    rw [hiss] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  have hw : X.MemWrites (.async (loadLeader L c, i) (.write (.load x y z)))
      { loc := a.loc.at j, size := 1 } [b] :=
    ⟨o, al, b, ho, ⟨pci, hspec ▸ hiss⟩, hspec ▸ hwl, hbyte, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hres := ConflictsOrdered.read_byte hX
    (U.ordered hF hLd hSt hS hI hB hN hX hb c) he hj
    (by
      rintro i' acc old new ⟨h1, pc', h2⟩
      cases h1
      rw [hrd] at h2
      cases h2)
    hl hw ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩ hv (by
      intro w' dst' bytes hw' hcov' hvis
      rcases intent_cases hN hw'.intent hcov' hl with ⟨g1, i1, rfl, hacc1⟩ |
        ⟨g1, i1, pc1, al1, sp1, x1, y1, z1, rfl, -, hiss1, hwl1⟩ |
        ⟨_, _, _, _, _, _, _, _, -, hfalse, -⟩
      · -- a thread write is in the tile loop or after it: the read precedes it
        obtain ⟨hgc1, -, hcls1⟩ := U.thread hacc1 hcov' hl
        obtain ⟨ev1, hev1, -, -⟩ := access_kind hacc1
        have hg1 := Frame.lt_of_get hX hev1
        have hk1 : i1 < (X.tr g1).length := (List.getElem?_eq_some_iff.mp hev1).1
        have hafter : 6 ≤ bar0Before X (g1, i1) → False := fun h6 =>
          asym hvis (bar_before hB hX hb ⟨hgk, hg1, hgc.trans hgc1.symm⟩ hk1
            (by rw [bar0UpTo_of_access hacc]; omega))
        rcases hcls1 with ⟨hw1, -⟩ | ⟨_, _, _, hw1, -⟩ | ⟨_, _, _, _, hb1, -⟩ |
          ⟨_, _, hw1, -⟩ | ⟨_, _, _, hb1, -⟩
        · cases hw1
        · cases hw1
        · exact (hafter (by omega)).elim
        · cases hw1
        · exact (hafter (by omega)).elim
      · have hcov1 := load_covers hiss1 hwl1
        have hg1 := Frame.lt_of_get hX hiss1
        have hk1 : i1 < (X.tr g1).length := (List.getElem?_eq_some_iff.mp hiss1).1
        rcases U.load hiss1 hwl1 hl with ⟨hm1, hblock1⟩ | ⟨s1, hm1, hbar1, -⟩
        · -- a load of the initial state at the byte: the same block, so the same load
          obtain ⟨rfl, -, -⟩ := hS.issue hg1 hiss1 hm1
          obtain rfl : i1 = i := nthEv_unique (p := issuesTo (Bar.state.loc L c)) hiss1
            (by simp [issuesTo, hm1]) hiss (by simp [issuesTo, hm]) (hblock1.symm.trans hblock)
          rw [hiss] at hiss1
          simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hiss1
          obtain ⟨-, -, rfl⟩ := hiss1
          exact .inl (same_load hwl1 hwl)
        · -- a tile load: the read is visible to it (the fence 1401, then the CTA barrier)
          obtain ⟨rfl, -, -, -⟩ := hLd.full_issue hg1 hiss1 hm1
          obtain ⟨f, pcf, hif, hfget, hlt⟩ := U.fence_before hB hX hb hacc (.inl rfl) hbar
            (hgc.trans hldiv.symm) hk1 (by omega)
          exact (asym hvis (publish_of_bar (hB.handoff0 hX hb) hif hfget
            ⟨hgk, hg1, hgc.trans hldiv.symm⟩ hk1 hlt hl.1 (hl.2.1.trans hgc.symm) hcov1)).elim
      · cases hfalse)
  rw [hres]
  simp [wbyte]

/-! ## List forms, with the content as a parameter -/

/-- **A. A read of the input stage returns the content of the tile's loads.** Event `k` of
compute thread `ga` of CTA `c` reads `a.size` bytes at offset `o` of input buffer `s`, after
`u + 1` successful polls of `loadFull s` (so in tile `3 u + s`), outside the 64-byte hole.
`sb` is the content of the stage. `hsb` is the coverage and content of the loads: every offset
outside the hole has a position `p < 70` and a slot such that the load leader's load with
`70 u + p` earlier ones on `loadFull s` has that slot at the byte and its record holds the
defined byte `sb o'` there. It speaks of issue events and records only. -/
theorem UnionFacts.stage_read (U : UnionFacts L X T O) (hF : LifeFacts L X T)
    (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X)
    (hB : BarFacts L X T) (hN : NoEvents K X) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) (hg : SyncGuarded L K X) {c : Nat} (hc : c < L.grid) {ga : Fin 128}
    {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hrd : X.get (computeThread L c ga, k) = some ⟨pc, .rd a bs⟩) (s : Fin 3) (u o : Nat)
    (sb : Nat → Option Byte)
    (hpolls : okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c ga)).take k) =
      u + 1)
    (hloc : a.loc = ⟨.shared, c, L.sharedBase + (32768 + 18048 * s.val + o)⟩)
    (hfree : o + a.size ≤ 4160 ∨ (4224 ≤ o ∧ o + a.size ≤ 18048))
    (hsb : ∀ o', o' < 18048 → (o' < 4160 ∨ 4224 ≤ o') → ∃ p < 70, ∃ x y z,
      ∀ i pci al sp, X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩ →
        sp.mbar = (Bar.loadFull s).loc L c →
        ((X.tr (loadLeader L c)).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) =
          70 * u + p →
        TensorCopy.writeLoc sp x y z =
            some ⟨.shared, c, L.sharedBase + (32768 + 18048 * s.val + o')⟩ ∧
          ∀ rec, X.tensor (loadLeader L c, i) = some rec → rec.effects.notified = true →
            TensorCopy.writeByte rec x y z = sb o' ∧ (sb o').isSome) :
    bs = (List.range a.size).map fun i => sb (o + i) := by
  have he : X.MemReads (.thread (computeThread L c ga, k)) a bs := .inl ⟨pc, hrd⟩
  have hlen : bs.length = a.size := (hX.rf _ a bs he).1
  obtain ⟨j, pcw, par, acq, sc, hjk, hw, hu⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := (Bar.loadFull s).loc L c) (h := computeThread L c ga) (f := k) (c := u) (by omega)
  apply List.ext_getElem?
  intro i'
  by_cases hi' : i' < a.size
  · obtain ⟨p, hp, x, y, z, hwit⟩ := hsb (o + i') (by omega) (by omega)
    have hobs := hLd.full_observes_copy hI hB hN hX hb hc s ga hw hu ⟨p, hp⟩
    obtain ⟨pci, al, sp, hiss, hm⟩ := hobs.load_mbar hX
    obtain ⟨rec, hrec, hnot⟩ := hobs.load_notified hX
    obtain ⟨-, hcnt⟩ := nthEv_spec_of_get hiss
    obtain ⟨hwl, hcont⟩ := hwit _ pci al sp hiss hm hcnt
    obtain ⟨hbyte, hsome⟩ := hcont rec hrec hnot
    obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.mp hsome
    have hlocj : a.loc.at i' =
        ⟨.shared, c, L.sharedBase + (32768 + 18048 * s.val + (o + i'))⟩ := by
      rw [hloc]
      simp only [Loc.at, Loc.mk.injEq, true_and]
      omega
    have hin : InInput L c s.val (a.loc.at i') := by
      rw [hlocj]
      simp only [InInput, InShared]
      refine ⟨trivial, trivial, ?_, ?_⟩ <;> omega
    have hres := U.input_read_byte hF hLd hSt hS hI hB hN hX hb hg hc hrd hi' hin hiss hm
      (by rw [hcnt, hpolls]; omega) (hlocj ▸ hwl) hrec (hbyte.trans hbb)
    rw [hres]
    simp [hi', hbb]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- **C. A read of the buffer region before the sixth `bar.sync 0` returns the content of the
initial-state loads** (the conversion loop's reads, the carry loads). Event `k` of thread `g`
reads `a.size` bytes at offset `o` of the union region of CTA `c`. `ic` is the content. `hic`
is the coverage and content of the 16 loads: every offset has a load number `q < 16` and a slot
such that the load leader's load with `q` earlier ones on the state barrier has that slot at
the byte and its record holds the defined byte `ic o'` there. -/
theorem UnionFacts.early_read (U : UnionFacts L X T O) (hF : LifeFacts L X T)
    (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X)
    (hB : BarFacts L X T) (hN : NoEvents K X) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) (hg : SyncGuarded L K X) {c g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (hrd : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hbar : bar0Before X (g, k) ≤ 5) (o : Nat) (ic : Nat → Option Byte)
    (hloc : a.loc = ⟨.shared, c, L.sharedBase + (32768 + o)⟩) (hsz : o + a.size ≤ 65536)
    (hic : ∀ o', o' < 65536 → ∃ q < 16, ∃ x y z,
      ∀ i pci al sp, X.get (loadLeader L c, i) = some ⟨pci, .tensorIssue al sp⟩ →
        sp.mbar = Bar.state.loc L c →
        ((X.tr (loadLeader L c)).take i).countP (issuesTo (Bar.state.loc L c)) = q →
        TensorCopy.writeLoc sp x y z = some ⟨.shared, c, L.sharedBase + (32768 + o')⟩ ∧
          ∀ rec, X.tensor (loadLeader L c, i) = some rec → rec.effects.notified = true →
            TensorCopy.writeByte rec x y z = ic o' ∧ (ic o').isSome) :
    bs = (List.range a.size).map fun i => ic (o + i) := by
  have he : X.MemReads (.thread (g, k)) a bs := .inl ⟨pc, hrd⟩
  have hlen : bs.length = a.size := (hX.rf _ a bs he).1
  have hacc : X.Access (g, k) a false := .inl ⟨bs, ⟨pc, hrd⟩, rfl⟩
  apply List.ext_getElem?
  intro i'
  by_cases hi' : i' < a.size
  · have hlocj : a.loc.at i' = ⟨.shared, c, L.sharedBase + (32768 + (o + i'))⟩ := by
      rw [hloc]
      simp only [Loc.at, Loc.mk.injEq, true_and]
      omega
    have hin : InUnion L c (a.loc.at i') := by
      rw [hlocj]
      simp only [InUnion, InShared]
      refine ⟨trivial, trivial, ?_, ?_⟩ <;> omega
    have hcov : a.Covers (a.loc.at i') := ⟨rfl, rfl, Nat.le_add_right _ _, by
      simp only [Loc.at]
      omega⟩
    obtain ⟨hgc, hpoll, -⟩ := U.thread hacc hcov hin
    have hc : c < L.grid := hgc ▸ cta_lt hb (Frame.lt_of_get hX hrd)
    obtain ⟨j, pcw, par, acq, sc, hjk, hw, -⟩ :=
      MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpoll
    obtain ⟨q, hq, x, y, z, hwit⟩ := hic (o + i') (by omega)
    have hobs := hS.observes_load hI hB hN hX hb hc hw ⟨q, hq⟩
    obtain ⟨pci, al, sp, hiss, hm⟩ := hobs.load_mbar hX
    obtain ⟨rec, hrec, hnot⟩ := hobs.load_notified hX
    obtain ⟨-, hcnt⟩ := nthEv_spec_of_get hiss
    obtain ⟨hwl, hcont⟩ := hwit _ pci al sp hiss hm hcnt
    obtain ⟨hbyte, hsome⟩ := hcont rec hrec hnot
    obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.mp hsome
    have hres := U.early_read_byte hF hLd hSt hS hI hB hN hX hb hg hrd hbar hi' hin hiss hm
      (hlocj ▸ hwl) hrec (hbyte.trans hbb)
    rw [hres]
    simp [hi', hbb]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-! ## B. Rows of `state_acc` -/

/-- The last index below `k` with a property, when there is one. -/
theorem exists_last {P : Nat → Prop} : ∀ {k : Nat}, (∃ k0 < k, P k0) →
    ∃ k' < k, P k' ∧ ∀ k'', k' < k'' → k'' < k → ¬ P k''
  | 0, ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)
  | k + 1, ⟨k0, hk0, hp⟩ => by
    by_cases hk : P k
    · exact ⟨k, Nat.lt_succ_self k, hk, fun k'' h1 h2 => by omega⟩
    · have h0 : k0 < k := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk0) with h | h
        · exact h
        · exact absurd (h ▸ hp) hk
      obtain ⟨k', hk', hp', hlast⟩ := exists_last ⟨k0, h0, hp⟩
      refine ⟨k', by omega, hp', fun k'' h1 h2 => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h | h
      · exact hlast k'' h1 h
      · exact h ▸ hk

/-- The byte of a write at index `i` of a location-equal footprint. -/
theorem wbyte_at {a' : Acc} {bs' : List Byte} {loc : Loc} {i : Nat} (h : a'.loc = loc) :
    wbyte a' bs' (loc.at i) = bs'[i]? := by
  simp [wbyte, h, Loc.at]

/-- **B. A read of a row of `state_acc` in the tile loop** returns the bytes of the lane's own
last 16-byte write of that row, or, when the lane has made no 16-byte write of the row, the
bytes the conversion loop left (`accInit`). Hypotheses beyond `StateAccFacts`:
`hrow` (an access of `state_acc` with six `bar.sync 0` before it is a 16-byte access at a
multiple of 16), `hconv` (a write with three before it is a 2-byte access), `honce` (a thread
writes a byte at most once in the conversion loop), `hcover` (every byte has a write event with
three `bar.sync 0` before it), `hcontent` (such a write writes `accInit` at the byte), `hlen`
(a write event carries as many bytes as its footprint), `hrmw` (no atomic). -/
theorem StateAccFacts.acc_read (hA : StateAccFacts L X) (hB : BarFacts L X T)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) (hg : SyncGuarded L K X)
    {c g k pc o : Nat} {a : Acc} {bs : List (Option Byte)} (accInit : Nat → Option Byte)
    (hrd : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hsz : a.size = 16)
    (hloc : a.loc = ⟨.shared, c, L.sharedBase + o⟩) (ho : o + 16 ≤ 32768)
    (hbar : bar0Before X (g, k) = 6)
    (hrow : ∀ {h i : Nat} {a' : Acc} {w : Bool} {l : Loc}, X.Access (h, i) a' w →
      a'.Covers l → InStateAcc L c l → bar0Before X (h, i) = 6 →
        a'.size = 16 ∧ ∃ r, a'.loc.addr = L.sharedBase + 16 * r)
    (hconv : ∀ {h i : Nat} {a' : Acc} {l : Loc}, X.Access (h, i) a' true → a'.Covers l →
      InStateAcc L c l → bar0Before X (h, i) = 3 → a'.size = 2)
    (honce : ∀ {h i i' : Nat} {a1 a2 : Acc} {l : Loc}, X.Access (h, i) a1 true →
      X.Access (h, i') a2 true → a1.Covers l → a2.Covers l → InStateAcc L c l →
      bar0Before X (h, i) = 3 → bar0Before X (h, i') = 3 → i = i')
    (hcover : ∀ l, InStateAcc L c l → ∃ h i pcw aw bw,
      X.get (h, i) = some ⟨pcw, .wr aw bw⟩ ∧ aw.Covers l ∧ bar0Before X (h, i) = 3)
    (hcontent : ∀ {h i pcw : Nat} {aw : Acc} {bw : List Byte} {l : Loc},
      X.get (h, i) = some ⟨pcw, .wr aw bw⟩ → aw.Covers l → InStateAcc L c l →
      bar0Before X (h, i) = 3 → wbyte aw bw l = accInit (l.addr - L.sharedBase))
    (hlen : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → bs.length = a.size)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) :
    (∃ k' < k, ∃ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ ∧ a'.loc = a.loc ∧
        a'.size = 16 ∧ bs = bs'.map some ∧
        ∀ k'', k' < k'' → k'' < k → ∀ pc'' a'' bs'',
          X.get (g, k'') = some ⟨pc'', .wr a'' bs''⟩ → a''.size = 16 → a''.loc ≠ a.loc) ∨
    ((∀ k' < k, ∀ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ → a'.size = 16 →
        a'.loc ≠ a.loc) ∧
      bs = (List.range 16).map fun i => accInit (o + i)) := by
  have he : X.MemReads (.thread (g, k)) a bs := .inl ⟨pc, hrd⟩
  have hbl : bs.length = 16 := ((hX.rf _ a bs he).1).trans hsz
  have hacc : X.Access (g, k) a false := .inl ⟨bs, ⟨pc, hrd⟩, rfl⟩
  have hgk := Frame.lt_of_get hX hrd
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hrd).1
  have hR := hA.ordered hB hX hb c
  have hnr : ∀ (i : EvId) (acc : Acc) (old : List (Option Byte)) (new : Option (List Byte)),
      ¬ (Ref.thread (g, k) = .thread i ∧ X.Rmw i acc old new) := by
    rintro i' acc old new ⟨h1, pc', h2⟩
    cases h1
    rw [hrd] at h2
    cases h2
  -- the bytes of the row
  have hcovR : ∀ i', i' < 16 → a.Covers (a.loc.at i') := fun i' hi' =>
    ⟨rfl, rfl, Nat.le_add_right _ _, by simp only [Loc.at]; omega⟩
  have hin : ∀ i', i' < 16 → InStateAcc L c (a.loc.at i') := fun i' hi' => by
    rw [hloc]
    simp only [InStateAcc, InShared, Loc.at]
    refine ⟨trivial, trivial, ?_, ?_⟩ <;> omega
  have hgc : c = g / L.block := (hA.phase hacc (hcovR 0 (by omega)) (hin 0 (by omega))).2.1
  have asym : ∀ {l : Loc} {w' : Ref}, modelCausality L X l w' (.thread (g, k)) →
      modelCausality L X l (.thread (g, k)) w' → False :=
    fun h h' => modelCausality_asymm hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk
      (show X.RefPresent (.thread (g, k)) from ⟨_, hrd⟩) h h'
  -- a tile-loop access that covers a byte of the row is at the row's location
  have hsame : ∀ {h i i' : Nat} {a' : Acc} {w : Bool}, X.Access (h, i) a' w → i' < 16 →
      a'.Covers (a.loc.at i') → bar0Before X (h, i) = 6 → a'.size = 16 ∧ a'.loc = a.loc := by
    intro h i i' a' w hacc' hi' hcov' h6
    obtain ⟨hs16, r, hr⟩ := hrow hacc' hcov' (hin i' hi') h6
    obtain ⟨-, r0, hr0⟩ := hrow hacc (hcovR 0 (by omega)) (hin 0 (by omega)) hbar
    obtain ⟨h1, h2, h3, h4⟩ := hcov'
    refine ⟨hs16, ?_⟩
    rcases hl' : a'.loc with ⟨sp', ct', ad'⟩
    rw [hl'] at h1 h2 h3 h4 hr
    rw [hloc] at h1 h2 h3 h4 hr0 ⊢
    simp only [Loc.at] at h1 h2 h3 h4 hr hr0
    subst h1 h2
    congr 1
    omega
  -- a write that covers a byte of the row and is visible to the read: its thread and phase
  have hwriter : ∀ {i' : Nat} {w' : Ref} {dst' : Acc} {bytes : List Byte}, i' < 16 →
      X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at i') →
      ∃ h1 i1 pc1, w' = .thread (h1, i1) ∧ X.get (h1, i1) = some ⟨pc1, .wr dst' bytes⟩ ∧
        X.Access (h1, i1) dst' true ∧ h1 < L.threads ∧
        c = h1 / L.block ∧ (bar0Before X (h1, i1) = 3 ∨ bar0Before X (h1, i1) = 6) := by
    intro i' w' dst' bytes hi' hw' hcov'
    obtain ⟨⟨h1, i1⟩, rfl⟩ := hA.thread_only hw'.intent hcov' (hin i' hi')
    have hacc1 : X.Access (h1, i1) dst' true := hw'.intent
    obtain ⟨p1, p2, p3⟩ := hA.phase hacc1 hcov' (hin i' hi')
    rcases hw' with ⟨pc1, hg1⟩ | ⟨old, pc1, hg1⟩
    · exact ⟨h1, i1, pc1, rfl, hg1, hacc1, p1, p2, p3⟩
    · exact (hrmw _ _ _ _ _ hg1).elim
  by_cases hex : ∃ k0 < k, ∃ pc' a' bs', X.get (g, k0) = some ⟨pc', .wr a' bs'⟩ ∧
      a'.loc = a.loc ∧ a'.size = 16
  · -- the lane's last 16-byte write of the row
    obtain ⟨k', hk'k, ⟨pc', a', bs', hget', hloc', hsz'⟩, hbetween⟩ := exists_last hex
    have hacc' : X.Access (g, k') a' true := .inr (.inl ⟨bs', ⟨pc', hget'⟩, rfl⟩)
    have hcovW : ∀ i', i' < 16 → a'.Covers (a.loc.at i') := fun i' hi' => by
      have := hcovR i' hi'
      unfold Acc.Covers at this ⊢
      rw [hloc', hsz', ← hsz]
      exact this
    have hb6 : bar0Before X (g, k') = 6 := by
      rcases (hA.phase hacc' (hcovW 0 (by omega)) (hin 0 (by omega))).2.2 with h3 | h6
      · have := hconv hacc' (hcovW 0 (by omega)) (hin 0 (by omega)) h3
        omega
      · exact h6
    have hbl' : bs'.length = 16 := (hlen _ _ _ _ hget').trans hsz'
    refine .inl ⟨k', hk'k, pc', a', bs', hget', hloc', hsz', ?_, fun k'' h1 h2 pc'' a'' bs'' hg''
      hs'' hl'' => hbetween k'' h1 h2 ⟨pc'', a'', bs'', hg'', hl'', hs''⟩⟩
    apply List.ext_getElem?
    intro i'
    by_cases hi' : i' < 16
    · have hres := ConflictsOrdered.read_byte hX hR he (hsz ▸ hi') hnr (hin i' hi')
        (w := .thread (g, k')) (.inl ⟨pc', hget'⟩) (hcovW i' hi')
        (same_thread hacc' hacc hk'k (hcovW i' hi') (hcovR i' hi')) (by
          intro w' dst' bytes hw' hcov' hvis
          obtain ⟨h1, i1, pc1, rfl, hg1, hacc1, hh1, hc1, hph⟩ := hwriter hi' hw' hcov'
          rcases hph with h3 | h6
          · -- a conversion store precedes the tile loop
            have hk' : k' < (X.tr g).length := by omega
            exact .inr (bar_before hB hX hb ⟨hh1, hgk, hc1.symm.trans hgc⟩ hk'
              (by rw [bar0UpTo_of_access hacc1]; omega))
          · obtain rfl : h1 = g := hA.owner hacc1 hacc (.inl rfl) hcov' (hcovR i' hi')
              (hin i' hi') (h6.trans hbar.symm)
            rcases Nat.lt_trichotomy i1 k' with h | h | h
            · exact .inr (same_thread hacc1 hacc' h hcov' (hcovW i' hi'))
            · exact .inl (by rw [h])
            · rcases Nat.lt_trichotomy i1 k with h' | h' | h'
              · -- a 16-byte write of the row between `k'` and `k`: there is none
                obtain ⟨hs1, hl1⟩ := hsame hacc1 hi' hcov' h6
                exact (hbetween i1 h h' ⟨pc1, dst', bytes, hg1, hl1, hs1⟩).elim
              · subst h'
                rw [hrd] at hg1
                cases hg1
              · exact (asym hvis (same_thread hacc hacc1 h' (hcovR i' hi') hcov')).elim)
      rw [hres, wbyte_at hloc', List.getElem?_map]
      obtain ⟨v, hv⟩ : ∃ v, bs'[i']? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [hv]
      rfl
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  · -- no 16-byte write of the row yet: the conversion loop's stores
    refine .inr ⟨fun k' hk' pc' a' bs' hg' hs' hl' => hex ⟨k', hk', pc', a', bs', hg', hl', hs'⟩,
      ?_⟩
    apply List.ext_getElem?
    intro i'
    by_cases hi' : i' < 16
    · obtain ⟨hw, iw, pcw, aw, bw, hgw, hcw, hw3⟩ := hcover _ (hin i' hi')
      have haccw : X.Access (hw, iw) aw true := .inr (.inl ⟨bw, ⟨pcw, hgw⟩, rfl⟩)
      obtain ⟨hhw, hcw', -⟩ := hA.phase haccw hcw (hin i' hi')
      have hres := ConflictsOrdered.read_byte hX hR he (hsz ▸ hi') hnr (hin i' hi')
        (w := .thread (hw, iw)) (.inl ⟨pcw, hgw⟩) hcw
        (.inl (hB.handoff0 hX hb hw g iw k ⟨hhw, hgk, hcw'.symm.trans hgc⟩ hk
          (by rw [bar0UpTo_of_access haccw]; omega))) (by
          intro w' dst' bytes hw' hcov' hvis
          obtain ⟨h1, i1, pc1, rfl, hg1, hacc1, hh1, hc1, hph⟩ := hwriter hi' hw' hcov'
          rcases hph with h3 | h6
          · -- another conversion store of the byte: the same thread, the same event
            obtain rfl : h1 = hw := hA.owner hacc1 haccw (.inl rfl) hcov' hcw (hin i' hi')
              (h3.trans hw3.symm)
            obtain rfl : i1 = iw := honce hacc1 haccw hcov' hcw (hin i' hi') h3 hw3
            exact .inl rfl
          · -- a tile-loop write of the row: the lane's own, and not before the read
            obtain rfl : h1 = g := hA.owner hacc1 hacc (.inl rfl) hcov' (hcovR i' hi')
              (hin i' hi') (h6.trans hbar.symm)
            obtain ⟨hs1, hl1⟩ := hsame hacc1 hi' hcov' h6
            rcases Nat.lt_trichotomy i1 k with h' | h' | h'
            · exact (hex ⟨i1, h', pc1, dst', bytes, hg1, hl1, hs1⟩).elim
            · subst h'
              rw [hrd] at hg1
              cases hg1
            · exact (asym hvis (same_thread hacc hacc1 h' (hcovR i' hi') hcov')).elim)
      rw [hres, hcontent hgw hcw (hin i' hi') hw3]
      have hoff : (a.loc.at i').addr - L.sharedBase = o + i' := by
        rw [hloc]
        simp only [Loc.at]
        omega
      rw [hoff]
      simp [hi']
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end PTX.Kernels.FlashKdaFwd.Protocol

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ValuesEndsRef
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Conversion
public import Kernels.FlashKdaFwd.Proof.Protocol.Export

@[expose] public section

/-!
# What a compute thread reads from a row of the bfloat16 state copy

`ValuesEnds.readBack_acc_of` is the field `acc` of `Values.ReadBack`
(`Proof/Values/Contract.lean`), word for word, given what the Store and the Compute phase owe
(`StoreOwes`, `ComputeOwes`; `ValuesEnds.lean: readBack_acc` is the statement without the
first): a 16-byte read by a compute thread of a row of `state_acc` (the bfloat16 copy of the
state, window offsets 0 to 32767 of the thread's block) returns the bytes of the thread's own
last 16-byte write of that row, or, when it has made none, the bytes that the conversion loop
left there (`Values.accInitByte`: the bfloat16 payloads of the initial state).

It is the protocol layer's read-back `StateAccFacts.acc_read` (`Proof/Protocol/ReadBack.lean`).
That theorem takes eight hypotheses about the accesses of `state_acc`; each is proved here from
the phase that makes the access, found with the case principle of the chain (`Stage.lean`,
`Sites.lean`): the number of `bar.sync 0` before an event and the instruction of its site
decide the phase.

* `hbar` (six `bar.sync 0` before the read), in `readBack_acc_of`: `StateAccFacts.phase` gives
  three or six; with three, a read is of eight bytes (startup) or of four (conversion).
* `hrow` (an access with six before it is a 16-byte row), `acc_row6`: `ComputeOwes.acc_row`
  and `StoreOwes.acc_free`; no access is fired at an instruction of the load loop.
* `hconv` (a write with three before it is two bytes), `conv_size`: the Conversion phase's
  event shape.
* `honce` (a thread writes a byte once in the conversion loop), `conv_once`: the position of a
  conversion store is fixed by its element.
* `hcover` (every byte has a conversion write), `acc_cover`: `BarFacts.peer_bar0` (the owner
  of the byte has made its sixth `bar.sync 0`) and `Conversion.conv_cover`.
* `hcontent` (a conversion write writes `accInitByte`), in `readBack_acc_of`:
  `Values.Ends.acc_content`.
* `hlen`, `hrmw`, in `readBack_acc_of`: `Protocol.write_length`, `Protocol.no_rmw`.

**Words.** A *followed state* of thread `g` at position `k` is the state of the thread's
machine before its `k`-th event. `bar0Before X (g, k)` is the number of `bar.sync 0` events of
thread `g` before position `k`: three in the conversion loop, six in the tile loops.
`X.Access (g, k) a w` says that event `k` of thread `g` is a memory read (`w = false`) or
write (`w = true`) of the footprint `a`. An *element* `el < 16384` of the state is converted by
one thread of each block, its *owner* (`Conversion.convOwner el` is the owner's index in the
block), which writes the two bytes at window offset `2 el`.

Everything is in the namespace `Assembly.ValuesEnds`; the final `readBack_acc` is in
`ValuesEnds.lean`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before Facts UnionFacts StoreCover Owners ctaTiles
  InStateAcc BarFacts no_rmw write_length)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace ValuesEnds

/-! ### Where an access is fired -/

/-- The load sites are at instructions up to 1400 (the offsets array, the conversion loop, the
carry loads) or in the compute and the store loop. -/
theorem load_site_pc : ∀ j : Fin 178,
    (Site.load j).pc ≤ 1400 ∨ (2105 < (Site.load j).pc ∧ (Site.load j).pc ≤ 3112) := by
  decide +kernel

/-- The row reads of the `ldmatrix` instructions are at instructions of the compute loop. -/
theorem mxLoad_site_pc : ∀ j : Fin 44,
    2105 < (Site.matrixLoad j).pc ∧ (Site.matrixLoad j).pc ≤ 3112 := by decide +kernel

/-- **The number of `bar.sync 0` before a followed state, by the instruction of its site**:
`Stage.bar0_bounds` in the protocol layer's notation. -/
theorem stage_bars {k : Nat} {s : D} (hst : Stage P L X g k s) (hub : NoUb X g k) :
    (s.site.pc ≤ 384 → bar0Before X (g, k) ≤ 3) ∧
    (387 ≤ s.site.pc → s.site.pc ≤ 620 → bar0Before X (g, k) = 3) ∧
    (s.site.pc = 621 → bar0Before X (g, k) = 4) ∧
    (621 < s.site.pc → s.site.pc ≤ 1402 → bar0Before X (g, k) = 5) ∧
    (1402 < s.site.pc → s.site.pc ≤ 3113 → bar0Before X (g, k) = 6) ∧
    (3113 < s.site.pc → 7 ≤ bar0Before X (g, k)) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hst.bar0_bounds hub
  exact ⟨b1, b2, b3, b4, b5, fun h => (b6 h).1⟩

/-- **A followed state with three `bar.sync 0` before it is in the startup phase or in the
Conversion phase.** -/
theorem stage_bar3 {k : Nat} {s : D} (hst : Stage P L X g k s) (hub : NoUb X g k)
    (hbar : bar0Before X (g, k) = 3) :
    Startup.InvE P X g k s ∨
      ∃ j0 s0, StartupDone P L X g j0 s0 ∧ j0 ≤ k ∧ Conversion.Inv P X g j0 k s := by
  obtain ⟨-, -, -, b4, b5, b6⟩ := stage_bars hst hub
  have h621 : s.site.pc ≤ 621 := by
    by_contra hc
    rcases Nat.lt_or_ge 1402 s.site.pc with h | h
    · rcases Nat.lt_or_ge 3113 s.site.pc with h' | h'
      · have := b6 h'
        omega
      · have := b5 h h'
        omega
    · have := b4 (by omega) h
      omega
  rcases Nat.lt_or_ge s.site.pc 387 with h | h
  · exact .inl (hst.of_pc_startup h)
  · exact .inr (hst.of_pc_conversion h h621)

/-- **A followed state with five `bar.sync 0` before it belongs to a thread that has left the
Conversion phase**: it is in the CarryLoad phase or at the entry of a tile loop. -/
theorem convDone_of_bar5 {k : Nat} {s : D} (hst : Stage P L X g k s) (hub : NoUb X g k)
    (hbar : bar0Before X (g, k) = 5) : ∃ j1 s1, ConversionDone P L X g j1 s1 ∧ j1 ≤ k := by
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := stage_bars hst hub
  cases hst with
  | startup hI =>
    have := b1 (pc_startup hI.inv)
    omega
  | conversion _ _ hI =>
    obtain ⟨h1, h2⟩ := pc_conversion hI
    rcases Nat.lt_or_ge s.site.pc 621 with h | h
    · have := b2 h1 (by omega)
      omega
    · have := b3 (by omega)
      omega
  | carryLoad past hj _ => exact ⟨_, _, past, hj⟩
  | compute _ past hj _ _ =>
    obtain ⟨j1, s1, hc, hlen, -⟩ := past.entry
    exact ⟨j1, s1, hc, by omega⟩
  | producer _ past hj _ _ =>
    obtain ⟨j1, s1, hc, hlen, -⟩ := past.entry
    exact ⟨j1, s1, hc, by omega⟩
  | store _ past hj _ _ _ =>
    obtain ⟨j1, s1, hc, hlen, -⟩ := past.entry
    exact ⟨j1, s1, hc, by omega⟩
  | epilogue _ _ hW _ =>
    obtain ⟨h1, h2⟩ := pc_epilogue hW
    rcases Nat.lt_or_ge 3113 s.site.pc with h | h
    · have := b6 h
      omega
    · have := b5 (by omega) h
      omega

/-- **A thread leaves the startup phase at one position.** -/
theorem startupDone_unique {j j' : Nat} {s s' : D} (h : StartupDone P L X g j s)
    (h' : StartupDone P L X g j' s') : j = j' := by
  have key : ∀ {j j' : Nat} {s s' : D}, StartupDone P L X g j s → StartupDone P L X g j' s' →
      ¬ j < j' := by
    intro j j' s s' h h' hlt
    exact (h'.before j s hlt h.state).inv.not_left (L := L) ⟨j, le_rfl, s, h.state, h.out.1⟩
  have h1 := key h h'
  have h2 := key h' h
  omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **Where a memory access is fired**: at an instruction up to 1400, at one of the compute or
the store loop (2106 to 3112), or after 3113. So not at an instruction of the load loop and
not at a `bar.sync 0` (`Ref/Kinds`: a read is fired at a load site, a write at a store
site). -/
theorem access_pc {k : Nat} {a : Acc} {w : Bool} {s : D} (hacc : X.Access (g, k) a w)
    (hσ : At (code L) X g k s) :
    s.site.pc ≤ 1400 ∨ (2105 < s.site.pc ∧ s.site.pc ≤ 3112) ∨ 3113 < s.site.pc := by
  have h177 := load177_pc
  rcases hacc with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
  · refine rd_site_ind (sounds hpre) hX he hσ rfl
      (P := fun t => t.pc ≤ 1400 ∨ (2105 < t.pc ∧ t.pc ≤ 3112) ∨ 3113 < t.pc)
      (fun j => ?_) (fun j v0 => ?_) (fun j v0 v1 => ?_) (fun j v0 v1 v2 => ?_) (fun j => ?_)
    · rcases load_site_pc j with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      exact .inr (.inl ⟨Nat.lt_trans (by decide) h177.1, h177.2⟩)
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      exact .inr (.inl ⟨Nat.lt_trans (by decide) h177.1, h177.2⟩)
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      exact .inr (.inl ⟨Nat.lt_trans (by decide) h177.1, h177.2⟩)
    · exact .inr (.inl (mxLoad_site_pc j))
  · refine wr_site_ind (sounds hpre) hX he hσ rfl
      (P := fun t => t.pc ≤ 1400 ∨ (2105 < t.pc ∧ t.pc ≤ 3112) ∨ 3113 < t.pc)
      (fun j => ?_) (fun j row => ?_)
    · rcases store_site_pc j with h | h | h <;> omega
    · have := stWr_site_pc j row
      omega
  · exact (no_rmw hX he).elim

/-! ### The hypotheses of the read-back -/

/-- **`hrow`: an access with six `bar.sync 0` before it that covers a byte of `state_acc` is
an access of a whole row** (16 bytes at a multiple of 16 from `shared_mem`): it is an access
of the compute loop (`ComputeOwes.acc_row`); the store loop accesses no byte of `state_acc`
(`StoreOwes.acc_free`) and the load loop makes no access. -/
theorem acc_row6 (SO : StoreOwes P L X) (CO : ComputeOwes P L X) {h i c : Nat} {a : Acc}
    {w : Bool} {l : Loc} (hacc : X.Access (h, i) a w) (hcov : a.Covers l)
    (hl : InStateAcc L c l) (h6 : bar0Before X (h, i) = 6) :
    a.size = 16 ∧ ∃ r, a.loc.addr = L.sharedBase + 16 * r := by
  obtain ⟨e, he, hne⟩ : ∃ e, X.get (h, i) = some e ∧ ∀ f, e.kind ≠ .ub f := by
    rcases hacc with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
    · exact ⟨_, he, fun f hf => by cases hf⟩
    · exact ⟨_, he, fun f hf => by cases hf⟩
    · exact ⟨_, he, fun f hf => by cases hf⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he hne
  obtain ⟨b1, b2, b3, b4, -, b6⟩ := stage_bars hst hub
  rcases access_pc hpre hX hacc hσ with h1 | ⟨h1, h2⟩ | h1
  · exfalso
    rcases hst.pc_cases with c1 | c1 | c1 | ⟨-, c1⟩ | ⟨-, c1⟩ | ⟨-, c1⟩ | c1
    · have := b1 c1
      omega
    · rcases Nat.lt_or_ge s.site.pc 621 with h' | h'
      · have := b2 c1.1 (by omega)
        omega
      · have := b3 (by omega)
        omega
    · have := b4 (by omega) (by omega)
      omega
    · omega
    · omega
    · omega
    · omega
  · rcases Nat.lt_or_ge 2944 s.site.pc with h3 | h3
    · exfalso
      obtain ⟨-, j0, s0, -, -, -, hI, -⟩ := hst.of_pc_store h3 h2
      exact SO.acc_free h i s a w l c hg hσ (hI hub) hacc hcov hl
    · obtain ⟨-, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute h1 h3
      exact CO.acc_row h j0 i s a w l c hg hσ hI hacc hcov hl
  · have := b6 h1
    omega

/-- **`hconv`: a write with three `bar.sync 0` before it is a 2-byte write** (a conversion
store). -/
theorem conv_size {h i : Nat} {a : Acc} (hacc : X.Access (h, i) a true)
    (h3 : bar0Before X (h, i) = 3) : a.size = 2 := by
  rcases hacc with ⟨bs, -, hw⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
  · cases hw
  · have hg := Frame.lt_of_get hX he
    obtain ⟨s, j0, s0, hσ, -, -, hI⟩ := conv_of_wr3 hpre hX he h3
    obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
    obtain ⟨j, u, -, rfl⟩ := hev.wr
    rfl
  · exact (no_rmw hX he).elim

/-- **`honce`: a thread writes a byte at most once in the conversion loop**: two of its writes
with three `bar.sync 0` before them that cover one byte are stores of one element, and the
position of a conversion store in the thread's trace is fixed by the element. -/
theorem conv_once {h i i' : Nat} {a1 a2 : Acc} {l : Loc} (h1 : X.Access (h, i) a1 true)
    (h2 : X.Access (h, i') a2 true) (hc1 : a1.Covers l) (hc2 : a2.Covers l)
    (b1 : bar0Before X (h, i) = 3) (b2 : bar0Before X (h, i') = 3) : i = i' := by
  have wr : ∀ {i : Nat} {a : Acc}, X.Access (h, i) a true →
      ∃ pc bs, X.get (h, i) = some ⟨pc, .wr a bs⟩ := by
    intro i a hacc
    rcases hacc with ⟨bs, -, hw⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
    · cases hw
    · exact ⟨pc, bs, he⟩
    · exact (no_rmw hX he).elim
  obtain ⟨pc1, bs1, he1⟩ := wr h1
  obtain ⟨pc2, bs2, he2⟩ := wr h2
  have hg := Frame.lt_of_get hX he1
  obtain ⟨s, j0, s0, hσ, past, -, hI⟩ := conv_of_wr3 hpre hX he1 b1
  obtain ⟨s', j0', s0', hσ', past', -, hI'⟩ := conv_of_wr3 hpre hX he2 b2
  obtain rfl := startupDone_unique past past'
  obtain ⟨pos, hr, -, hd, hev⟩ := Conversion.event_at hpre hX hg he1 hσ hI
  obtain ⟨pos', hr', -, hd', hev'⟩ := Conversion.event_at hpre hX hg he2 hσ' hI'
  obtain ⟨j, u, rfl, rfl⟩ := hev.wr
  obtain ⟨j', u', rfl, rfl⟩ := hev'.wr
  obtain ⟨-, -, o1⟩ := Conversion.slotOf_owner
    (Conversion.elemIx_lt j.isLt (Conversion.st_round hr.pos))
  obtain ⟨-, -, o2⟩ := Conversion.slotOf_owner
    (Conversion.elemIx_lt j'.isLt (Conversion.st_round hr'.pos))
  obtain ⟨-, -, c3, c4⟩ := hc1
  obtain ⟨-, -, d3, d4⟩ := hc2
  simp only [Conversion.wrAddr] at c3 c4 d3 d4
  have hslot : Conversion.slotOf h (Conversion.elemIx j.val u) =
      Conversion.slotOf h (Conversion.elemIx j'.val u') := by omega
  have hix := congrArg Conversion.convOrd hslot
  rw [o1, o2] at hix
  simp only [Conversion.done] at hd hd'
  omega

/-- **`hcover`: every byte of `state_acc` of a block has a write with three `bar.sync 0`
before it, once a thread of the block has made six.** The owner of the byte's element is a
thread of the block; it has made its sixth `bar.sync 0` (`BarFacts.peer_bar0`: the barrier
releases when every thread of the block has arrived), so it has left the Conversion phase, and
a thread that left it has converted all its elements (`Conversion.conv_cover`). -/
theorem acc_cover (hB : BarFacts L X (ctaTiles P)) {k : Nat} (hk : k < (X.tr g).length)
    (hbar : 6 ≤ bar0Before X (g, k)) {l : Loc} (hl : InStateAcc L (g / L.block) l) :
    ∃ h i pcw aw bw, X.get (h, i) = some ⟨pcw, .wr aw bw⟩ ∧ aw.Covers l ∧
      bar0Before X (h, i) = 3 := by
  have hb := hpre.block
  have hg : g < L.threads := by
    by_contra hn
    rw [hX.outside g (by omega)] at hk
    exact absurd hk (Nat.not_lt_zero _)
  obtain ⟨l1, l2, l3, l4⟩ := hl
  -- the element of the byte and its owner
  obtain ⟨el, hel⟩ : ∃ el, el = (l.addr - L.sharedBase) / 2 := ⟨_, rfl⟩
  have hel16 : el < 16384 := by omega
  have ht : Conversion.convOwner el < 192 := by
    unfold Conversion.convOwner
    omega
  obtain ⟨h, hhdef⟩ : ∃ h, h = Protocol.thr L (g / L.block) (Conversion.convOwner el) :=
    ⟨_, rfl⟩
  have hh : h < L.threads := by
    rw [hhdef]
    exact Protocol.thr_lt hb (Protocol.cta_lt hb hg) ht
  have hdiv : h / L.block = g / L.block := by
    rw [hhdef]
    exact Protocol.thr_div hb ht
  have htid : tid h = Conversion.convOwner el := by
    rw [← block_mod hpre, hhdef]
    exact Protocol.thr_mod hb ht
  -- the owner's sixth `bar.sync 0`: it has left the Conversion phase
  obtain ⟨e, pc, md, he, hbe⟩ := hB.peer_bar0 hX hb hh hdiv hk (q := 5) (by omega)
  have helt : e < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f hf => by cases hf)
  obtain ⟨j1, s1, hdone, hj1⟩ := convDone_of_bar5 hst hub hbe
  obtain ⟨j0, s0, hsd, hlen, -⟩ := hdone.entry
  have hleft : Conversion.Left P X h L j0 e :=
    ⟨by omega, s1, by rw [← hlen]; exact hdone.state, by rw [← hlen]; exact hdone.out⟩
  -- its store of the element
  obtain ⟨hi, hslot⟩ := Conversion.slot_cover hel16 htid
  obtain ⟨-, pcw, bw, hw⟩ :=
    Conversion.conv_cover hpre hX hh hsd.state hsd.conversion_in hleft helt hi
  rw [hslot] at hw
  refine ⟨h, _, pcw, _, bw, hw, ⟨l1, ?_, ?_, ?_⟩, ?_⟩
  · show l.cta = cta h
    rw [← block_div hpre, hdiv]
    exact l2
  · show Conversion.wrAddr P el ≤ l.addr
    have := hpre.sharedBase
    unfold Conversion.wrAddr
    omega
  · show l.addr < Conversion.wrAddr P el + 2
    have := hpre.sharedBase
    unfold Conversion.wrAddr
    omega
  · have hwlt : j0 + (2 + 2 * Conversion.convOrd el) < (X.tr h).length :=
      (List.getElem?_eq_some_iff.mp hw).1
    obtain ⟨d, hσw⟩ := followed_event hpre hX hw (by rintro pc' f hf; cases hf)
    rcases Conversion.conversion_inv hpre hX hh hsd.state hsd.conversion_in
      (Nat.le_add_right _ _) hwlt hσw with hI | ⟨hle, -⟩
    · exact (Conversion.conv_store hpre hX hh hsd.state hsd.conversion_in hσw hI hw).1
    · exfalso
      simp only [Conversion.len] at hle
      omega

end

end ValuesEnds

open ValuesEnds

/-- **The field `acc` of `Values.ReadBack`**: a 16-byte read by a compute thread of a row of
the bfloat16 state copy `state_acc` of its block returns the bytes of the thread's own last
16-byte write of that row, or, when it has made no 16-byte write of the row yet (the first
tile), the bytes the conversion loop left there: the bfloat16 payloads of the initial state.

Remaining hypotheses: the protocol contracts `F`, `U`, `C` (assembly groups A, B, C1); the two
hypotheses of the sources, `StateIssues` and `WriteFrame` (group D); and what the Store and the
Compute phase still owe (`StoreOwes.acc_free`, `ComputeOwes.acc_row`). -/
theorem ValuesEnds.readBack_acc_of (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O) (C : StoreCover L X O)
    (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) (SO : StoreOwes P L X)
    (CO : ComputeOwes P L X) :
    ∀ g k pc a bs o, g % L.block < 128 → X.get (g, k) = some ⟨pc, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, P.sharedBase + o⟩ → a.size = 16 → o + 16 ≤ 32768 →
      (∃ k' < k, ∃ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ ∧ a'.loc = a.loc ∧
          a'.size = 16 ∧ bs = bs'.map some ∧
          ∀ k'', k' < k'' → k'' < k → ∀ pc'' a'' bs'',
            X.get (g, k'') = some ⟨pc'', .wr a'' bs''⟩ → a''.size = 16 → a''.loc ≠ a.loc) ∨
        ((∀ k' < k, ∀ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ → a'.size = 16 →
            a'.loc ≠ a.loc) ∧
          bs = (List.range 16).map fun i =>
            Values.accInitByte P (Values.seqOf P L g) (Values.headOf P L g) (o + i)) := by
  intro g k pc a bs o _ hrd hloc hsz ho
  have hg := Frame.lt_of_get hX hrd
  have hb := hpre.block
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hrd).1
  have hloc' : a.loc = ⟨.shared, g / L.block, L.sharedBase + o⟩ := by
    rw [hloc, hpre.sharedBase]
  have hacc : X.Access (g, k) a false := .inl ⟨bs, ⟨pc, hrd⟩, rfl⟩
  have hcov0 : a.Covers a.loc := ⟨rfl, rfl, Nat.le_refl _, by omega⟩
  have hin0 : InStateAcc L (g / L.block) a.loc := by
    rw [hloc']
    exact ⟨rfl, rfl, by simp only; omega, by simp only; omega⟩
  -- six `bar.sync 0` before the read: with three, a read is of eight or of four bytes
  have hbar : bar0Before X (g, k) = 6 := by
    rcases (F.stateAcc.phase hacc hcov0 hin0).2.2 with h3 | h6
    · exfalso
      obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX hrd (fun f hf => by cases hf)
      rcases stage_bar3 hst hub h3 with hI | ⟨j0, s0, -, -, hI⟩
      · rcases Startup.read_startup hpre hX hg hrd hσ with ⟨i, -, ha, -⟩ | hleft
        · rw [ha] at hsz
          have h8 : (8 : Nat) = 16 := hsz
          omega
        · exact hI.inv.not_left hleft
      · obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg hrd hσ hI
        obtain ⟨j, u, -, -, ha⟩ := hev.rd
        rw [ha] at hsz
        have h4 : (4 : Nat) = 16 := hsz
        omega
    · exact h6
  exact F.stateAcc.acc_read F.bars hX hb (F.syncGuarded hpre hX) (c := g / L.block)
    (fun o' => Values.accInitByte P (g / L.block % P.sequences) (g / L.block / P.sequences) o')
    hrd hsz hloc' ho hbar
    (fun hacc' hcov' hl' h6 => acc_row6 hpre hX SO CO hacc' hcov' hl' h6)
    (fun hacc' _ _ h3 => conv_size hpre hX hacc' h3)
    (fun h1 h2 c1 c2 _ b1 b2 => conv_once hpre hX h1 h2 c1 c2 b1 b2)
    (fun l hl => acc_cover hpre hX F.bars hklt (by omega) hl)
    (fun hw hc hl h3 => Values.Ends.acc_content (ValuesEnds.followed hpre hX)
      (convRef hpre hX) (earlyRead hpre hX F U hSI hW)
      (by have h1 := hpre.sharedBase; have h2 := hpre.sharedAlignment; omega) hw hc hl h3)
    (fun e pc a bs he => write_length hX C he) (fun _ _ _ _ _ => no_rmw hX)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Values

@[expose] public section

/-! # The Tensor Memory branches of `Unsafe`: collectives, resources, conflicts

*Collectives* (`no_tcDivergent`, `no_tcExited`): a thread's warp-collective `tcgen05` events
are, by their ordinal, warp 0's allocation, load, wait and deallocation, or another warp's load and
wait (`coll`); the lanes of a warp agree on them, the addresses by the column every thread keeps
(`c_eq`), and a thread that exited made all of them (`trace_full`).

*Resources* (`no_resourceUnsafe`, `no_releaseUnsafe`): the allocator's history is empty, the
allocation, or the allocation and its release (`history_shape`), so it replays without a fault,
and once every thread has exited and every operation is complete it is the whole history, which
leaves no allocation live.

*Conflicts* (`no_writesUnsafe`, `no_readsUnsafe`): the only Tensor Memory writer is the one MMA,
which reads no Tensor Memory operand. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow Tmem.Pair
noncomputable section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

/-- The source line of warp-collective instance `k` of thread `g`. -/
def collPc (g k : Nat) : Nat :=
  if g / 32 = 0 then
    (if k = 0 then Flow.tmemAlloc_0 else if k = 1 then Flow.tmemLoad_0 else if k = 2 then
      Flow.tmemWait_0
      else Flow.tmemDealloc_0)
  else if k = 0 then Flow.tmemLoad_0 else Flow.tmemWait_0

/-- What every lane must agree on in warp-collective instance `k` of thread `g`. -/
def collSt (S col g k : Nat) : TcKind :=
  if g / 32 = 0 then
    (if k = 0 then .resource .one (some (tslot S)) (.alloc 32) else if k = 1 then .ld (taddr g col)
      [] .s32x32b
      else if k = 2 then .waitLd else .resource .one none (.dealloc col 32))
  else if k = 0 then .ld (taddr g col) [] .s32x32b else .waitLd

omit hpre hX hW in
/-- Threads of the same warp. -/
theorem same_warp (hB : L.block = 128) {g h : Nat} (hs : SameWarp L g h) (hg : g < 128)
    (hh : h < 128) : g / 32 = h / 32 := by
  have := hs.2; rw [hB, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hh] at this; exact this

/-- The warp-collective events, by instance. -/
theorem coll {g i k pc : Nat} {ke : TcKind} (hk : X.TcK (g, i) k)
    (h : X.get (g, i) = some ⟨pc, .tc ke⟩) :
    pc = collPc g k ∧ tcStatic ke = collSt L.sharedBase (P 0).col g k := by
  have hc := hk.1
  obtain ⟨hg, hi, hkk⟩ := hW.tcK hk
  obtain ⟨ev, hev, hcoll⟩ := hc
  rw [h] at hev; cases hev
  have hld := ldIdx_eq (g := g) (P g)
  have htl := tl_ge (g := g) (P g)
  rcases tc_coll hcoll with ⟨pc', grp, dst, act, he⟩ | ⟨pc', ta, vs, sh, he⟩ |
      ⟨pc', he⟩ | ⟨pc', ta, vs, sh, he⟩ | ⟨pc', he⟩ <;>
    simp only [Event.mk.injEq, Kind.tc.injEq] at he <;> obtain ⟨rfl, rfl⟩ := he
  · rcases hW.resource h with ⟨d, n, rfl, rfl, rfl⟩ | ⟨ta, n, rfl, rfl, rfl⟩
    · obtain ⟨-, -, h32, rfl, rfl, rfl⟩ := hW.talloc h
      rw [hW.get_of_lt hg hi, fullAt_head _ (by unfold hd; split_ifs <;> omega)] at h
      rcases hkk with ⟨-, -, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩ <;> try omega
      simp [headE, h32] at h
      split_ifs at h <;> simp [allocE] at h <;> simp [collPc, collSt, h32, h, tcStatic]
    obtain ⟨-, -, h32, hpos, rfl, rfl⟩ := hW.tdealloc h
    rw [hW.get_of_lt hg hi, hpos, show ldIdx g (P g) + 13 = ldIdx g (P g) + 1 + 12 by omega,
      fullAt_post] at h
    simp [postAt, h32, deallocE] at h
    rcases hkk with ⟨-, h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, rfl⟩ <;> try omega
    rw [c_eq hpre hX hW hg (by omega)]
    simp [collPc, collSt, h32, h, tcStatic]
  · obtain rfl := hW.tld_shape h
    obtain ⟨-, -, hpos, rfl, rfl⟩ := hW.tld h
    rw [hW.get_of_lt hg hi, hpos, fullAt_ld] at h
    simp [ldE] at h
    rw [c_eq hpre hX hW hg (by omega)]
    rcases hkk with ⟨-, h1, -⟩ | ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩ <;> try omega
    by_cases h32 : g < 32 <;> simp [collPc, collSt, h32, h, tcStatic]
  · obtain ⟨-, -, hpos⟩ := hW.waitLd h
    rw [hW.get_of_lt hg hi, hpos, show ldIdx g (P g) + 1 = ldIdx g (P g) + 1 + 0 from rfl,
      fullAt_post] at h
    simp [postAt, wldE] at h
    rcases hkk with ⟨-, h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩ | ⟨-, h1, -⟩ <;> try omega
    by_cases h32 : g < 32 <;> simp [collPc, collSt, h32, h, tcStatic]
  · exact (hW.no_tst h).elim
  · exact (hW.no_waitSt h).elim


/-- **The lanes of a warp agree on their warp-collective `tcgen05` events.** -/
theorem no_tcDivergent : ¬ AlignedClass.tc.Divergent L kernel X := by
  have hB := hpre.block
  rw [AlignedClass.divergent_tc_iff]
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, k, pc, pc', ke, kf, hsw, hke, hkf, hge, hgf, hne⟩
  obtain ⟨hg, -, -⟩ := hW.tcK hke
  obtain ⟨hh, -, -⟩ := hW.tcK hkf
  obtain ⟨p1, s1⟩ := coll hpre hX hW hke hge
  obtain ⟨p2, s2⟩ := coll hpre hX hW hkf hgf
  have hw := same_warp hB hsw hg hh
  simp only at hw
  have ht : taddr g (P 0).col = taddr h (P 0).col := by unfold taddr; rw [hw]
  rcases hne with hne | hne <;> apply hne
  · rw [p1, p2]; unfold collPc
    by_cases h32 : g / 32 = 0
    · rw [ite_eq_left h32, ite_eq_left (show h / 32 = 0 by omega)]
    · rw [ite_eq_right h32, ite_eq_right (show ¬ h / 32 = 0 by omega)]
  · rw [s1, s2]; unfold collSt
    by_cases h32 : g / 32 = 0
    · rw [ite_eq_left h32, ite_eq_left (show h / 32 = 0 by omega), ht]
    · rw [ite_eq_right h32, ite_eq_right (show ¬ h / 32 = 0 by omega), ht]

/-- **No lane exits before the warp-collective `tcgen05` events of the others.** -/
theorem no_tcExited : ¬ AlignedClass.tc.Exited L kernel X := by
  have hB := hpre.block
  rw [AlignedClass.exited_tc_iff]
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, k, hsw, hke, ⟨⟨pcx, hgf⟩, hcnt⟩⟩
  obtain ⟨hg, -, hkk⟩ := hW.tcK hke
  obtain ⟨hh, -, htr⟩ := trace_full hX hW hgf
  have hw := same_warp hB hsw hg hh
  simp only at hw hcnt
  rw [htr, fullE_tc] at hcnt
  split_ifs at hcnt with h32 <;> rcases hkk with ⟨h1, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h1, -, rfl⟩
    <;>
    (try split_ifs at hcnt) <;> omega

/-! ### The MMA instruction -/

omit hpre hX in
theorem no_writesUnsafe : ¬ TcMma.WritesUnsafe L X := fun hu =>
  hu fun _ _ _ hx hy => by
    have hs : ∀ e a vals sh, ¬ X.TSt e a vals sh := fun ⟨_, _⟩ _ _ _ ⟨_, h⟩ => hW.no_tst h
    have hcp : ∀ e c, ¬ X.CpIssue e c := fun ⟨_, _⟩ _ ⟨_, h⟩ => hW.no_cp h
    have hsh : ∀ e s, ¬ X.ShiftIssue e s := fun ⟨_, _⟩ _ ⟨_, h⟩ => hW.no_shift h
    replace hx := TcMma.tmemWrite_of_no_store hs hcp hsh hx
    replace hy := TcMma.tmemWrite_of_no_store hs hcp hsh hy
    exact .inl ((mma_access hW (.inl hx)).1.trans (mma_access hW (.inl hy)).1.symm)

omit hpre hX in
theorem no_readsUnsafe : ¬ TcMma.ReadsUnsafe L X := by
  intro hu
  refine hu (TcMma.readsSafe_iff.mpr ⟨?_, ?_, ?_⟩)
  · rintro ⟨g, j⟩ writer cell ⟨d, s, mask, row, col, ⟨pc, hm⟩, _⟩ _
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hW.mma hm
    cases h
  · rintro ⟨g, j⟩ writer cell ⟨d, s, acc, mask, index, b, ⟨pc, hm⟩, ha⟩ _
    obtain ⟨-, -, -, -, -, rfl, -, -⟩ := hW.mma hm
    simp [TcMma.aCell, mmaSpec] at ha
  · rintro ⟨g, j⟩ writer cell ⟨_, ⟨_, h⟩, _⟩ _
    exact (hW.no_shift h).elim

/-! ### The allocator history -/

theorem history_other {key : Nat} (hk : key ≠ 0) : X.tmemHistory key = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  exact hk (rec_shape hpre hX hW hr).1

omit hpre in
theorem alloc_rec_m {col : Nat} (h : allocReq L.sharedBase col ∈ X.tmemHistory 0) : 0 < m 0 := by
  have hev := ((hX.tmemPair.1 0).1 _ h).2.2.2.2.1 0
  simp [WarpRequest.event, allocReq] at hev
  exact (hW.talloc hev).2.1

omit hpre in
theorem dealloc_rec_m (h : deallocReq P ∈ X.tmemHistory 0) : ldIdx 0 (P 0) + 13 < m 0 := by
  have hev := ((hX.tmemPair.1 0).1 _ h).2.2.2.2.1 0
  simp [WarpRequest.event, deallocReq] at hev
  exact (hW.tdealloc hev).2.1

/-- The release names the allocated column. -/
theorem dealloc_col (h : deallocReq P ∈ X.tmemHistory 0) : (P 0).c = (P 0).col := by
  have hm := dealloc_rec_m hX hW h
  have hld := ldIdx_eq (g := 0) (P 0)
  have htl := tl_zero (P 0)
  exact c_eq hpre hX hW (g := 0) (by decide) (by omega)

/-- Replaying the recorded allocation and release completes. -/
theorem history_runs : ∀ key, ∃ s, runRequests {} (X.tmemHistory key) = .done s ∧
    (deallocReq P ∈ X.tmemHistory key → s.live = []) := by
  intro key
  by_cases hk : key = 0
  · subst hk
    rcases history_shape hpre hX hW with h | ⟨col, h⟩ | ⟨col, h⟩
    · exact ⟨{}, by rw [h]; rfl, by rw [h]; simp⟩
    · have hcol := base_room hpre hX hW (col := col) (by rw [h]; simp)
      refine ⟨{ previousColumns := some 32, nextLifetime := 1, live := [⟨0, col, 32⟩] },
        ?_, fun hd => by rw [h] at hd; simp [allocReq, deallocReq] at hd⟩
      rw [h]
      have hav : Tmem.available {} col 32 = true := by
        simp [Tmem.available]; omega
      simp [runRequests, allocReq, Tmem.perform, Tmem.validColumns, hav]
    · have hcol := base_room hpre hX hW (col := col) (by rw [h]; simp)
      have hc := dealloc_col hpre hX hW (by rw [h]; simp)
      have hm := dealloc_rec_m hX hW (by rw [h]; simp)
      have hb := alloc_base hpre hX hW (col := col) (by rw [h]; simp)
        (by have := ldIdx_eq (g := 0) (P 0); omega)
      subst hb
      refine ⟨⟨true, some 32, 1, []⟩, ?_, fun _ => rfl⟩
      rw [h]
      have hav : Tmem.available {} (P 0).col 32 = true := by
        simp [Tmem.available]; omega
      simp [runRequests, allocReq, deallocReq, Tmem.perform, Tmem.validColumns, hav, hc]
  · exact ⟨{}, by rw [history_other hpre hX hW hk]; rfl, by
      rw [history_other hpre hX hW hk]; simp⟩

theorem no_resourceUnsafe : ¬ Tmem.Pair.ResourceUnsafe L X := by
  refine Tmem.Pair.not_resourceUnsafe (fun key reason hrun => ?_) (fun key => ?_)
  · obtain ⟨s, hs, -⟩ := history_runs hpre hX hW key
    rw [hs] at hrun
    cases hrun
  · by_cases hk : key = 0
    · subst hk
      rcases history_shape hpre hX hW with h | ⟨col, h⟩ | ⟨col, h⟩ <;> rw [h] <;>
        simp [allocReq, deallocReq]
    · rw [history_other hpre hX hW hk]
      exact .nil

theorem no_releaseUnsafe : ¬ Tmem.Pair.ReleaseUnsafe L X := by
  have hT := threads_eq hpre
  rintro ⟨hexit, hdrain, hnot⟩
  apply hnot
  have hd : deallocReq P ∈ X.tmemHistory 0 := by
    rcases hexit 0 (by omega) with ⟨_, request, ho⟩ | ⟨pc, hx⟩
    · obtain ⟨i, s, targets, _, hi, _⟩ := hX.clc.canceled_has_issue ho
      exact (hW.no_clc hi).elim
    · rw [List.getLast?_eq_getElem?] at hx
      obtain ⟨-, hm, htr⟩ := trace_full hX hW hx
      have hld := ldIdx_eq (g := 0) (P 0)
      have htl := tl_zero (P 0)
      rw [fullE_length] at hm
      have hget : X.get (0, ldIdx 0 (P 0) + 13) = some (deallocE (P 0).c) := by
        rw [hW.get_of_lt (by decide) (by simp at hm; omega),
          show ldIdx 0 (P 0) + 13 = ldIdx 0 (P 0) + 1 + 12 by omega, fullAt_post]
        simp [postAt, deallocE]
      obtain ⟨ws, ⟨key, r, hr, -, rfl⟩ | ⟨q, hq, -⟩, w, hw, hp⟩ := hdrain _ _ _ _ _ hget
      · rw [List.mem_singleton.mp hw] at hp
        obtain ⟨rfl, hshape⟩ := rec_shape hpre hX hW hr
        rcases hshape with ⟨_, rfl⟩ | rfl
        · exfalso
          obtain ⟨lane, he⟩ := hp
          simp [WarpRequest.event, allocReq] at he
        · exact hr
      · rw [pairing_nil hX hW] at hq
        cases hq
  intro key s hs
  obtain ⟨s', hs', hl⟩ := history_runs hpre hX hW key
  rw [hs] at hs'
  cases hs'
  by_cases hk : key = 0
  · subst hk; exact hl hd
  · rw [history_other hpre hX hW hk] at hs
    simp [runRequests] at hs
    subst hs
    rfl


end
end PTX.Kernels.TcGemm.Proof

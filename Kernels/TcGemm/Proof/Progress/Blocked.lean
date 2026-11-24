-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Progress.Steps
public import Lemmas.Step.TmemPair
public import Lemmas.Step.CtaBarNamed
import Lemmas.Tmem.AllocResult

@[expose] public section

/-! # `tc_gemm` progress: a thread that its last event blocks

A pending thread that is not released made, as its last event, an arrival on a barrier, a
warp-collective `tcgen05` event some lane of its warp has not made, or an allocator operation
whose return is not ready (`blocked_steps`).

* At an arrival with ordinal `o` (`bar_blocked`): a thread without its arrival of that ordinal is
  pending and earlier; if some thread passed its arrival, the generation is released
  (`released_of_passed`), and so is the blocked arrival, a contradiction; otherwise every thread's
  last event is its arrival, the barrier's history completes the generation
  (`NamedBar.named_finish`) and the released thread steps there (`released_steps`).
* A lane of the warp without the collective event of the same ordinal is pending and earlier
  (`coll_lag`): it has not made its allocation (time 1), load, wait or deallocation.
* An uncovered allocation or deallocation whose warp has all made it is performed by the
  allocator (`alloc_entry`, `dealloc_entry`, `Step.warp_entry_counted`): before the allocation
  the allocator's history is empty, and before the deallocation it holds the allocation of the
  column the deallocation frees.
* A nonleader whose allocation is covered either observes the result store or can advance
  the leader to that store. The leader's own release has no result-store need.

An uncovered allocator operation is its thread's last event, a pending thread ranked below it
(`tmem_steps`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy Tmem.Pair CtaBarrier

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

/-- Every lane of the warp of `g` made its `k`-th warp-collective `tcgen05` event: the warp
needs of such an event (`tcNeeds`). -/
def TcWarpDone (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∀ h ∈ warpLanes L g, ∃ j, X.TcK (h, j) k

/-! ### Uncovered allocator operations -/

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

omit hX hW in
/-- Lane `t` of a thread of warp 0 is thread `t`. -/
theorem warpThread_zero {g : Nat} (hg : g / 32 = 0) (t : Nat) : Step.warpThread L g t = t := by
  have hB := hpre.block
  simp only [Step.warpThread, hB]
  rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  simp

omit hX hW in
/-- Threads of warp 0 are of one warp. -/
theorem sameWarp_zero {g h : Nat} (hg : g / 32 = 0) (hh : h / 32 = 0) : SameWarp L g h := by
  have hB := hpre.block
  have hT := threads_eq hpre
  refine ⟨⟨by omega, by omega, ?_⟩, ?_⟩ <;> rw [hB] <;>
    simp [Nat.div_eq_of_lt (show g < 128 by omega), Nat.div_eq_of_lt (show h < 128 by omega),
      Nat.mod_eq_of_lt (show g < 128 by omega), Nat.mod_eq_of_lt (show h < 128 by omega), hg, hh]

omit hX hW in
/-- A lane of the warp of a thread is a thread of the launch. -/
theorem lt_of_mem_warpLanes {g h : Nat} (hg : g < 128) (hm : h ∈ warpLanes L g) : h < 128 := by
  have hB := hpre.block
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  rw [List.mem_range] at hl
  simp only [warpSize, warpLane, laneOf, hB, Nat.mod_eq_of_lt hg] at hl ⊢
  omega

omit hX hW in
/-- The lanes of the warp of a thread are the threads of its warp. -/
theorem mem_warpLanes_iff {g h : Nat} (hg : g < 128) :
    h ∈ warpLanes L g ↔ h < 128 ∧ h / 32 = g / 32 := by
  have hT := threads_eq hpre
  constructor
  · intro hm
    have hh := lt_of_mem_warpLanes hpre hg hm
    exact ⟨hh, warp_eq hpre.block (sameWarp_of_mem_warpLanes hm (by omega) (by omega)) hh hg⟩
  · rintro ⟨hh, hw⟩
    have hB := hpre.block
    refine mem_warpLanes_of_sameWarp ⟨⟨by omega, by omega, ?_⟩, ?_⟩ <;> rw [hB] <;>
      simp [Nat.div_eq_of_lt hh, Nat.div_eq_of_lt hg, Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hg, hw]

/-- No allocation of this kernel reuses a released column: the only release is recorded after
the only allocation. -/
theorem no_reuseRelease (e : EvId) (j : Nat) :
    ¬ ReuseRelease L X e j := by
  rintro ⟨i, r, d, n, base, b', n', hi, -, hra, hj, hji, hda, -⟩
  obtain ⟨hk, -⟩ := rec_shape hpre hX hW (List.mem_of_getElem? hi)
  rw [hk] at hi
  rcases history_shape hpre hX hW with hh | ⟨col, hh⟩ | ⟨col, hh⟩ <;> rw [hh] at hi <;>
    rcases i with _ | _ | i <;> simp at hi
  all_goals first
    | omega
    | (subst hi; simp [deallocReq] at hra)

/-- **An uncovered allocation that every lane of warp 0 made is performed**: a counted
extension. -/
theorem alloc_entry {g : Nat} (hg : g / 32 = 0) (hdone : TcWarpDone L X g 0)
    (hnc : ¬ Covered L X (g, 0)) :
    ∃ Y, Consistent L kernel [] mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hT := threads_eq hpre
  have hB := hpre.block
  have hg' : g < L.threads := by omega
  -- every lane made the allocation, as its last event, uncovered
  have hlane : ∀ t : Fin 32, X.get (t.val, 0) = some (allocE L.sharedBase) ∧
      ¬ Covered L X (t.val, 0) ∧ (X.tr t.val).length = 1 := by
    intro t
    have ht32 : t.val / 32 = 0 := by omega
    obtain ⟨j, hk⟩ := hdone t.val (mem_warpLanes_of_sameWarp (sameWarp_zero hpre ht32 hg))
    obtain ⟨-, hj, hc⟩ := hW.tcK hk
    have hj0 : j = 0 := by
      rcases hc with ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, -, h1⟩
      · exact h1
      · simp only [ht32, ↓reduceIte] at h1; omega
      · simp only [ht32, ↓reduceIte] at h1; omega
      · omega
    subst hj0
    have hget := (talloc_at hW ht32 hj).1
    have hnc' : ¬ Covered L X (t.val, 0) := by
      rintro ⟨ws, ⟨cta, r, hr, -, rfl⟩ | ⟨q, hq, -⟩, w, hw, l, hl⟩
      · rw [List.mem_singleton.mp hw] at hl
        obtain ⟨rfl, ⟨c, rfl⟩ | rfl⟩ := rec_shape hpre hX hW hr
        · exact hnc ⟨[_], .inl ⟨0, _, hr, rfl, rfl⟩, _, List.mem_singleton_self _, ⟨g, by omega⟩,
            by simp only [allocReq, WarpRequest.event, Nat.zero_mul, Nat.zero_add]⟩
        · simp only [deallocReq, WarpRequest.event, Prod.mk.injEq] at hl
          omega
      · rw [pairing_nil hX hW] at hq
        cases hq
    have hlast := Step.pending_is_last hX ⟨_, _, _, _, hget, trivial⟩ hnc'
    exact ⟨hget, hnc', by simp only at hlast; omega⟩
  obtain ⟨-, h0nc, h0len⟩ : _ ∧ ¬ Covered L X (0, 0) ∧ (X.tr 0).length = 1 :=
    hlane ⟨0, by decide⟩
  obtain ⟨Y, hY, hle, -, hsz⟩ := Step.warp_entry_counted hX hg' (by rw [hB])
    (pc := Flow.tmemAlloc_0)
    (dst := some (tslot L.sharedBase)) (action := .alloc 32 0)
    (fun t => by rw [warpThread_zero hpre hg, (hlane t).2.2]; exact (hlane t).1)
    ⟨0, fun t => by rw [warpThread_zero hpre hg, (hlane t).2.2]; exact (talloc_at hW (by omega)
      (by rw [← len_eq hpre hX hW (by omega), (hlane t).2.2]; omega)).2⟩
    (fun t => by rw [warpThread_zero hpre hg, (hlane t).2.2]; exact (hlane t).2.1)
    (fun w hw w' grp _ hbef i _ => by
      rw [List.mem_singleton.mp hw] at hbef
      have := hbef.2.2 0
      simp only [Step.ownerRecord, Step.warpRequest, warpThread_zero hpre hg, Fin.val_zero,
        h0len] at this
      omega)
    (by
      rw [show g / L.block = 0 by rw [hB]; omega,
        history_nil hpre hX hW h0nc 0]
      simp [runRequests, Step.ownerRecord, Tmem.perform, Tmem.validColumns, Tmem.available])
    (fun _ ha => by cases ha)
  exact ⟨Y, hY, hle, hsz⟩

/-- **An uncovered deallocation that every lane of warp 0 made is performed**: a counted
extension. -/
theorem dealloc_entry {g : Nat} (hg : g / 32 = 0) (hdone : TcWarpDone L X g 3)
    (hnc : ¬ Covered L X (g, ldIdx g (P g) + 13)) :
    ∃ Y, Consistent L kernel [] mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hT := threads_eq hpre
  have hB := hpre.block
  have hg' : g < L.threads := by omega
  have h0d : ∀ h, h < 128 → ldIdx h (P h) + 13 < m h → hd h + 1 < m h := fun h _ hm => by
    have := ldIdx_eq (g := h) (P h); have := tl_ge (g := h) (P h); omega
  -- every lane made the deallocation, as its last event, uncovered
  have hlane : ∀ t : Fin 32, X.get (t.val, ldIdx t.val (P t.val) + 13) =
      some (deallocE (P 0).col) ∧ ¬ Covered L X (t.val, ldIdx t.val (P t.val) + 13) ∧
      (X.tr t.val).length = ldIdx t.val (P t.val) + 14 := by
    intro t
    have ht32 : t.val / 32 = 0 := by omega
    obtain ⟨j, hk⟩ := hdone t.val (mem_warpLanes_of_sameWarp (sameWarp_zero hpre ht32 hg))
    obtain ⟨-, hj, hc⟩ := hW.tcK hk
    have hj0 : j = ldIdx t.val (P t.val) + 13 := by
      rcases hc with ⟨-, -, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1, -⟩
      · omega
      · simp only [ht32, ↓reduceIte] at h1; omega
      · simp only [ht32, ↓reduceIte] at h1; omega
      · exact h1
    subst hj0
    have hget : X.get (t.val, ldIdx t.val (P t.val) + 13) = some (deallocE (P 0).col) := by
      rw [hW.get_of_lt (by omega) hj, show ldIdx t.val (P t.val) + 13 =
        ldIdx t.val (P t.val) + 1 + 12 by omega, fullAt_post,
        c_eq hpre hX hW (by omega) (h0d _ (by omega) hj)]
      simp [postAt, ht32]
    have hnc' : ¬ Covered L X (t.val, ldIdx t.val (P t.val) + 13) := by
      rintro ⟨ws, ⟨cta, r, hr, -, rfl⟩ | ⟨q, hq, -⟩, w, hw, l, hl⟩
      · rw [List.mem_singleton.mp hw] at hl
        obtain ⟨rfl, ⟨c, rfl⟩ | rfl⟩ := rec_shape hpre hX hW hr
        · simp only [allocReq, WarpRequest.event, Prod.mk.injEq] at hl
          omega
        · exact hnc ⟨[_], .inl ⟨0, _, hr, rfl, rfl⟩, _, List.mem_singleton_self _, ⟨g, by omega⟩,
            by simp only [deallocReq, WarpRequest.event, Nat.zero_mul, Nat.zero_add]⟩
      · rw [pairing_nil hX hW] at hq
        cases hq
    have hlast := Step.pending_is_last hX ⟨_, _, _, _, hget, .inl rfl⟩ hnc'
    exact ⟨hget, hnc', by simp only at hlast; omega⟩
  obtain ⟨-, -, h0len⟩ : _ ∧ _ ∧ (X.tr 0).length = ldIdx 0 (P 0) + 14 := hlane ⟨0, by decide⟩
  have hm0 : ldIdx 0 (P 0) + 13 < m 0 := by
    rw [len_eq hpre hX hW (by decide)] at h0len
    omega
  have hrec := alloc_recorded hpre hX hW (P := P) (m := m) (by
    have := ldIdx_eq (g := 0) (P 0); have := tl_zero (P 0); omega)
  have hroom := col_ok hpre hX hW (P := P) (m := m) (by
    have := ldIdx_eq (g := 0) (P 0); have := tl_zero (P 0); omega)
  have hhist : X.tmemHistory 0 = [allocReq L.sharedBase (P 0).col] := by
    rcases history_shape hpre hX hW with hh | ⟨col, hh⟩ | ⟨col, hh⟩
    · rw [hh] at hrec; cases hrec
    · rw [hh] at hrec ⊢
      simp only [List.mem_singleton, allocReq, Requests.mk.injEq, Tmem.Action.alloc.injEq,
        true_and] at hrec
      rw [hrec]
    · exfalso
      apply hnc
      exact ⟨[_], .inl ⟨0, deallocReq P, by rw [hh]; simp, rfl, rfl⟩, _,
        List.mem_singleton_self _, ⟨⟨g, by omega⟩, by
          simp only [deallocReq, WarpRequest.event, Nat.zero_mul, Nat.zero_add]⟩⟩
  obtain ⟨Y, hY, hle, -, hsz⟩ := Step.warp_entry_counted hX hg' (by rw [hB])
    (pc := Flow.tmemDealloc_0) (dst := none) (action := .dealloc (P 0).col 32)
    (fun t => by
      rw [warpThread_zero hpre hg, (hlane t).2.2, show ldIdx t.val (P t.val) + 14 - 1 =
        ldIdx t.val (P t.val) + 13 by omega]
      exact (hlane t).1)
    ⟨3, fun t => by
      rw [warpThread_zero hpre hg, (hlane t).2.2, show ldIdx t.val (P t.val) + 14 - 1 =
        ldIdx t.val (P t.val) + 13 by omega]
      exact tcK_dealloc hW (by omega) (by omega) (by
        have := (hlane t).2.2
        rw [len_eq hpre hX hW (by omega)] at this
        omega)⟩
    (fun t => by
      rw [warpThread_zero hpre hg, (hlane t).2.2, show ldIdx t.val (P t.val) + 14 - 1 =
        ldIdx t.val (P t.val) + 13 by omega]
      exact (hlane t).2.1)
    (fun w hw w' grp hv hbef i hi => by
      rw [List.mem_singleton.mp hw] at hbef
      obtain ⟨-, rfl | rfl⟩ := own_shape hpre hW hv
      · exact ⟨[_], .inl ⟨0, _, hrec, rfl, rfl⟩, _, List.mem_singleton_self _, hi⟩
      · have := hbef.2.2 0
        simp only [Step.ownerRecord, Step.warpRequest, warpThread_zero hpre hg, Fin.val_zero,
          h0len, deallocReq] at this
        omega)
    (by
      rw [show g / L.block = 0 by rw [hB]; omega, hhist]
      simp [runRequests, allocReq, Step.ownerRecord, Tmem.perform, Tmem.validColumns,
        Tmem.available, hroom])
    (fun _ ha => by cases ha)
  exact ⟨Y, hY, hle, hsz⟩

end


/-! ### Blocked threads -/

section
variable (hpre : Pre L A B D a b mem0) (ht : ThreadFacts L A B D X)
  (hmax : Maximal L kernel [] mem0 X) (hW : Wit A B D L.sharedBase X P m u)
include hpre ht hmax hW

omit ht in
/-- **A lane of the warp lags behind a warp-collective event**: some lane of the warp has not
made the event of the same ordinal; it is pending and earlier. -/
theorem coll_lag {g k : Nat} (hg : g < 128) (hnd : ¬ TcWarpDone L X g k)
    (hlag : ∀ h < 128, h / 32 = g / 32 → (¬ ∃ j, X.TcK (h, j) k) →
      m h ≤ ldIdx h (P h) + 13 ∧ timeOf L A B D X h < timeOf L A B D X g) :
    Descent.Steps L kernel [] mem0 (Descent.Obl L) (rank L A B D) X (.thread g) := by
  have hT := threads_eq hpre
  simp only [TcWarpDone, not_forall] at hnd
  obtain ⟨h, hm, hno⟩ := hnd
  obtain ⟨hh', hw⟩ := (mem_warpLanes_iff hpre hg).mp hm
  obtain ⟨hm, hlt⟩ := hlag h hh' hw hno
  exact .inr ⟨X, .thread h, hmax, pending_of hpre hmax.1 hW hh' hm, hlt⟩

/-- **A thread blocked at a barrier arrival steps.** Its arrival with ordinal `o` is at position
`pos g`, its last event; every thread's arrival of that ordinal is at `pos h`. -/
theorem bar_blocked (hC : ∀ g < L.threads, (code L A B D g).Sound)
    (hT : ∀ Y, Consistent L kernel [] mem0 Y → ThreadFacts L A B D Y)
    (hS : SafeGoal kernel [] L mem0) {g : Nat} (hg : g < 128) (hp : Frame.Pending L X g)
    (hnr : ¬ Step.Released L X g) (pos : Nat → Nat) (o : Nat)
    (hlast : (X.tr g).length = pos g + 1)
    (hbar : ∀ h < 128, pos h < m h →
      ∃ pc, X.IsBarrier (h, pos h) 0 none pc ∧ ((X.tr h).take (pos h)).countP Execution.isBar = o)
    (hpend : ∀ h < 128, pos h + 1 ≤ ldIdx h (P h) + 13)
    (hlag : ∀ h < 128, m h ≤ pos h → timeOf L A B D X h < timeOf L A B D X g) :
    Descent.Steps L kernel [] mem0 (Descent.Obl L) (rank L A B D) X (.thread g) := by
  have hX := hmax.1
  have hTh := threads_eq hpre
  have hB := hpre.block
  have hproto := protocol hpre hX hW
  by_cases hl : ∃ h < 128, m h ≤ pos h
  · obtain ⟨h, hh, hm⟩ := hl
    exact .inr ⟨X, .thread h, hmax, pending_of hpre hX hW hh (by have := hpend h hh; omega),
      hlag h hh hm⟩
  push Not at hl
  have hmg : m g = pos g + 1 := by rw [← len_eq hpre hX hW hg, hlast]
  obtain ⟨pcg, hbg, hog⟩ := hbar g hg (hl g hg)
  have hlast' : (X.tr g).length - 1 = pos g := by omega
  -- the barrier condition of the blocked arrival, from its generation's release
  have hrel_of : ∀ (Y : Execution), Y.tr = X.tr → Consistent L kernel [] mem0 Y →
      ThreadFacts L A B D Y → (∀ id count pc, 0 < (Y.tr g).length →
        Y.IsBarrier (g, (Y.tr g).length - 1) id count pc →
        ∃ key, CtaBarK L Y (g, (Y.tr g).length - 1) key ∧ CtaBarDone L Y (g / L.block) key) →
      Step.Released L Y g := by
    intro Y htr hY htY hb
    obtain ⟨P', m', u', hW'⟩ := wit hpre htY hY
    have hget : Y.get (g, (Y.tr g).length - 1) = X.get (g, (X.tr g).length - 1) := by
      simp only [Execution.get, htr]
    refine hW'.tcBulk.released (fun pc id count mode h => ?_) (fun pc k h hk => ?_)
      (fun pc t h _ => ?_)
    · cases mode
      case arrive => exact (hY.noBarArrive Fact.out _ _ _ _ h).elim
      obtain ⟨key, hk, hd⟩ := hb id count pc (by rw [htr]; omega) h
      exact NamedBar.ready_of_released hY.ctaBar h hk hd
    · rw [hget, hlast', hbg] at h
      cases h
      rcases hk with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    · rw [hget, hlast', hbg] at h
      cases h
  by_cases hpass : ∃ h < 128, pos h + 1 < m h
  · -- the generation is released: so is the blocked arrival
    obtain ⟨h, hh, hm⟩ := hpass
    obtain ⟨pch, hbh, hoh⟩ := hbar h hh (by omega)
    have hd := released_of_passed hpre hX hW hbh (by simp only; rw [len_eq hpre hX hW hh]; omega)
    simp only at hd
    rw [hoh] at hd
    refine absurd (hrel_of X rfl hX ht fun id count pc _ hb => ⟨0 + 16 * o, ?_, ?_⟩) hnr
    · rw [hlast']
      refine NamedBar.reached_key_of_release hX (n := 4) (by decide) (target_none hpre)
        (p := Finset.range 4) (by decide) hbg (by omega) (bar_src hpre hW hbg).2.2.2
        (by rw [barId_eq hpre hX hW]; exact hog) (by rw [cta_zero hpre hg]; exact hd)
        (fun _ _ r hr => by
          rw [show (g, pos g).1 / L.block = 0 from cta_zero hpre hg] at hr
          exact hproto r (List.mem_of_mem_take hr))
        (Finset.card_range 4) (warps_bound hpre)
    · simp only [CtaBarDone, cta_zero hpre hg]
      simpa using hd
  push Not at hpass
  -- every thread's last event is its arrival: the history completes the generation
  have hall : ∀ h < 128, m h = pos h + 1 := fun h hh => le_antisymm (hpass h hh) (hl h hh)
  have hP : NamedBar.Part L X 0 none 0 (Finset.range 4) := by
    refine ⟨fun e pc cnt he _ => ?_, fun y hy _ j pc hx => ?_⟩
    · obtain ⟨-, hc, -, hw⟩ := bar_src hpre hW he
      exact ⟨hw, hc⟩
    · have hy' : y < 128 := by rw [hB] at hy; omega
      obtain ⟨-, hj, hpos⟩ := hW.exit hx
      have := hall y hy'
      have := hpend y hy'
      split_ifs at hpos <;> omega
  obtain ⟨Y, hmaxY, hle, hsz, htr, hdone, hkeys⟩ := NamedBar.named_finish hmax
    (show 0 < L.grid by rw [hpre.grid]; decide) (n := 4) (by decide) (target_none hpre)
    (by decide) (Finset.card_range 4) (warps_bound hpre) hP (G := o) (fun g' hg' _ => by
      have hg'' : g' < 128 := by omega
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [len_eq hpre hX hW hg'', hall g' hg'', Nat.add_sub_cancel]
      obtain ⟨pc, hb, hc⟩ := hbar g' hg'' (by rw [hall g' hg'']; omega)
      exact ⟨pc, hb, by rw [barId_eq hpre hX hW]; exact hc⟩)
    (fun _ _ ha => by cases ha)
  have htY := hT Y hmaxY.1
  obtain ⟨P', m', u', hW'⟩ := wit hpre htY hmaxY.1
  have hpY : Frame.Pending L Y g := ⟨hp.1, not_canceled hW' hmaxY.1, by rw [htr]; exact hp.2.2⟩
  have hrelY : Step.Released L Y g := hrel_of Y htr hmaxY.1 htY fun id count pc _ _ => by
    refine ⟨0 + 16 * o, ?_, by rw [cta_zero hpre hg]; exact hdone⟩
    have := hkeys g (by omega) (by rw [Finset.mem_range]; omega)
    simpa [htr] using this
  rcases released_steps hpre htY (hS.2 Y hmaxY.1) hmaxY hW' hC hpY hrelY with
    ⟨Z, hZ, hYZ, hlt⟩ | ⟨Z, o', hZ, hobl, hlt⟩
  · exact .inl ⟨Z, hZ, Execution.le_trans hle hYZ, by omega⟩
  · refine .inr ⟨Z, o', hZ, hobl, ?_⟩
    simp only [rank, timeOf_congr htr] at hlt ⊢
    exact hlt

omit ht in
/-- A thread is released after a warp-collective event that its warp completed, when its return
is ready if it is an allocator operation. -/
theorem released_of_done {g k : Nat} {e : Event} (he : X.get (g, (X.tr g).length - 1) = some e)
    (hk : X.TcK (g, (X.tr g).length - 1) k) (hd : TcWarpDone L X g k)
    (hrr : ∀ pc grp dst act, e = ⟨pc, .tc (.resource grp dst act)⟩ →
      ReturnReady L X (g, (X.tr g).length - 1))
    (hResult : ∀ pc group dst n, e = ⟨pc, .tc (.resource group dst (.alloc n))⟩ →
      laneOf L g ≠ 0 → ∃ store dest, AllocResult L X store (g, (X.tr g).length - 1) dest) :
    Step.Released L X g := by
  have htc : ∀ n ∈ tcNeeds L X (g, (X.tr g).length - 1), match n with
      | .node fills => ∃ x, X.RefPresent x ∧ fills x
      | .cond holds => holds := by
    intro n hm
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm
    obtain ⟨j, hj⟩ := hd h hh
    exact ⟨.thread (h, j), hj.1.imp fun _ h => h.1, j, rfl, by rw [hk.2]; exact hj⟩
  obtain ⟨⟨ev, hev, hc⟩, -⟩ := hk
  refine ⟨fun pc kd hq _ n hn => ?_⟩
  rw [hq] at hev he
  cases hev
  simp only [Needs, hq] at hn
  cases kd with
  | tc t =>
    cases t <;> simp only [isTcColl] at hc <;> simp only [KindNeeds] at hn
    all_goals try first
      | exact htc n hn
      | exact absurd hn List.not_mem_nil
    rename_i group dst request hResume
    unfold resourceNeeds at hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨hperf, hcov⟩ := hrr _ _ _ _ (Option.some.inj he).symm
      rcases hW.resource hq with ⟨d, n', rfl, rfl, rfl⟩ | ⟨ta, n', rfl, rfl, rfl⟩ <;>
        simp only [List.mem_append, List.mem_cons] at hn <;>
        rcases hn with hn | rfl | hn
      all_goals try first
        | exact htc n hn
        | exact hperf
      all_goals
        unfold needsIf at hn
        split_ifs at hn with hmw
        swap
        · simp at hn
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hn
        rcases hn with rfl | hn
        · exact hcov hmw
      all_goals try exact absurd hn List.not_mem_nil
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hn
      split_ifs at hj with hre
      · exact (no_reuseRelease hpre hmax.1 hW _ _ hre).elim
      · simp at hj
    · obtain rfl := allocResultNeeds_node L hn
      cases request
      case alloc =>
        by_cases hLane : laneOf L g = 0
        · simp [allocResultNeeds, hLane] at hn
        · obtain ⟨store, dest, hstore⟩ :=
            hResult _ group dst _ (Option.some.inj he).symm hLane
          obtain ⟨_, pc, hget⟩ := hstore.writes
          exact ⟨.thread store, ⟨⟨pc, _⟩, hget⟩, dest, hstore⟩
      all_goals simp [allocResultNeeds] at hn
  | _ => simp [isTcColl] at hc

omit hpre ht in
/-- A covered allocator operation's return is ready. -/
theorem returnReady_of_covered {i : EvId} (hc : Covered L X i) : ReturnReady L X i := by
  refine ⟨?_, fun _ => hc⟩
  obtain ⟨ws, hcomp, w, hw, hp⟩ := hc
  rcases hcomp with ⟨cta, r, hr, -, rfl⟩ | ⟨q, hq, -⟩
  · rw [List.mem_singleton.mp hw] at hp
    exact ⟨cta, r, hr, hp⟩
  · rw [pairing_nil hmax.1 hW] at hq
    cases hq

omit ht in
private theorem covered_alloc_owner {g : Nat}
    (he : X.get (g, 0) = some (allocE L.sharedBase)) (hc : Covered L X (g, 0)) :
    (allocReq L.sharedBase 0).own.Valid L X .one ∧
      Participates L (allocReq L.sharedBase 0).own (g, 0) ∧ Covered L X (0, 0) := by
  obtain ⟨ws, hcomp, w, hw, hp⟩ := hc
  obtain ⟨grp, hvalid⟩ := Completed.valid hmax.1.tmemPair hcomp hw
  obtain ⟨rfl, halloc | hdealloc⟩ := own_shape hpre hW hvalid
  · subst w
    exact ⟨hvalid, hp, ws, hcomp, _, hw, 0, by simp [allocReq, WarpRequest.event]⟩
  · obtain ⟨lane, hLane⟩ := hp
    have hget := hvalid.2.2.1 lane
    rw [hLane, he] at hget
    simp [allocE, hdealloc, deallocReq] at hget

/-- **A pending thread that its last event blocks steps.** -/
theorem blocked_steps (hC : ∀ g < L.threads, (code L A B D g).Sound)
    (hT : ∀ Y, Consistent L kernel [] mem0 Y → ThreadFacts L A B D Y)
    (hS : SafeGoal kernel [] L mem0) {g : Nat} (hp : Frame.Pending L X g)
    (hnr : ¬ Step.Released L X g) :
    Descent.Steps L kernel [] mem0 (Descent.Obl L) (rank L A B D) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hTh := threads_eq hpre
  have hg128 : g < 128 := by omega
  have hub : ¬ HasUb X := fun h => hS.2 X hX (.inl h)
  have hlenm := len_eq hpre hX hW hg128
  have hlen0 : 0 < (X.tr g).length := by
    by_contra h0
    exact hnr (released_of_site ht hX hub hW hg fun _ _ h => absurd h h0)
  obtain ⟨d', e, hd', he, hev, hnext⟩ := last_info ht hX hub hg hlen0
  have hb : d'.site.blocks = true := by
    by_contra hb
    refine hnr (released_of_site ht hX hub hW hg fun d0 e0 _ hd0 _ _ => ?_)
    rw [hd'] at hd0
    obtain rfl := Option.some.inj (Option.some.inj hd0)
    simpa using hb
  have hj : (X.tr g).length - 1 < m g := by omega
  obtain ⟨site, c, vals⟩ := d'
  cases site with
  | bar0 z =>
    simp only [SiteEvent] at hev
    subst hev
    have htime : timeOf L A B D X g = 10 := timeOf_of (d := ⟨.load z, c, vals⟩) hnext
    have hpos : (X.tr g).length = hd g := by
      obtain ⟨-, -, -, hp'⟩ := hW.bar he
      rcases hp' with h | h
      · omega
      · exfalso
        have := hW.get_of_lt hg128 hj
        rw [he, h, show ldIdx g (P g) + 11 = ldIdx g (P g) + 1 + 10 by omega, fullAt_post] at this
        simp [postAt, bar0E, bar1E] at this
    refine bar_blocked hpre ht hmax hW hC hT hS hg128 hp hnr (fun h => hd h - 1) 0
      (by have := hd_pos (g := g); omega) (fun h hh hm => ?_) (fun h _ => ?_) (fun h hh hm => ?_)
    · have hb' : X.IsBarrier (h, hd h - 1) 0 none Flow.bar_0 := by
        show X.get _ = _
        rw [hW.get_of_lt hh hm, fullAt_bar0]
        rfl
      refine ⟨_, hb', ?_⟩
      have kh := hW.barK (k := ((X.tr h).take (hd h - 1)).countP Execution.isBar) ⟨⟨0, _, hb'⟩, rfl⟩
      have := ldIdx_eq (g := h) (P h)
      have := tl_ge (g := h) (P h)
      rcases kh.2.2 with ⟨-, h1⟩ | ⟨h1, -⟩ <;> omega
    · have := hd_pos (g := h); have := ldIdx_eq (g := h) (P h); have := tl_ge (g := h) (P h)
      omega
    · have := time_le_9 hpre ht hW hh (by have := hd_pos (g := h); omega)
      omega
  | bar1 =>
    simp only [SiteEvent] at hev
    subst hev
    have htime : timeOf L A B D X g = 28 := timeOf_of (d := ⟨.fence2, c, vals⟩) hnext
    have hpos : (X.tr g).length = ldIdx g (P g) + 12 := by
      obtain ⟨-, -, -, hp'⟩ := hW.bar he
      rcases hp' with h | h
      · exfalso
        have := hW.get_of_lt hg128 hj
        rw [he, show (X.tr g).length - 1 = hd g - 1 by omega, fullAt_bar0] at this
        simp [bar0E, bar1E] at this
      · omega
    refine bar_blocked hpre ht hmax hW hC hT hS hg128 hp hnr (fun h => ldIdx h (P h) + 11) 1
      (by omega) (fun h hh hm => ?_) (fun h _ => by omega) (fun h hh hm => ?_)
    · have hb' : X.IsBarrier (h, ldIdx h (P h) + 11) 0 none Flow.bar_1 := by
        show X.get _ = _
        rw [hW.get_of_lt hh hm, show ldIdx h (P h) + 11 = ldIdx h (P h) + 1 + 10 by omega,
          fullAt_post]
        rfl
      refine ⟨_, hb', ?_⟩
      have kh := hW.barK (k := ((X.tr h).take (ldIdx h (P h) + 11)).countP Execution.isBar)
        ⟨⟨0, _, hb'⟩, rfl⟩
      have := ldIdx_eq (g := h) (P h)
      have := tl_ge (g := h) (P h)
      rcases kh.2.2 with ⟨h1, -⟩ | ⟨-, h1⟩ <;> omega
    · have := time_le_27 hpre ht hW hh hm
      omega
  | alloc =>
    simp only [SiteEvent] at hev
    subst hev
    obtain ⟨-, -, h32, hj0, -, -⟩ := hW.talloc he
    have htime : 2 ≤ timeOf L A B D X g := by
      rw [timeOf_of (d := ⟨if g = 0 then .allocSt else .bar0 false, c, vals⟩) hnext]
      split <;> simp [Site.time]
    have htk : X.TcK (g, (X.tr g).length - 1) 0 := by
      rw [hj0]
      exact (talloc_at hW h32 (by omega)).2
    by_cases hdn : TcWarpDone L X g 0
    · by_cases hcov : Covered L X (g, 0)
      · have he0 : X.get (g, 0) = some (allocE L.sharedBase) :=
          (talloc_at hW h32 (by omega)).1
        obtain ⟨howner, hpart, hcov0⟩ := covered_alloc_owner hpre hmax hW he0 hcov
        by_cases hpub : 1 < m 0
        · have hstore := tslot_at hW hpub
          obtain ⟨lane, hLane⟩ := hpart
          have hres := AllocResult.of_warpRequest (bytes :=
            (Value.bits 32 (BitVec.ofNat 64 (P 0).col)).toBytes) howner rfl rfl rfl rfl (by
              simpa [allocReq, WarpRequest.event, tslotE] using hstore) lane
          rw [hLane] at hres
          have hresult : AllocResult L X (0, 1) (g, 0) (tslot L.sharedBase) := by
            simpa [allocReq, WarpRequest.event] using hres
          exact (hnr (released_of_done hpre hmax hW he htk hdn
            (fun _ _ _ _ _ => by rw [hj0]; exact returnReady_of_covered hmax hW hcov)
            (fun _ _ _ _ _ _ => by rw [hj0]; exact ⟨(0, 1), tslot L.sharedBase, hresult⟩))).elim
        · have hget0 : X.get (0, 0) = some (allocE L.sharedBase) := by
            simpa [allocReq, WarpRequest.event, allocE] using howner.2.2.1 0
          have hlen' : 0 < (X.tr 0).length := PTX.len_of_get hget0
          have hm0 := len_eq hpre hX hW (g := 0) (by decide)
          have hlen1 : (X.tr 0).length = 1 := by omega
          have hlast0 : X.get (0, (X.tr 0).length - 1) = some (allocE L.sharedBase) := by
            rw [hlen1]; exact hget0
          have htk0 : X.TcK (0, (X.tr 0).length - 1) 0 := by
            rw [hlen1]; exact (talloc_at hW (g := 0) rfl (by omega)).2
          have hdn0 : TcWarpDone L X 0 0 := by
            intro h hh
            obtain ⟨hlt, hw⟩ := (mem_warpLanes_iff hpre (g := 0) (by decide)).1 hh
            exact hdn _ ((mem_warpLanes_iff hpre hg128).2 ⟨hlt, hw.trans h32.symm⟩)
          have hp0 : Frame.Pending L X 0 := by
            refine ⟨by omega, not_canceled hW hX, fun pc hlast => ?_⟩
            rw [List.getLast?_eq_getElem?] at hlast
            change X.get (0, (X.tr 0).length - 1) = _ at hlast
            rw [hlast0] at hlast
            cases hlast
          have hrel0 := released_of_done hpre hmax hW hlast0 htk0 hdn0
            (fun _ _ _ _ _ => by
              rw [hlen1]; exact returnReady_of_covered hmax hW hcov0)
            (fun _ _ _ _ _ h => (h (by simp [laneOf])).elim)
          have htime0 : timeOf L A B D X 0 = 2 := by
            have hs : stateAt L A B D X 0 (X.tr 0).length =
                some (some ⟨.allocSt, 0, []⟩) := by
              rw [hlen1]
              change Frame.stateAt (code L A B D) X 0 (0 + 1) = _
              rw [Frame.stateAt_succ (C := code L A B D) (g := 0) (k := 0) hget0,
                Frame.stateAt_zero]
              rfl
            exact timeOf_of hs
          rcases released_steps hpre ht (hS.2 X hX) hmax hW hC hp0 hrel0 with
            hstep | ⟨Y, o, hmaxY, hObl, hlt⟩
          · exact .inl hstep
          · exact .inr ⟨Y, o, hmaxY, hObl, by simp only [rank, htime0] at hlt ⊢; omega⟩
      · obtain ⟨Y, hY, hle, hsz⟩ := alloc_entry hpre hX hW h32 hdn hcov
        exact .inl ⟨Y, hY, hle, hsz⟩
    · refine coll_lag hpre hmax hW hg128 hdn fun h hh hw hno => ?_
      have hm0 : m h = 0 := by
        by_contra hm
        exact hno ⟨0, (talloc_at hW (by omega) (by omega)).2⟩
      have hnil : X.tr h = [] := by
        rw [← List.length_eq_zero_iff, len_eq hpre hX hW hh, hm0]
      have h1 : timeOf L A B D X h = 1 := by
        have h32' : h / 32 = 0 := by omega
        have hz := Frame.stateAt_zero (C := code L A B D) (X := X) (g := h)
        simp only [code, h32', ↓reduceIte] at hz
        have hz' : stateAt L A B D X h (X.tr h).length = some (some ⟨.alloc, 0, []⟩) := by
          rw [hnil]
          exact hz
        rw [timeOf_of hz']
        rfl
      exact ⟨by omega, by omega⟩
  | ld =>
    simp only [SiteEvent] at hev
    obtain ⟨vs, -, rfl⟩ := hev
    obtain ⟨-, -, hpos, -, -⟩ := hW.tld he
    have htime : timeOf L A B D X g = 17 := timeOf_of (d := ⟨.waitLd, c, vs⟩) hnext
    have htk := tcK_ld hW hg128 (by omega)
    rw [← hpos] at htk
    have hdn : ¬ TcWarpDone L X g (if g / 32 = 0 then 1 else 0) := fun hd =>
      hnr (released_of_done hpre hmax hW he htk hd
        (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h _ => by cases h))
    refine coll_lag hpre hmax hW hg128 hdn fun h hh hw hno => ?_
    have hm : m h ≤ ldIdx h (P h) := by
      by_contra hm
      exact hno ⟨_, by rw [← hw]; exact tcK_ld hW hh (by omega)⟩
    have := time_le_16 hpre ht hW hh hm
    exact ⟨by omega, by omega⟩
  | waitLd =>
    simp only [SiteEvent] at hev
    subst hev
    obtain ⟨-, -, hpos⟩ := hW.waitLd he
    have htime : timeOf L A B D X g = 18 := timeOf_of (d := ⟨.st 0, c, vals⟩) hnext
    have htk := tcK_wld hW hg128 (by omega)
    rw [← hpos] at htk
    have hdn : ¬ TcWarpDone L X g (if g / 32 = 0 then 2 else 1) := fun hd =>
      hnr (released_of_done hpre hmax hW he htk hd
        (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h _ => by cases h))
    refine coll_lag hpre hmax hW hg128 hdn fun h hh hw hno => ?_
    have hm : m h ≤ ldIdx h (P h) + 1 := by
      by_contra hm
      exact hno ⟨_, by rw [← hw]; exact tcK_wld hW hh (by omega)⟩
    have := time_le_17 hpre ht hW hh hm
    exact ⟨by omega, by omega⟩
  | dealloc =>
    simp only [SiteEvent] at hev
    subst hev
    obtain ⟨-, -, h32, hpos, -, -⟩ := hW.tdealloc he
    have htime : timeOf L A B D X g = 30 := timeOf_of (d := ⟨.exit, c, vals⟩) hnext
    have htk := tcK_dealloc hW hg128 h32 (by omega)
    rw [← hpos] at htk
    by_cases hdn : TcWarpDone L X g 3
    · have hnc : ¬ Covered L X (g, ldIdx g (P g) + 13) := fun hc => hnr (released_of_done hpre hmax
        hW he htk hdn (fun _ _ _ _ _ => by rw [hpos]; exact returnReady_of_covered hmax hW hc)
        (fun _ _ _ _ h _ => by cases h))
      obtain ⟨Y, hY, hle, hsz⟩ := dealloc_entry hpre hX hW h32 hdn hnc
      exact .inl ⟨Y, hY, hle, hsz⟩
    · refine coll_lag hpre hmax hW hg128 hdn fun h hh hw hno => ?_
      have hm : m h ≤ ldIdx h (P h) + 13 := by
        by_contra hm
        exact hno ⟨_, tcK_dealloc hW hh (by omega) (by omega)⟩
      have := time_le_29 hpre ht hW hh (by omega) hm
      exact ⟨hm, by omega⟩
  | _ => simp [Site.blocks] at hb

omit hpre ht in
/-- **An uncovered allocator operation steps**: it is its thread's last event, so the thread is
pending, ranked below it. -/
theorem tmem_steps (ho : Descent.Obl L X .tmem) :
    Descent.Steps L kernel [] mem0 (Descent.Obl L) (rank L A B D) X .tmem := by
  have hX := hmax.1
  simp only [Descent.Obl, Drained, not_forall] at ho
  obtain ⟨⟨g, j⟩, pc, grp, dst, req, hget, hnc⟩ := ho
  have hmw : MustWait X (g, j) := by
    refine ⟨pc, grp, dst, req, hget, ?_⟩
    rcases hW.resource hget with ⟨_, _, rfl, rfl, rfl⟩ | ⟨_, _, rfl, rfl, rfl⟩
    · trivial
    · exact .inl rfl
  have hlast := Step.pending_is_last hX hmw hnc
  simp only at hlast
  have hle := timeOf_le (L := L) (A := A) (B := B) (D := D) (X := X) g
  refine .inr ⟨X, .thread g, hmax, ⟨Frame.lt_of_get hX hget, not_canceled hW hX,
    fun pc' hl => ?_⟩, by simp only [rank]; omega⟩
  have hx : X.get (g, (X.tr g).length - 1) = some ⟨pc', .exit⟩ := by
    change (X.tr g)[_]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hl
  rw [show (X.tr g).length - 1 = j by omega, hget] at hx
  cases hx

end

end

end PTX.Kernels.TcGemm.Proof

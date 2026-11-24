-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.Snoc
public import Lemmas.Cluster.ClusterBarrierExecution

@[expose] public section

/-! Thread-order preservation when appending an ordinary instruction. Independent
async stages and phase histories are preserved, not reconstructed from thread order. -/
namespace PTX
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event}
  {r : Nat → Option AsyncCopy.Ref}

theorem old_step_snoc_ps {a b : EvId} (h : po X a b ∨ CtaBarSync L X a b) :
    po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b := by
  rcases h with h | hs
  · exact .inl ((po_snoc_old h.2.2.1).mpr h)
  · exact .inr (CtaBarSync.mono hs le_snoc)

/-- Without a new release arrival, an old mbarrier synchronization stays old. -/
theorem msync_snoc_old (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) (h : MSync L (X.snoc g e r) a b) :
    MSync L X a b := by
  obtain ⟨x, w, m, rs, ws, ⟨tx, count, pc, hp⟩, ⟨⟨pcw, parity, hw⟩, hphase⟩, hsc, hwf, hwlt, _,
    hxe, hle⟩ := h
  have hxo : x.2 < (X.tr x.1).length := by
    rw [snoc_get] at hp
    split_ifs at hp
    · cases e; cases hp; exact (hna m tx count rs rfl).elim
    · exact len_of_get hp
  have hwo : w.2 < (X.tr w.1).length := by rw [hwf]; omega
  exact ⟨x, w, m, rs, ws, ⟨tx, count, pc, by rwa [snoc_get_old hxo] at hp⟩,
    ⟨⟨pcw, parity, by rwa [snoc_get_old hwo] at hw⟩, hphase⟩, hsc, hwf, hwlt, hbo, hxe, hle⟩

theorem msync_snoc {a b : EvId} (h : MSync L X a b) : MSync L (X.snoc g e r) a b := by
  have le : X.le (X.snoc g e r) := le_snoc
  obtain ⟨x, w, m, rs, ws, ⟨tx, count, pc, hp⟩, ⟨⟨pcw, parity, hw⟩, hphase⟩, hsc, hwf, hwlt, hf,
    hxe, hle⟩ := h
  exact ⟨x, w, m, rs, ws, ⟨tx, count, pc, Execution.le_get le hp⟩,
    ⟨⟨pcw, parity, Execution.le_get le hw⟩, hphase⟩, hsc, hwf, hwlt,
    lt_of_lt_of_le hf (le.1 _).length_le, hxe, hle⟩

theorem snoc_ne_new {v : EvId} (hv : v.2 < (X.tr v.1).length) :
    v ≠ (g, (X.tr g).length) := by
  rintro rfl; simp at hv

theorem snoc_rf_old {v : EvId} (hv : v ≠ (g, (X.tr g).length)) (k : Nat) :
    (X.snoc g e r).rf (.thread v) k = X.rf (.thread v) k := by
  change (if _ then _ else _) = _
  rw [ite_eq_right (fun h => hv (AsyncCopy.Ref.thread.inj h))]

theorem snoc_memReads_thread_old {v : EvId} (hv : v.2 < (X.tr v.1).length) {b : Acc}
    {cs : List (Option Byte)} :
    (X.snoc g e r).MemReads (.thread v) b cs ↔ X.MemReads (.thread v) b cs := by
  simp only [Execution.MemReads, Execution.Reads, Execution.Rmw, snoc_get_old hv]

theorem snoc_memWrites_thread_old {v : EvId} (hv : v.2 < (X.tr v.1).length) {a : Acc}
    {bs : List Byte} :
    (X.snoc g e r).MemWrites (.thread v) a bs ↔ X.MemWrites (.thread v) a bs := by
  simp only [Execution.MemWrites, Execution.Writes, Execution.Rmw, snoc_get_old hv]

theorem StrongRead.memReads {Y : Execution} {v : EvId} {b : Acc} {cs : List (Option Byte)}
    (h : StrongRead Y v b cs) : Y.MemReads (.thread v) b cs := by
  rcases h with ⟨h, -⟩ | ⟨n, h, -⟩
  · exact .inl h
  · exact .inr ⟨n, h⟩

theorem memWrites_thread_lt {Y : Execution} {v : EvId} {a : Acc} {bs : List Byte}
    (h : Y.MemWrites (.thread v) a bs) : v.2 < (Y.tr v.1).length := by
  rcases h with ⟨pc, hp⟩ | ⟨old, pc, hp⟩
  · exact len_of_get hp
  · exact len_of_get hp

theorem memReads_thread_lt {Y : Execution} {v : EvId} {b : Acc} {cs : List (Option Byte)}
    (h : Y.MemReads (.thread v) b cs) : v.2 < (Y.tr v.1).length := by
  rcases h with ⟨pc, hp⟩ | ⟨new, pc, hp⟩
  · exact len_of_get hp
  · exact len_of_get hp

/-- An event of the extension is an old event or the appended one. -/
theorem snoc_lt_or_new {v : EvId} (hv : v.2 < ((X.snoc g e r).tr v.1).length) :
    v.2 < (X.tr v.1).length ∨ v = (g, (X.tr g).length) := by
  rw [snoc_len] at hv
  split_ifs at hv with hg
  · rcases Nat.lt_or_ge v.2 (X.tr g).length with h | h
    · left; rw [hg]; exact h
    · right; exact Prod.ext hg (by omega)
  · exact .inl hv

/-- No old read of `X` reads its first byte from the appended event when the appended event
writes memory in the extension. This holds when the reads of `X` are well formed
(`SnocReadsOld.of_rfWf`) and when the appended event writes nothing (`SnocReadsOld.of_noWrite`).
-/
def SnocReadsOld (X : Execution) (g : Nat) (e : Event) (r : Nat → Option AsyncCopy.Ref) : Prop :=
  ∀ v b cs a bs, v.2 < (X.tr v.1).length → X.MemReads (.thread v) b cs → 0 < b.size →
    X.rf (.thread v) 0 = some (.thread (g, (X.tr g).length)) →
    ¬ (X.snoc g e r).MemWrites (.thread (g, (X.tr g).length)) a bs

theorem SnocReadsOld.of_rfWf {mem0 : Mem0} (hrf : RfWf mem0 X) : SnocReadsOld X g e r := by
  intro v b cs a bs _ hr hz h0 _
  have hs := (hrf _ _ _ hr).2 0 hz
  rw [h0] at hs
  obtain ⟨a', bs', hw, -⟩ := hs
  have hl := memWrites_thread_lt hw
  simp at hl

theorem SnocReadsOld.of_noWrite (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) : SnocReadsOld X g e r := by
  intro v b cs a bs _ _ _ _ hw
  rcases hw with ⟨pc, hp⟩ | ⟨old, pc, hp⟩
  · rw [snoc_get_new] at hp
    exact hwr a bs (congrArg Event.kind (Option.some.inj hp))
  · rw [snoc_get_new] at hp
    exact hrmw a old _ (congrArg Event.kind (Option.some.inj hp))

/-- An old read reads its first byte from an old write. -/
theorem SnocReadsOld.src_old (hold : SnocReadsOld X g e r) {v w : EvId} {b : Acc}
    {cs : List (Option Byte)} {a : Acc} {bs : List Byte} (hv : v.2 < (X.tr v.1).length)
    (hr : (X.snoc g e r).MemReads (.thread v) b cs) (hz : 0 < b.size)
    (h : (X.snoc g e r).rf (.thread v) 0 = some (.thread w))
    (hw : (X.snoc g e r).MemWrites (.thread w) a bs) : w.2 < (X.tr w.1).length := by
  rcases snoc_lt_or_new (memWrites_thread_lt hw) with hwo | rfl
  · exact hwo
  · rw [snoc_rf_old (snoc_ne_new hv)] at h
    exact (hold v b cs a bs hv ((snoc_memReads_thread_old hv).mp hr) hz h hw).elim

/-- A synchronization of the extension that starts at the appended event needs a read that reads
from a releasing write of the appended event, or an appended `fence.sc`. -/
theorem snoc_no_baseCausality_from_new_of
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (hnew : ∀ a bs v b cs, (X.snoc g e r).MemWrites (.thread (g, (X.tr g).length)) a bs →
      a.release = true → (X.snoc g e r).MemReads (.thread v) b cs → 0 < b.size →
      (X.snoc g e r).rf (.thread v) 0 ≠ some (.thread (g, (X.tr g).length))) {f : EvId} :
    ¬ baseCausality L (X.snoc g e r) (g, (X.tr g).length) f := by
  intro h
  obtain ⟨c, h1, _⟩ := Relation.TransGen.head'_iff.mp h
  rcases h1 with ⟨h1, h2, h3⟩ | ⟨_, k, i, j, hi, _, h4, _⟩ | hs | hc | hw | ha | hfs
  · simp only at h1 h2; rw [← h1, snoc_len, ite_eq_left rfl] at h3; omega
  · have hi' := hi.lt
    simp only [snoc_len, ↓reduceIte] at hi'; omega
  · obtain ⟨x, w, m, rs, ws, hr, _, _, _, _, _, hx, hle⟩ := hs
    have hxl := hr.lt
    rw [snoc_len, ite_eq_left hx] at hxl
    have hxe : x = (g, (X.tr g).length) := Prod.ext hx (by simp only at hle; omega)
    obtain ⟨tx, count, pc, hp⟩ := hr
    rw [hxe, snoc_get_new] at hp
    cases e; cases hp; exact hna m tx count rs rfl
  · obtain ⟨_, i, j, _, hi, hlt, _⟩ := hc
    simp only [snoc_len, ↓reduceIte] at hi
    omega
  · obtain ⟨i, j, ⟨_, mask, inst, ⟨pc, hp⟩, _⟩, hi, _⟩ := hw
    have hh := len_of_get hp
    simp only [snoc_len, ↓reduceIte] at hh
    omega
  · obtain ⟨a, b, bs, cs, hw, hread, hr, -, -, -, hz, -, -, hf⟩ := ha
    exact hnew a bs c b cs hw hr hread hz (hf 0 hz)
  · rcases hfs with
      ⟨w, rd, a, b, bs, cs, se, sf, hw, -, hsr, hrel, -, -, -, -, hz, -, -, -, -, hf⟩ |
      ⟨⟨s, -, ⟨pc, hp⟩, -, -⟩, -⟩
    · rcases hrel with ⟨rfl, hr, -⟩ | ⟨sem, -, -, h1, h2⟩
      · exact hnew a bs rd b cs hw hr hsr.memReads hz (hf 0 hz)
      · have hwl := memWrites_thread_lt hw
        simp only at h1 h2
        rw [snoc_len, ← h1, ite_eq_left rfl] at hwl
        omega
    · rw [snoc_get_new] at hp
      exact hsc s (congrArg Event.kind (Option.some.inj hp))

/-- An appended instruction that is no release arrival, no releasing write or atomic and no
`fence.sc` starts no synchronization. -/
theorem snoc_no_baseCausality_from_new_of_not_arrive
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hwr : ∀ a bs, e.kind = .wr a bs → a.release = false)
    (hrmw : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    (hsc : ∀ s, e.kind ≠ .fence .sc s) {f : EvId} :
    ¬ baseCausality L (X.snoc g e r) (g, (X.tr g).length) f := by
  refine snoc_no_baseCausality_from_new_of hna hsc fun a bs v b cs hw hr _ _ _ => ?_
  rcases hw with ⟨pc, hp⟩ | ⟨old, pc, hp⟩
  · rw [snoc_get_new] at hp
    rw [hwr a bs (congrArg Event.kind (Option.some.inj hp))] at hr
    cases hr
  · rw [snoc_get_new] at hp
    rw [hrmw a old _ (congrArg Event.kind (Option.some.inj hp))] at hr
    cases hr

/-- The appended event does not read its first byte from itself. -/
def SnocReadsSelf (X : Execution) (g : Nat) (e : Event) (r : Nat → Option AsyncCopy.Ref) : Prop :=
  ∀ b cs, (X.snoc g e r).MemReads (.thread (g, (X.tr g).length)) b cs → 0 < b.size →
    r 0 ≠ some (.thread (g, (X.tr g).length))

/-- An appended instruction without asynchronous or object effects starts no synchronization when
no old read reads from it (`SnocReadsOld`) and it does not read from itself (`SnocReadsSelf`). -/
theorem snoc_no_baseCausality_from_new (hk : e.kind.isTma = false)
    (hold : SnocReadsOld X g e r) (hself : SnocReadsSelf X g e r)
    {f : EvId} :
    ¬ baseCausality L (X.snoc g e r) (g, (X.tr g).length) f := by
  refine snoc_no_baseCausality_from_new_of (fun m tx count sc he => by rw [he] at hk; cases hk)
    (fun s he => by rw [he] at hk; cases hk) fun a bs v b cs hw _ hread hz hv => ?_
  rcases snoc_lt_or_new (memReads_thread_lt hread) with hvo | rfl
  · have hl := hold.src_old hvo hread hz hv hw
    simp at hl
  · exact hself b cs hread hz (by rw [← hv]; exact (ite_eq_left rfl).symm)

theorem old_step_snoc {a b : EvId}
    (h : po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b) :
    po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨ MSync L (X.snoc g e r) a b := by
  rcases h with hp | hs | hm
  · rcases old_step_snoc_ps (.inl hp) with hp | hs
    · exact .inl hp
    · exact .inr (.inl hs)
  · rcases old_step_snoc_ps (.inr hs) with hp | hs
    · exact .inl hp
    · exact .inr (.inl hs)
  · exact .inr (.inr (msync_snoc hm))

/-- Appending an event keeps every release/acquire synchronization. -/
theorem synchronizesWith_snoc {a b : EvId} (h : synchronizesWith L X a b) :
    synchronizesWith L (X.snoc g e r) a b := by
  have le : X.le (X.snoc g e r) := le_snoc
  obtain ⟨aa, bb, bs, cs, hw, hread, hr, ha, hl, hn, hz, hs, ht, hf⟩ := h
  refine ⟨aa, bb, bs, cs, ?_, ?_, hr, ha, hl, hn, hz, hs, ht, ?_⟩
  · rcases hw with ⟨pc, hp⟩ | ⟨old, pc, hp⟩
    · exact .inl ⟨pc, Execution.le_get le hp⟩
    · exact .inr ⟨old, pc, Execution.le_get le hp⟩
  · rcases hread with ⟨pc, hp⟩ | ⟨new, pc, hp⟩
    · exact .inl ⟨pc, Execution.le_get le hp⟩
    · exact .inr ⟨new, pc, Execution.le_get le hp⟩
  · intro k hk
    rw [le.2.1 (.thread b) k ⟨bb, cs, hread⟩]
    exact hf k hk

/-- Appending an event keeps every fence synchronization; the Fence-SC order is unchanged. -/
theorem fenceSync_snoc {a b : EvId} (h : FenceSync L X a b) :
    FenceSync L (X.snoc g e r) a b := by
  have le : X.le (X.snoc g e r) := le_snoc
  have get {v : EvId} {k : Kind} (h : ∃ pc, X.get v = some ⟨pc, k⟩) :
      ∃ pc, (X.snoc g e r).get v = some ⟨pc, k⟩ := by
    obtain ⟨pc, hp⟩ := h; exact ⟨pc, Execution.le_get le hp⟩
  rcases h with ⟨w, rd, aa, bb, bs, cs, se, sf, hw, hst, hsr, hrel, hacq, hfn, hl, hn, hz, hs1,
      hs2, hs3, hs4, hf⟩ | ⟨⟨s, s', hs, hs', hm⟩, hsc⟩
  · refine .inl ⟨w, rd, aa, bb, bs, cs, se, sf, ?_, hst, ?_, ?_, ?_, ?_, hl, hn, hz, hs1, hs2, hs3,
      hs4, ?_⟩
    · rcases hw with h | ⟨old, h⟩
      · exact .inl (get h)
      · exact .inr ⟨old, get h⟩
    · rcases hsr with ⟨h, hb⟩ | ⟨n, h, hb⟩
      · exact .inl ⟨get h, hb⟩
      · exact .inr ⟨n, get h, hb⟩
    · rcases hrel with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, get h, h1⟩
    · rcases hacq with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, get h, h1⟩
    · obtain ⟨sem, sc, h | h⟩ := hfn
      · exact ⟨sem, sc, .inl (get h)⟩
      · exact ⟨sem, sc, .inr (get h)⟩
    · intro k hk
      rw [le.2.1 (.thread rd) k ⟨bb, cs, hsr.memReads⟩]
      exact hf k hk
  · exact .inr ⟨⟨s, s', get hs, get hs', hm⟩, hsc⟩

theorem old_step_snoc_full {a b : EvId}
    (h : po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) :
    po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨ MSync L (X.snoc g e r) a b ∨
      ClusterSync L (X.snoc g e r) a b ∨ WarpBarSync L (X.snoc g e r) a b ∨
      synchronizesWith L (X.snoc g e r) a b ∨ FenceSync L (X.snoc g e r) a b := by
  have le : X.le (X.snoc g e r) := le_snoc
  rcases h with h | h | h | h | h | h | h
  · rcases old_step_snoc (g := g) (e := e) (r := r) (.inl h) with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · rcases old_step_snoc (g := g) (e := e) (r := r) (.inr (.inl h)) with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inl (msync_snoc h)))
  · exact .inr (.inr (.inr (.inl (h.mono le))))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    obtain ⟨i, j, ⟨hs, mask, inst, ⟨pc, hp⟩, ⟨pc', hq⟩⟩, hi, hj, hf⟩ := h
    exact ⟨i, j, ⟨hs, mask, inst, ⟨pc, Execution.le_get le hp⟩,
      ⟨pc', Execution.le_get le hq⟩⟩, hi, hj, lt_of_lt_of_le hf (le.1 _).length_le⟩
  · exact .inr (.inr (.inr (.inr (.inr (.inl (synchronizesWith_snoc h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (fenceSync_snoc h))))))

/-- A release/acquire synchronization of the extension into an old event is one of `X`: the old
acquire read reads from an old write. -/
theorem synchronizesWith_snoc_old (hold : SnocReadsOld X g e r) {a b : EvId}
    (hbo : b.2 < (X.tr b.1).length) (h : synchronizesWith L (X.snoc g e r) a b) :
    synchronizesWith L X a b := by
  obtain ⟨aa, bb, bs, cs, hw, hread, hr, ha, hl, hn, hz, hs, ht, hf⟩ := h
  have hao := hold.src_old hbo hread hz (hf 0 hz) hw
  refine ⟨aa, bb, bs, cs, (snoc_memWrites_thread_old hao).mp hw,
    (snoc_memReads_thread_old hbo).mp hread, hr, ha, hl, hn, hz, hs, ht, fun k hk => ?_⟩
  rw [← snoc_rf_old (snoc_ne_new hbo)]
  exact hf k hk

/-- A fence synchronization of the extension into an old event is one of `X` when the appended
event is no `fence.sc`: the acquire pattern is old, so its read reads from an old write, and the
release pattern ends at that write. -/
theorem fenceSync_snoc_old (hold : SnocReadsOld X g e r) (hsc : ∀ s, e.kind ≠ .fence .sc s)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) (h : FenceSync L (X.snoc g e r) a b) :
    FenceSync L X a b := by
  have fence {v : EvId} {sem : FenceSem} {s : MbarScope} (hv : v.2 < (X.tr v.1).length)
      (h : (X.snoc g e r).ThreadFence v sem s) : X.ThreadFence v sem s := by
    obtain ⟨pc, hp⟩ := h; exact ⟨pc, by rwa [snoc_get_old hv] at hp⟩
  rcases h with ⟨w, rd, aa, bb, bs, cs, se, sf, hw, hst, hsr, hrel, hacq, hfn, hl, hn, hz, hs1,
      hs2, hs3, hs4, hf⟩ | ⟨⟨s, s', hs, hs', hm⟩, hfsc⟩
  · have hro : rd.2 < (X.tr rd.1).length := by
      rcases hacq with ⟨rfl, -, -⟩ | ⟨sem, -, -, h1, h2⟩
      · exact hbo
      · rw [h1]; omega
    have hwo := hold.src_old hro hsr.memReads hz (hf 0 hz) hw
    have hao : a.2 < (X.tr a.1).length := by
      rcases hrel with ⟨rfl, -, -⟩ | ⟨sem, -, -, h1, h2⟩
      · exact hwo
      · rw [h1]; omega
    refine .inl ⟨w, rd, aa, bb, bs, cs, se, sf, (snoc_memWrites_thread_old hwo).mp hw, hst, ?_,
      ?_, ?_, ?_, hl, hn, hz, hs1, hs2, hs3, hs4, fun k hk => ?_⟩
    · rcases hsr with ⟨⟨pc, hp⟩, hb⟩ | ⟨n, ⟨pc, hp⟩, hb⟩
      · exact .inl ⟨⟨pc, by rwa [snoc_get_old hro] at hp⟩, hb⟩
      · exact .inr ⟨n, ⟨pc, by rwa [snoc_get_old hro] at hp⟩, hb⟩
    · rcases hrel with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, fence hao h, h1⟩
    · rcases hacq with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, fence hbo h, h1⟩
    · obtain ⟨sem, sc, h | h⟩ := hfn
      · exact ⟨sem, sc, .inl (fence hao h)⟩
      · exact ⟨sem, sc, .inr (fence hbo h)⟩
    · rw [← snoc_rf_old (snoc_ne_new hro)]
      exact hf k hk
  · have hao : a.2 < (X.tr a.1).length := by
      obtain ⟨pc, hp⟩ := hs
      rcases snoc_lt_or_new (len_of_get hp) with h | rfl
      · exact h
      · rw [snoc_get_new] at hp
        exact (hsc s (congrArg Event.kind (Option.some.inj hp))).elim
    exact .inr ⟨⟨s, s', fence hao hs, fence hbo hs', hm⟩, hfsc⟩

/-- **An appended event adds no causality step into an old event** when it records no new
barrier phase, makes no old mbarrier synchronization new, gives no old warp barrier a new
partner and is no `fence.sc`, and no old read reads from the appended write (`SnocReadsOld`). -/
theorem snoc_step_old_of (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hbar : ∀ v key, CtaBarK L (X.snoc g e r) v key ↔ CtaBarK L X v key)
    (hbara : ∀ v key, CtaBarArrivalK L (X.snoc g e r) v key ↔ CtaBarArrivalK L X v key)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (hms : MSync L (X.snoc g e r) a b → MSync L X a b)
    (hfresh : ∀ mask inst, e.kind = .warpBar mask inst → ∀ j pc, j.2 + 1 < (X.tr j.1).length →
      X.get j = some ⟨pc, .warpBar mask inst⟩ → ¬ SameWarp L g j.1)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (h : po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨
      MSync L (X.snoc g e r) a b ∨ ClusterSync L (X.snoc g e r) a b ∨
      WarpBarSync L (X.snoc g e r) a b ∨ synchronizesWith L (X.snoc g e r) a b ∨
      FenceSync L (X.snoc g e r) a b) :
    po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b := by
  rcases h with h | h | h | h | h | h | h
  · exact .inl ((po_snoc_old hbo).mp h)
  · obtain ⟨hc,key,i,j,hi,hj,hei,hjf,_⟩ := h
    exact .inr (.inl ⟨hc,key,i,j,(hbara _ _).mp hi,(hbar _ _).mp hj,hei,hjf,hbo⟩)
  · exact .inr (.inr (.inl (hms h)))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    obtain ⟨hc, i, j, hs, _, hi, hj, _⟩ := h
    obtain ⟨pc, aligned, hp⟩ := hcl.arrival_present hs.choose_spec.1
    exact ⟨hc, i, j, hs, len_of_get hp, hi, hj, hbo⟩
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    obtain ⟨i, j, ⟨hs, mask, inst, ⟨pc, hp⟩, ⟨pc', hq⟩⟩, hi, hj, _⟩ := h
    have hqo : j < (X.tr b.1).length := by omega
    have hqi : X.get (b.1,j) = some ⟨pc', .warpBar mask inst⟩ := by
      rwa [snoc_get_old hqo] at hq
    have hpo : i < (X.tr a.1).length := by
      rw [snoc_get] at hp
      split_ifs at hp with hnew
      · have he := congrArg Event.kind (Option.some.inj hp)
        simp only [Prod.mk.injEq] at hnew
        obtain ⟨rfl, -⟩ := hnew
        exact (hfresh mask inst he (b.1, j) pc' (by simp only; omega) hqi hs).elim
      · exact len_of_get hp
    exact ⟨i,j,⟨hs,mask,inst,⟨pc,by rwa [snoc_get_old hpo] at hp⟩,⟨pc',hqi⟩⟩,hi,hj,hbo⟩
  · exact .inr (.inr (.inr (.inr (.inr (.inl (synchronizesWith_snoc_old hold hbo h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (fenceSync_snoc_old hold hsc hbo h))))))

/-- Causality into an old event of `Y` is old when every causality step of `Y` into an old
event is a step of `X`. -/
theorem baseCausality_old_of_step {Y : Execution}
    (hstep : ∀ {a b : EvId}, b.2 < (X.tr b.1).length →
      (po Y a b ∨ CtaBarSync L Y a b ∨ MSync L Y a b ∨ ClusterSync L Y a b ∨
        WarpBarSync L Y a b ∨ synchronizesWith L Y a b ∨ FenceSync L Y a b) →
      po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
        WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b)
    {a b : EvId} (h : baseCausality L Y a b)
        (hbo : b.2 < (X.tr b.1).length) : baseCausality L X a b := by
  induction h with
  | single h => exact .single (hstep hbo h)
  | @tail b c _ hbc ih =>
    have hbc' := hstep hbo hbc
    exact (ih (baseCausality_events (Relation.TransGen.single hbc')).1).tail hbc'

theorem snoc_step_old_with_bar (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst)
    (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hbar : ∀ v key, CtaBarK L (X.snoc g e r) v key ↔ CtaBarK L X v key)
    (hbara : ∀ v key, CtaBarArrivalK L (X.snoc g e r) v key ↔ CtaBarArrivalK L X v key)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨
      MSync L (X.snoc g e r) a b ∨ ClusterSync L (X.snoc g e r) a b ∨
      WarpBarSync L (X.snoc g e r) a b ∨ synchronizesWith L (X.snoc g e r) a b ∨
      FenceSync L (X.snoc g e r) a b) :
    po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b :=
  snoc_step_old_of hcl hold hbar hbara hbo (msync_snoc_old hna hbo) (fun m i he =>
      (hwb m i he).elim) hsc h

theorem snoc_step_old_full (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst)
    (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨
      MSync L (X.snoc g e r) a b ∨ ClusterSync L (X.snoc g e r) a b ∨
      WarpBarSync L (X.snoc g e r) a b ∨ synchronizesWith L (X.snoc g e r) a b ∨
      FenceSync L (X.snoc g e r) a b) :
    po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b :=
  snoc_step_old_with_bar hwb hcl hold (fun _ _ => snoc_ctaBarK hnb)
    (fun _ _ => snoc_ctaBarArrivalK hnb) hna hsc hbo h

/-- Appending a source event alone does not record a new collective arrival. -/
theorem snoc_ctaBarK_history (hc : CtaBarHistoryOk L X) {v : EvId} {key : Nat} :
    CtaBarK L (X.snoc g e r) v key ↔ CtaBarK L X v key := by
  constructor
  · rintro ⟨hg,⟨count,pc,hp⟩,hgen⟩
    have hgen' : CtaBarrier.GenerationOf L.block (X.barriers (v.1 / L.block)) v (key % 16)
      (key / 16) := hgen
    obtain ⟨ev,he⟩ := hc.generation_present hgen'
    unfold Execution.IsBarrier at hp
    exact ⟨hg,⟨count,pc,by rwa [snoc_get_old (len_of_get he)] at hp⟩,hgen'⟩
  · intro h; exact h.mono le_snoc

/-- Appending a source event alone does not record a new collective arrival of either form. -/
theorem snoc_ctaBarArrivalK_history (hc : CtaBarHistoryOk L X) {v : EvId} {key : Nat} :
    CtaBarArrivalK L (X.snoc g e r) v key ↔ CtaBarArrivalK L X v key := by
  constructor
  · rintro ⟨hg,⟨count,pc,mode,hp⟩,hgen⟩
    have hgen' : CtaBarrier.GenerationOf L.block (X.barriers (v.1 / L.block)) v (key % 16)
      (key / 16) := hgen
    obtain ⟨ev,he⟩ := hc.generation_present hgen'
    exact ⟨hg,⟨count,pc,mode,by rwa [snoc_get_old (len_of_get he)] at hp⟩,hgen'⟩
  · intro h; exact h.mono le_snoc

/-- Appending any thread event preserves the existing thread causality. -/
theorem baseCausality_snoc {a b : EvId} (h : baseCausality L X a b) : baseCausality L
    (X.snoc g e r) a b := by
  induction h with
  | single h => exact .single (old_step_snoc_full h)
  | tail _ h ih => exact ih.tail (old_step_snoc_full h)

/-- Without a new barrier arrival, release arrival or `fence.sc`, appending an instruction to an
execution where no old read reads from it (`SnocReadsOld`) cannot create new thread order into an
old event. This includes TC issue instructions. -/
theorem baseCausality_snoc_old_of_not_arrive (hcl : ClusterHistoryOk L X)
    (hold : SnocReadsOld X g e r)
    (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst) (hnb : ∀ id count mode,
        e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    baseCausality L (X.snoc g e r) a b ↔ baseCausality L X a b :=
  ⟨fun h => baseCausality_old_of_step (snoc_step_old_full hwb hcl hold hnb hna hsc) h hbo,
      baseCausality_snoc⟩

theorem baseCausality_snoc_old (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hk : e.kind.isTma = false) {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    baseCausality L (X.snoc g e r) a b ↔ baseCausality L X a b :=
  baseCausality_snoc_old_of_not_arrive hcl hold (fun mask inst he => by rw [he] at hk; cases hk)
    hnb (fun m tx count sc he => by rw [he] at hk; cases hk)
    (fun s he => by rw [he] at hk; cases hk) hbo

/-- Preserve causality by preserving each generating relation. -/
theorem baseCausality_congr {Y Y' : Execution} (hl : ∀ h, (Y.tr h).length = (Y'.tr h).length)
    (hsa : ∀ a b, SameAccess Y a b ↔ SameAccess Y' a b)
    (hbar : ∀ v k, CtaBarK L Y v k ↔ CtaBarK L Y' v k)
    (hbara : ∀ v k, CtaBarArrivalK L Y v k ↔ CtaBarArrivalK L Y' v k)
    (hms : ∀ a b, MSync L Y a b ↔ MSync L Y' a b)
    (hc : ∀ a b, ClusterSync L Y a b ↔ ClusterSync L Y' a b)
    (hwb : ∀ a b, WarpBarSync L Y a b ↔ WarpBarSync L Y' a b)
    (hm : ∀ a b, synchronizesWith L Y a b ↔ synchronizesWith L Y' a b)
    (hfs : ∀ a b, FenceSync L Y a b ↔ FenceSync L Y' a b) :
    baseCausality L Y = baseCausality L Y' := by
  have hstep : (fun a b => po Y a b ∨ CtaBarSync L Y a b ∨ MSync L Y a b ∨
      ClusterSync L Y a b ∨ WarpBarSync L Y a b ∨ synchronizesWith L Y a b ∨ FenceSync L Y a b) =
      (fun a b => po Y' a b ∨ CtaBarSync L Y' a b ∨ MSync L Y' a b ∨
      ClusterSync L Y' a b ∨ WarpBarSync L Y' a b ∨ synchronizesWith L Y' a b ∨
        FenceSync L Y' a b) := by
    funext a b
    apply propext
    simp only [hms, hc, hwb, hm, hfs]
    unfold po CtaBarSync
    simp only [hl, hbar, hbara, hsa]
  unfold baseCausality; rw [hstep]

theorem snoc_rd_kind {a0 : Acc} {bs0 : List (Option Byte)} {pc : Nat} {v : EvId} {k : Kind}
    (hk : ∀ a bs, k ≠ .rd a bs) :
    (∃ pc', (X.snoc g ⟨pc, .rd a0 bs0⟩ r).get v = some ⟨pc', k⟩) ↔
      ∃ pc', X.get v = some ⟨pc', k⟩ := by
  rw [snoc_get]
  split_ifs with hv
  · constructor
    · rintro ⟨pc', hev⟩; cases hev; exact absurd rfl (hk a0 bs0)
    · rintro ⟨pc', hev⟩; subst hv
      unfold Execution.get at hev; rw [List.getElem?_eq_none (le_refl _)] at hev; cases hev
  · rfl

theorem synchronizesWith_snoc_rd {a0 : Acc} {bs0 : List (Option Byte)} {pc : Nat}
    (ha : a0.acquire = false) {u v : EvId} :
    synchronizesWith L (X.snoc g ⟨pc, .rd a0 bs0⟩ r) u v ↔ synchronizesWith L X u v := by
  refine ⟨fun h => ?_, synchronizesWith_snoc⟩
  obtain ⟨a, b, bs, cs, hw, hread, hr, hac, hl, hn, hz, hs, ht, hf⟩ := h
  have hw' : X.MemWrites (.thread u) a bs := by
    rcases hw with ⟨p, hp⟩ | ⟨old, p, hp⟩
    · exact .inl ((snoc_rd_kind (by simp)).mp ⟨p, hp⟩)
    · exact .inr ⟨old, (snoc_rd_kind (by simp)).mp ⟨p, hp⟩⟩
  have hvo : v ≠ (g, (X.tr g).length) := by
    rintro rfl
    rcases hread with ⟨q, hq⟩ | ⟨new, q, hq⟩
    · rw [snoc_get_new] at hq; cases hq; rw [ha] at hac; cases hac
    · rw [snoc_get_new] at hq; cases hq
  have hread' : X.MemReads (.thread v) b cs := by
    simpa only [Execution.MemReads, Execution.Reads, Execution.Rmw, snoc_get,
      ite_eq_right hvo] using hread
  refine ⟨a, b, bs, cs, hw', hread', hr, hac, hl, hn, hz, hs, ht, fun k hk => ?_⟩
  rw [← snoc_rf_old hvo]
  exact hf k hk

/-- An appended read without acquire semantics is in no fence synchronization: it is no write and
no fence, and nothing follows it in its thread. -/
theorem fenceSync_snoc_rd {a0 : Acc} {bs0 : List (Option Byte)} {pc : Nat}
    (ha : a0.acquire = false) {u v : EvId} :
    FenceSync L (X.snoc g ⟨pc, .rd a0 bs0⟩ r) u v ↔ FenceSync L X u v := by
  refine ⟨fun h => ?_, fenceSync_snoc⟩
  have fence {x : EvId} {sem : FenceSem} {s : MbarScope}
      (h : (X.snoc g ⟨pc, .rd a0 bs0⟩ r).ThreadFence x sem s) : X.ThreadFence x sem s :=
    (snoc_rd_kind (by simp)).mp h
  rcases h with ⟨w, rd, aa, bb, bs, cs, se, sf, hw, hst, hsr, hrel, hacq, hfn, hl, hn, hz, hs1,
      hs2, hs3, hs4, hf⟩ | ⟨⟨s, s', hs, hs', hm⟩, hfsc⟩
  · have hw' : X.MemWrites (.thread w) aa bs := by
      rcases hw with ⟨p, hp⟩ | ⟨old, p, hp⟩
      · exact .inl ((snoc_rd_kind (by simp)).mp ⟨p, hp⟩)
      · exact .inr ⟨old, (snoc_rd_kind (by simp)).mp ⟨p, hp⟩⟩
    have hro : rd ≠ (g, (X.tr g).length) := by
      rcases hacq with ⟨rfl, hb, -⟩ | ⟨sem, hv, -, h1, h2⟩
      · rintro rfl
        rcases hsr with ⟨⟨q, hq⟩, -⟩ | ⟨n, ⟨q, hq⟩, -⟩
        · rw [snoc_get_new] at hq; cases hq; rw [ha] at hb; cases hb
        · rw [snoc_get_new] at hq; cases hq
      · obtain ⟨q, hq⟩ := fence hv
        have hvl := len_of_get hq
        exact snoc_ne_new (by rw [h1]; omega)
    have hsr' : StrongRead X rd bb cs := by
      simpa only [StrongRead, Execution.Reads, Execution.Rmw, snoc_get, ite_eq_right hro] using hsr
    refine .inl ⟨w, rd, aa, bb, bs, cs, se, sf, hw', hst, hsr', ?_, ?_, ?_, hl, hn, hz, hs1, hs2,
      hs3, hs4, fun k hk => ?_⟩
    · rcases hrel with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, fence h, h1⟩
    · rcases hacq with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, fence h, h1⟩
    · obtain ⟨sem, sc, h | h⟩ := hfn
      · exact ⟨sem, sc, .inl (fence h)⟩
      · exact ⟨sem, sc, .inr (fence h)⟩
    · rw [← snoc_rf_old hro]
      exact hf k hk
  · exact .inr ⟨⟨s, s', fence hs, fence hs', hm⟩, hfsc⟩

theorem baseCausality_snoc_eq {e' : Event} {r' : Nat → Option AsyncCopy.Ref} {a0 a1 : Acc}
    {bs0 bs1 : List (Option Byte)} {pc pc' : Nat} (he : e = ⟨pc, .rd a0 bs0⟩)
    (he' : e' = ⟨pc', .rd a1 bs1⟩)
    (ha0 : a0.acquire = false) (ha1 : a1.acquire = false) (hsame : a0 = a1) :
    baseCausality L (X.snoc g e r) = baseCausality L (X.snoc g e' r') := by
  subst he; subst he'; subst hsame
  have hget : ∀ v, ((X.snoc g ⟨pc, .rd a0 bs0⟩ r).get v).bind Event.acc =
      ((X.snoc g ⟨pc', .rd a0 bs1⟩ r').get v).bind Event.acc := by
    intro v; rw [snoc_get, snoc_get]; split_ifs <;> simp [Event.acc]
  apply baseCausality_congr (fun h => by simp only [snoc_len]) (fun a b => by
    unfold SameAccess; simp only [hget])
  · intro v k
    exact (snoc_ctaBarK (by simp)).trans (snoc_ctaBarK (by simp)).symm
  · intro v k
    exact (snoc_ctaBarArrivalK (by simp)).trans (snoc_ctaBarArrivalK (by simp)).symm
  · intro u v
    have rel (x : EvId) (m : Loc) (sc : MbarScope) :
        MbarRelease (X.snoc g ⟨pc,.rd a0 bs0⟩ r) x m sc ↔
        MbarRelease (X.snoc g ⟨pc',.rd a0 bs1⟩ r') x m sc := by
      by_cases hx : x = (g,(X.tr g).length)
      · simp [MbarRelease,Execution.Arrive,snoc_get,hx]
      · simp only [MbarRelease,Execution.Arrive,snoc_get,ite_eq_right hx]
    have acq (y : AsyncCopy.Ref) (x : EvId) (m : Loc) (b : Bool) (sc : MbarScope) :
        AsyncCopy.WaitObserves (X.snoc g ⟨pc,.rd a0 bs0⟩ r) y x m b sc ↔
        AsyncCopy.WaitObserves (X.snoc g ⟨pc',.rd a0 bs1⟩ r') y x m b sc := by
      by_cases hx : x = (g,(X.tr g).length)
      · simp [AsyncCopy.WaitObserves,snoc_get,hx]
      · simp only [AsyncCopy.WaitObserves,snoc_get,ite_eq_right hx]
        rfl
    unfold MSync
    simp only [rel,acq,snoc_len]
  · intro u v
    unfold ClusterSync
    simp only [snoc_len]
    rfl
  · intro u v
    have hw (x : EvId) (mask inst : Nat) :
        (X.snoc g ⟨pc,.rd a0 bs0⟩ r).WarpBar x mask inst ↔
        (X.snoc g ⟨pc',.rd a0 bs1⟩ r').WarpBar x mask inst :=
      (snoc_rd_kind (k := .warpBar mask inst) (by simp)).trans
        (snoc_rd_kind (k := .warpBar mask inst) (by simp)).symm
    unfold WarpBarSync WarpBarEdge
    simp only [hw,snoc_len]
  · intro u v
    exact (synchronizesWith_snoc_rd ha0).trans (synchronizesWith_snoc_rd ha1).symm
  · intro u v
    exact (fenceSync_snoc_rd ha0).trans (fenceSync_snoc_rd ha1).symm

end
end
end PTX

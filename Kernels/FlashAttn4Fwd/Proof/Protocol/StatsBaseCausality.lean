-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Lemmas.Protocol.RegionOrder
public import Lemmas.Protocol.NamedBarMember

@[expose] public section

/-! # The statistics words are handed over in order

A statistics word (`statsWord`) is written by the softmax thread of its row and read by the
correction thread of its row, which handle the same rows (`rowOf`), so they use the same
statistics barrier (`same_barrier`). The softmax's store of generation `G` (its arrival number `G`
on the barrier follows the store) and the correction's load of generation `G'` (it follows the
correction's `bar.sync` number `G'`) are ordered both ways:

* **`stats_baseCausality`**: if `G ≤ G'`, the store happens before the load, through the softmax's
  arrival number `G` and the correction's `bar.sync` number `G`
  (`NamedBar.Sources.arrive_sync_baseCausality`, Core `CtaBarSync` with a `bar.arrive` source). The
  passed `bar.sync` has the softmax's barrier event of its ordinal
  (`NamedBar.Sources.member_arrival_any`; a softmax thread that exits does so after the store, so it
  made the arrival that follows the store), which comes after the store;
* **`stats_war`**: if `G' < G`, the load happens before the store, through the credit barrier: the
  correction's credit arrival with `G'` earlier ones follows its load, and the softmax's poll with
  `G' + 1` earlier successful polls, before its store, observes it (`StatsCredit`).

So every conflict on the statistics words is ordered (`stats_ordered`): two stores of a word are
one thread's, in program order, and loads do not conflict with each other. That no access of another
proxy touches a statistics word is the premise `hasync`, proved in `OutputRegion`
(`statsAsync`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof CtaBarrier

noncomputable section

namespace Stats

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- Two statistics words with a common byte are one word. -/
theorem word_eq {c c' st st' ρ ρ' : Nat} {a b : Acc} {l : Loc}
    (ha : a.loc = statsWord L c st ρ) (hsa : a.size = 4) (hb : b.loc = statsWord L c' st' ρ')
    (hsb : b.size = 4) (hla : a.Covers l) (hlb : b.Covers l) (hρ : ρ < 128) (hρ' : ρ' < 128) :
    c = c' ∧ st = st' ∧ ρ = ρ' := by
  obtain ⟨-, hc, h1, h2⟩ := hla
  obtain ⟨-, hc', h1', h2'⟩ := hlb
  rw [ha, hsa] at *
  rw [hb, hsb] at *
  simp only [statsWord] at *
  omega

/-- **A row's softmax and correction threads use the same statistics barrier** of the stage. -/
theorem same_barrier (hpre : Pre P L mem0) {g h st : Nat} (hwh : 8 ≤ warpOf L h)
    (hwh' : warpOf L h < 12) (hst : warpOf L g / 4 = st)
    (hρ : rowOf L g = rowOf L h) :
    warpOf L g + 3 = statsId st (warpOf L g % 4) ∧
      warpOf L h - 5 + 4 * st = statsId st (warpOf L g % 4) := by
  unfold rowOf warpOf at *
  rw [hpre.block] at *
  unfold statsId
  omega

/-- Two softmax threads of one CTA, stage and row are one thread. -/
theorem soft_unique (hpre : Pre P L mem0) {g g' : Nat} (hc : ctaOf L g = ctaOf L g')
    (hw : warpOf L g < 8) (hw' : warpOf L g' < 8) (hst : warpOf L g / 4 = warpOf L g' / 4)
    (hρ : rowOf L g = rowOf L g') : g = g' := by
  unfold ctaOf warpOf rowOf at *
  rw [hpre.block] at *
  omega

/-- **A store of generation `G` happens before a load of generation `G' ≥ G`** of its word. -/
theorem stats_baseCausality (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ht : StatsFacts L X)
    {g i h j st : Nat} {a b : Acc} {wa wb : Bool} (hg : g < L.threads) (hwg : warpOf L g < 8)
    (hs : SoftStore L X g i a wa) (hacs : X.Access (g, i) a wa) (hh : h < L.threads)
    (hwh : 8 ≤ warpOf L h) (hwh' : warpOf L h < 12) (hst : st < 2) (hl : CorrLoad L X h j b wb st)
    (hacc : X.Access (h, j) b wb) (hov : a.Overlap b)
    (hord : barOrd X g i (warpOf L g + 3) + 1 ≤ barOrd X h j (warpOf L h - 5 + 4 * st)) :
    baseCausality L X (g, i) (h, j) := by
  obtain ⟨-, hla, hsa, -, hnext⟩ := hs
  obtain ⟨-, hlb, hsb, -⟩ := hl
  obtain ⟨l, hcl, hcl'⟩ := hov
  obtain ⟨hc, hst', hρ⟩ := word_eq hla hsa hlb hsb hcl hcl' (rowOf_lt L g) (rowOf_lt L h)
  obtain ⟨hid, hid'⟩ := same_barrier hpre hwh hwh' hst' hρ
  rw [hid] at hnext hord
  rw [hid'] at hord
  -- the store's event is a memory access, not a barrier event
  obtain ⟨pci, ki, hgi, hki⟩ : ∃ pci ki, X.get (g, i) = some ⟨pci, ki⟩ ∧
      ((∃ a' bs, ki = .rd a' bs) ∨ (∃ a' ws, ki = .wr a' ws) ∨
        ∃ a' old new, ki = .rmw a' old new) := by
    rcases hacs with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
    · exact ⟨pc, _, he, .inl ⟨_, _, rfl⟩⟩
    · exact ⟨pc, _, he, .inr (.inl ⟨_, _, rfl⟩)⟩
    · exact ⟨pc, _, he, .inr (.inr ⟨_, _, _, rfl⟩)⟩
  have hilen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[i]? = some ⟨pci, ki⟩ from hgi)).1
  obtain ⟨y, pcy, cnty, my, hyj, hy, hyo⟩ :=
    exists_bar (X := X) (g := h) (x := j) (c := barOrd X g i (statsId st (warpOf L g % 4)))
      (by omega)
  obtain ⟨hcy, st'', k'', hst'', hk'', hidy, hwy⟩ :=
    stats_of_bar ht hh hy (by unfold statsId; omega)
  have hmy : my = .sync := by
    rcases hwy with ⟨h1, -⟩ | ⟨-, h1⟩
    · omega
    · exact h1
  subst hmy hcy
  have hlen := hacc.lt
  simp only at hlen
  have hk : warpOf L g % 4 < 4 := Nat.mod_lt _ (by decide)
  have hsucc : barOrd X g (i + 1) (statsId st (warpOf L g % 4)) =
      barOrd X g i (statsId st (warpOf L g % 4)) := by
    unfold barOrd
    rw [List.take_add_one, show (X.tr g)[i]? = some ⟨pci, ki⟩ from hgi, Option.toList_some,
      List.countP_append]
    have : Execution.isBarId (statsId st (warpOf L g % 4)) ⟨pci, ki⟩ = false := by
      rcases hki with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    simp [this]
  obtain ⟨j0, pc0, m0, hj0, ho0⟩ := NamedBar.Sources.member_arrival_any hX
    (sources ht (st := st) hk) (shape hpre hst hk) (f := (h, y)) hy (by simp only; omega) (g := g)
    (by unfold ctaOf at hc; exact hc)
    (by
      simp only [pair, Finset.mem_insert, Finset.mem_singleton]
      unfold warpOf at hst' ⊢
      omega)
    (fun ⟨x, pcx, hx⟩ => by
      have hlast := Execution.exit_last hX hg hx
      have hix : i ≠ x := by
        rintro rfl
        rw [hgi] at hx
        cases hx
        rcases hki with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
      obtain ⟨pca, ha⟩ := hnext (by omega)
      refine ⟨i + 1, pca, .arrive, ha, ?_⟩
      rw [← barOrd, ← barOrd, hsucc, hyo])
  have hij0 : i < j0 := by
    rcases Nat.lt_trichotomy i j0 with h' | rfl | h'
    · exact h'
    · rw [hgi] at hj0
      cases hj0
      rcases hki with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
    · have := barOrd_lt hj0 h'
      simp only at ho0
      unfold barOrd at this hyo
      omega
  simp only at ho0
  unfold barOrd at hyo
  exact (sources ht hk).arrive_sync_baseCausality hX (shape hpre hst hk)
    ⟨hg, hh, by unfold ctaOf at hc; exact hc⟩ hj0 hy (by omega) (by rw [ho0, hyo])
    hij0 hyj hlen

/-- **A load of generation `G'` happens before a store of generation `G > G'`** of its word,
through the credit barrier. -/
theorem stats_war (hpre : Pre P L mem0) (hU : StatsCredit L X)
    {g i h j st : Nat} {a b : Acc} {wa wb : Bool} (hg : g < L.threads) (hwg : warpOf L g < 8)
    (hs : SoftStore L X g i a wa) (hacc : X.Access (g, i) a wa) (hh : h < L.threads)
    (hwh : 8 ≤ warpOf L h) (hwh' : warpOf L h < 12) (hst : st < 2)
    (hl : CorrLoad L X h j b wb st) (hov : a.Overlap b)
    (hord : barOrd X h j (warpOf L h - 5 + 4 * st) ≤ barOrd X g i (warpOf L g + 3)) :
    baseCausality L X (h, j) (g, i) := by
  obtain ⟨-, hla, hsa, hpoll, -⟩ := hs
  obtain ⟨-, hlb, hsb, harr, -⟩ := hl
  obtain ⟨l, hcl, hcl'⟩ := hov
  obtain ⟨hc, hst', hρ⟩ := word_eq hla hsa hlb hsb hcl hcl' (rowOf_lt L g) (rowOf_lt L h)
  obtain ⟨hid, hid'⟩ := same_barrier hpre hwh hwh' hst' hρ
  rw [hid] at hpoll hord
  rw [hid'] at harr hord
  rw [hst', hc] at hpoll
  exact (hU (ctaOf L h) st hst).baseCausality_of_counts (h := g) (g := h)
    (q := barOrd X h j (statsId st (warpOf L g % 4)) - 1)
    ⟨hg, hc, hwg, hst'⟩ ⟨hh, rfl, hwh, hwh'⟩ (by omega) (by omega) hacc.lt

/-- **Every conflict on the statistics words is ordered**, given that no access of another proxy
reaches them. -/
theorem stats_ordered (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (hU : StatsCredit L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStatsArea L l → False) :
    ConflictsOrdered L X (InStatsArea L) := by
  intro e f a b l hc ha hb hl
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := hc
  cases e with
  | async i p => exact (hasync i p a we l hie ha hl).elim
  | thread e =>
  cases f with
  | async i p => exact (hasync i p b wf l hif hb hl).elim
  | thread f =>
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  have hie' : X.Access (g, i) a we := hie
  have hif' : X.Access (h, j) b wf := hif
  have hg := access_thread_lt hX hie'
  have hh := access_thread_lt hX hif'
  rcases ht.stats_access hg hie' ha hl with ⟨hwg, hse⟩ | ⟨h8, h12, ste, hste, hle⟩ <;>
    rcases ht.stats_access hh hif' hb hl with ⟨hwh, hsf⟩ | ⟨h8', h12', stf, hstf, hlf⟩
  · obtain ⟨-, hla, hsa, -⟩ := hse
    obtain ⟨-, hlb, hsb, -⟩ := hsf
    obtain ⟨hc, hst, hρ⟩ := word_eq hla hsa hlb hsb ha hb (rowOf_lt L g) (rowOf_lt L h)
    obtain rfl := soft_unique hpre hc hwg hwh hst hρ
    have hij : i ≠ j := fun h' => hne (by rw [h'])
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact .inl (modelCausality.of_base L
        (.single (.inl (po_of_overlap hie' hif' rfl hlt ⟨l, ha, hb⟩))))
    · exact .inr (modelCausality.of_base L
        (.single (.inl (po_of_overlap hif' hie' rfl hlt ⟨l, hb, ha⟩))))
  · by_cases hord : barOrd X g i (warpOf L g + 3) + 1 ≤
        barOrd X h j (warpOf L h - 5 + 4 * stf)
    · exact .inl (modelCausality.of_base L
        (stats_baseCausality hpre hX ht hg hwg hse hie' hh h8' h12' hstf hlf hif' ⟨l, ha, hb⟩
          hord))
    · exact .inr (modelCausality.of_base L
        (stats_war hpre hU (g := g) (h := h) hg hwg hse hie' hh h8' h12' hstf hlf ⟨l, ha, hb⟩
          (by omega)))
  · by_cases hord : barOrd X h j (warpOf L h + 3) + 1 ≤
        barOrd X g i (warpOf L g - 5 + 4 * ste)
    · exact .inr (modelCausality.of_base L
        (stats_baseCausality hpre hX ht hh hwh hsf hif' hg h8 h12 hste hle hie' ⟨l, hb, ha⟩
          hord))
    · exact .inl (modelCausality.of_base L
        (stats_war hpre hU (g := h) (h := g) hh hwh hsf hif' hg h8 h12 hste hle ⟨l, hb, ha⟩
          (by omega)))
  · obtain ⟨rfl, -⟩ := hle
    obtain ⟨rfl, -⟩ := hlf
    simp at hw

end Stats

end
end PTX.Kernels.FlashAttn4Fwd.Proof

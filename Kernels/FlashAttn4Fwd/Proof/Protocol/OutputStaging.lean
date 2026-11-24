-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCredit
public import Lemmas.TensorStore.TensorStore
public import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # The output staging ring is ordered

Stage `st`'s staging buffer of a CTA is a ring (`Staging.Ring`) of items: item `j` is the
correction's writes made after `j` staged arrivals of the stage (`gen`) and the store lanes'
tensor stores of the stage made after `j` free arrivals (`rd`). The handoffs are the unit handoffs
of the stage's two barriers (`OutputHandoff`): a store lane's poll with `j` earlier successful polls
of the staged barrier observes every correction thread's staged arrival with `j` earlier ones, and
a correction thread's poll with `j + 1` earlier successful polls of the free barrier observes every
store lane's free arrival with `j` earlier ones. That is the content of the two barriers' phases
(count 128 and 32: one arrival of every producer per phase), proved in `OutputHandoff`
(`Output.outputHandoff`).

* **Publication** (`publish_vis`): a correction write of item `j` is followed by its proxy fence
  and, at or after it, its staged arrival of item `j` or later; a store lane's poll for item
  `j' ≥ j` observes that arrival, and the lane's tensor store follows its poll. So the write is
  visible to the store's source reads (`Staging.Publish.modelCausality`, MEM-MODEL-CAUSALITY).
* **Release** (`release_vis`): a tensor store of item `j` is covered by the lane's later `.read`
  bulk-group wait, before the lane's free arrival of item `j`, which the correction's poll for its
  item `j' > j` observes before its writes. So the source reads are visible to those writes
  (`Staging.Release.modelCausality`, EXT-READ-WAIT-ORDER).
* Two correction writes of a common byte are one thread's (each row's thread writes only its own
  lines, `corr_unique`), in program order, and items grow along it.

So every conflict on a staging byte is ordered (`staging_ordered`, `Staging.Ring.ordered`). That
every access of another proxy to a staging byte is a tensor store's source read is the premise
`hasync`, proved in `OutputRegion` (`stagingAsync`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace Output

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- A store lane of CTA `c`. -/
def storeIn (L : Launch) (c g : Nat) : Prop := g < L.threads ∧ ctaOf L g = c ∧ warpOf L g = 13

/-- **The output handoffs** of every stage of every CTA: staged (correction to store, offset 0) and
free (store to correction, offset 1). -/
def OutputHandoff (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 →
    MbarRing.UnitHandoff L X (stagedBar L c st) (Stats.corrIn L c) (storeIn L c) 0 ∧
      MbarRing.UnitHandoff L X (freeBar L c st) (storeIn L c) (Stats.corrIn L c) 1

/-- The correction writes of item `j` of stage `st` in CTA `c`. -/
def gen (L : Launch) (X : Execution) (c st j : Nat) (e : EvId) : Prop :=
  Stats.corrIn L c e.1 ∧ (∃ a, X.Access e a true ∧ CorrStage L X e.1 e.2 a st) ∧
    arrivals (stagedBar L c st) ((X.tr e.1).take e.2) = j

/-- The tensor stores of item `j` of stage `st` in CTA `c` (any slot). -/
def rd (L : Launch) (X : Execution) (c st j : Nat) (i : EvId) (_ : Nat × Nat × Nat) : Prop :=
  storeIn L c i.1 ∧ (∃ pc addr s, X.get i = some ⟨pc, .tensorStore addr s⟩ ∧
    StoreSrc L X i.1 i.2 pc s st) ∧ arrivals (freeBar L c st) ((X.tr i.1).take i.2) = j

/-- Two correction threads of one CTA and row are one thread. -/
theorem corr_unique (hpre : Pre P L mem0) {g g' : Nat} (hc : ctaOf L g = ctaOf L g')
    (h8 : 8 ≤ warpOf L g) (h12 : warpOf L g < 12) (h8' : 8 ≤ warpOf L g')
    (h12' : warpOf L g' < 12) (hρ : rowOf L g = rowOf L g') : g = g' := by
  unfold ctaOf warpOf rowOf at *
  rw [hpre.block] at *
  omega

/-- A byte of a line is in the line's stage. -/
theorem line_stage {c st hh ρ : Nat} {a : Acc} {l : Loc} (hh2 : hh < 2) (hρ : ρ < 128)
    (ha : InLine L c st hh ρ a) (hl : a.Covers l) :
    InStage L c st l ∧ lineBase L st hh ρ ≤ l.addr ∧ l.addr < lineBase L st hh ρ + 128 := by
  obtain ⟨hs, hc, h1, h2⟩ := ha
  obtain ⟨hs', hc', h3, h4⟩ := hl
  unfold lineBase at *
  refine ⟨⟨hs'.trans hs, hc'.trans hc, by omega, by omega⟩, by omega, by omega⟩

/-- Two lines with a common byte are one line. -/
theorem line_eq {c c' st st' hh hh' ρ ρ' : Nat} {a b : Acc} {l : Loc} (hh2 : hh < 2)
    (hh2' : hh' < 2) (hρ : ρ < 128) (hρ' : ρ' < 128) (ha : InLine L c st hh ρ a)
    (hb : InLine L c' st' hh' ρ' b) (hla : a.Covers l) (hlb : b.Covers l) :
    c = c' ∧ st = st' ∧ ρ = ρ' := by
  obtain ⟨-, hc, h1, h2⟩ := ha
  obtain ⟨-, hc', h1', h2'⟩ := hb
  obtain ⟨-, hlc, h3, h4⟩ := hla
  obtain ⟨-, hlc', h3', h4'⟩ := hlb
  unfold lineBase at *
  refine ⟨hc.symm.trans (hlc.symm.trans (hlc'.trans hc')), by omega, by omega⟩

theorem acc_eq {e : EvId} {a b : Acc} {w w' : Bool} (ha : X.Access e a w) (hb : X.Access e b w') :
    a = b := by
  have h := ha.acc
  rw [hb.acc] at h
  exact (Option.some.inj h).symm

theorem arrivals_mono (m : Loc) (g : Nat) {i j : Nat} (hij : i ≤ j) :
    arrivals m ((X.tr g).take i) ≤ arrivals m ((X.tr g).take j) :=
  (List.take_sublist_take_left (l := X.tr g) hij).countP_le (p := arrivesOn m)

/-- Two correction writes of stage `st` in CTA `c` with a common byte are one thread's. -/
theorem gen_thread (hpre : Pre P L mem0) {c st j j' : Nat} {e f : EvId} {a b : Acc}
    {w w' : Bool} {l : Loc} (he : gen L X c st j e) (hf : gen L X c st j' f)
    (ha : X.Access e a w) (hb : X.Access f b w') (hla : a.Covers l) (hlb : b.Covers l) :
    e.1 = f.1 := by
  obtain ⟨⟨-, hce, h8, h12⟩, ⟨a0, ha0, ⟨hh, hh2, hline⟩, -⟩, -⟩ := he
  obtain ⟨⟨-, hcf, h8', h12'⟩, ⟨b0, hb0, ⟨hh', hh2', hline'⟩, -⟩, -⟩ := hf
  rw [acc_eq ha0 ha] at hline
  rw [acc_eq hb0 hb] at hline'
  obtain ⟨hc, -, hρ⟩ := line_eq hh2 hh2' (rowOf_lt L e.1) (rowOf_lt L f.1) hline
    hline' hla hlb
  exact corr_unique hpre hc h8 h12 h8' h12' hρ

/-- **A correction write is visible to the tensor stores of its item and later items.** -/
theorem publish_vis (hH : OutputHandoff L X) {c st j j' : Nat} {g i : EvId}
    {s : Nat × Nat × Nat} {l : Loc} (hst : st < 2) (hg : gen L X c st j g)
    (hr : rd L X c st j' i s) (hjj : j ≤ j')
    (hcov : AsyncCovers X i (.read (.store s.1 s.2.1 s.2.2)) l) (hl : InStage L c st l) :
    modelCausality L X l (.thread g) (.async i (.read (.store s.1 s.2.1 s.2.2))) := by
  obtain ⟨hcorr, ⟨a0, hacc0, -, -, hfence⟩, hj⟩ := hg
  obtain ⟨hstore, ⟨pc, addr, sp, higet, -, -, hpoll, -⟩, hj'⟩ := hr
  rw [hstore.2.1, hj'] at hpoll
  obtain ⟨w0, pcw, par, acq, sc, hw0, hwget, hwq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := stagedBar L c st) (h := i.1) (f := i.2)
      (c := j') (by omega)
  obtain ⟨x, hx, hs⟩ := (hH c st hst).1 i.1 w0 pcw par acq sc j' hstore hwget hwq g.1 hcorr
  obtain ⟨ev, hev, harr⟩ := hs.arrives
  -- the arrival observed by the store lane's poll comes after the write
  have hgx : g.2 < x := by
    have hle := MbarRing.arrival_index_ge (e := g.2) hev harr hx (by omega)
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · rcases hacc0 with ⟨bs, ⟨pcg, hgg⟩, -⟩ | ⟨bs, ⟨pcg, hgg⟩, -⟩ | ⟨o, n, pcg, hgg⟩ <;>
      · rw [← h] at hev
        rw [hev] at hgg
        cases hgg
        simp [arrivesOn, sourceArrive] at harr
  obtain ⟨rs, ⟨tx, cnt, pcx, hxget⟩, -⟩ := id hs
  rw [← hcorr.2.1] at hxget
  obtain ⟨f, pcf, hgf, hfx, hfget, hfarr⟩ := hfence x pcx tx cnt true rs hgx hxget
  have hpub : Staging.Publish L X g (g.1, f) (g.1, x) (i.1, w0) i (stagedBar L c st) :=
    { isFence := ⟨pcf, hfget⟩
      fence_lt := hcorr.1
      before := .single (.inl (po_of_not_access rfl hgf (len_of_get hfget)
        (by rw [hfget]; rfl)))
      release := hs
      arrive := ⟨rfl, hfx.le⟩
      issue := ⟨rfl, hw0, len_of_get higet⟩
      cluster := ⟨hcorr.1, hstore.1, by
        have h1 := hcorr.2.1
        have h2 := hstore.2.1
        unfold ctaOf at h1 h2
        simp only [h1, h2]⟩ }
  exact hpub.modelCausality hl.1
      (by have := hcorr.2.1; unfold ctaOf at this; rw [this]; exact hl.2.1)
    hcov

/-- **A tensor store's source reads are visible to the correction writes of later items.** -/
theorem release_vis (hX : Consistent L K A mem0 X) (hH : OutputHandoff L X) {c st j j' : Nat}
    {g i : EvId} {s : Nat × Nat × Nat} {a : Acc} {l : Loc} (hst : st < 2)
    (hr : rd L X c st j i s) (hg : gen L X c st j' g) (hjj : j < j') (ha : X.Access g a true)
    (hcov : AsyncCovers X i (.read (.store s.1 s.2.1 s.2.2)) l) :
    modelCausality L X l (.async i (.read (.store s.1 s.2.1 s.2.2))) (.thread g) := by
  obtain ⟨hstore, ⟨pc, addr, sp, higet, -, -, -, -, hwaits⟩, hj⟩ := hr
  obtain ⟨hcorr, ⟨a0, -, -, hpolls, -⟩, hj'⟩ := hg
  rw [hcorr.2.1, hj'] at hpolls
  -- the store lane's free arrival that the correction's poll observes comes after the store
  obtain ⟨y, pcy, par, acq, sc, -, hyget, hyq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := freeBar L c st) (h := g.1) (f := g.2)
      (c := j + 1) (by omega)
  obtain ⟨e, he, hs⟩ := (hH c st hst).2 g.1 y pcy par acq sc j hcorr hyget hyq i.1 hstore
  obtain ⟨ev, hev, harr⟩ := hs.arrives
  have hie : i.2 < e := by
    have hle := MbarRing.arrival_index_ge (e := i.2) hev harr he (by omega)
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · rw [← h, higet] at hev
      cases hev
      simp [arrivesOn, sourceArrive] at harr
  obtain ⟨rs, ⟨tx, cnt, pce, heget⟩, -⟩ := id hs
  rw [← hstore.2.1] at heget
  obtain ⟨w, -, hwe, hwait, hwarr⟩ := hwaits e pce hie (.inr ⟨tx, cnt, true, rs, heget⟩)
  rw [hstore.2.1] at hwarr
  have hrel : Staging.Release L X i (i.1, w) g :=
    { done := Step.BulkWait.stages_of_returned hX hwait
        (by have := len_of_get heget; simp only at this ⊢; omega)
      wait := hwait
      before := (hH c st hst).2.baseCausality_of_counts (h := g.1) (g := i.1) (e := w) (f := g.2)
        (q := j) hcorr hstore (by omega) (by omega) ha.lt }
  exact hrel.modelCausality hcov

/-- **The ring of stage `st`'s staging buffer of CTA `c`**, given that the other proxies only read
staging bytes as tensor-store sources. -/
theorem ring (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (hH : OutputHandoff L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k))
    {c st : Nat} (hst : st < 2) :
    Staging.Ring L X (InStage L c st) (gen L X c st) (rd L X c st) where
  cover := by
    intro e a w l hint hcov hl
    have hstg : InStaging L l := by
      unfold InStage at hl
      unfold InStaging
      obtain ⟨h1, -, h3, h4⟩ := hl
      refine ⟨h1, ?_, ?_⟩ <;> omega
    cases e with
    | thread g =>
      have hg := access_thread_lt hX hint
      obtain ⟨h8, h12, rfl, st', hst', hcs⟩ := ht.staging_access hg hint hcov hstg
      obtain ⟨hh, hh2, hline⟩ := hcs.1
      obtain ⟨hl', -⟩ := line_stage hh2 (rowOf_lt L g.1) hline hcov
      have hcst : ctaOf L g.1 = c ∧ st' = st := by
        obtain ⟨-, hc1, h1, h2⟩ := hl
        obtain ⟨-, hc2, h3, h4⟩ := hl'
        exact ⟨hc2.symm.trans hc1, by omega⟩
      obtain ⟨hc, rfl⟩ := hcst
      exact .inl ⟨_, g, rfl, ⟨hg, hc, h8, h12⟩, ⟨a, hint, hcs⟩, rfl⟩
    | async i p =>
      obtain ⟨x, y, k, rfl⟩ := hasync i p a w l hint hcov hstg
      obtain ⟨-, sp, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hint
      have hi := event_thread_lt hX hget
      obtain ⟨h13, st', hst', hsrc⟩ := ht.store_tma hi hget
      have hl' := hsrc.2.1 x y k a.loc hloc
      have hla : l = a.loc := by
        obtain ⟨h1, h2, h3, h4⟩ := hcov
        rw [hsz] at h4
        cases l
        cases ha : a.loc
        rw [ha] at h1 h2 h3 h4
        simp only at h1 h2 h3 h4
        rw [h1, h2, show _ = _ from Nat.le_antisymm (by omega) h3]
      rw [← hla] at hl'
      have hcst : ctaOf L i.1 = c ∧ st' = st := by
        obtain ⟨-, hc1, h1, h2⟩ := hl
        obtain ⟨-, hc2, h3, h4⟩ := hl'
        exact ⟨hc2.symm.trans hc1, by omega⟩
      obtain ⟨hc, rfl⟩ := hcst
      exact .inr ⟨_, i, (x, y, k), rfl, ⟨hi, hc, h13⟩, ⟨pc, addr, sp, hget, hsrc⟩, rfl⟩
  same := by
    intro j g g' a a' w w' l hg hg' hne ha ha' _ hla hla' _
    have hth := gen_thread hpre hg hg' ha ha' hla hla'
    have hij : g.2 ≠ g'.2 := fun h => hne (Prod.ext hth h)
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact .inl (.single (.inl (po_of_overlap ha ha' hth hlt ⟨l, hla, hla'⟩)))
    · exact .inr (.single (.inl (po_of_overlap ha' ha hth.symm hlt ⟨l, hla', hla⟩)))
  later := by
    intro j j' g g' a a' w w' l hg hg' hjj ha ha' _ hla hla' _
    have hth := gen_thread hpre hg hg' ha ha' hla hla'
    have hlt : g.2 < g'.2 := by
      by_contra hge
      have := arrivals_mono (X := X) (stagedBar L c st) g.1 (Nat.le_of_not_lt hge)
      have h1 := hg.2.2
      have h2 := hg'.2.2
      rw [← hth] at h2
      omega
    exact .single (.inl (po_of_overlap ha ha' hth hlt ⟨l, hla, hla'⟩))
  publish := by
    intro j j' g i s a l hg hr hjj _ _ hcov hl
    exact publish_vis hH hst hg hr hjj hcov hl
  release := by
    intro j j' i s g a l hr hg hjj ha _ hcov _
    exact release_vis hX hH hst hr hg hjj ha hcov

/-- **Every conflict on a staging byte is ordered.** -/
theorem staging_ordered (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ht : OutputFacts L X) (hH : OutputHandoff L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k)) :
    ConflictsOrdered L X (InStaging L) := by
  intro e f a b l hc ha hb hl
  unfold InStaging at hl
  obtain ⟨hs, h1, h2⟩ := hl
  have hst : (l.addr - (L.sharedBase + 3072)) / 32768 < 2 := by omega
  refine (ring hpre hX ht hH hasync (c := l.cta) hst).ordered e f a b l hc ha hb ?_
  unfold InStage
  refine ⟨hs, rfl, ?_, ?_⟩ <;> omega

end Output

end
end PTX.Kernels.FlashAttn4Fwd.Proof

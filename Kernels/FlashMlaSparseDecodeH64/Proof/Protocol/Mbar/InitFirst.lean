-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.Bar0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.StartInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Lemmas.Kernel.ElectSource
public import Lemmas.Flow.ElectActor
public import Lemmas.Protocol.InitFirst
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Flow.CountTake

@[expose] public section

/-! # Every object is initialized first

* **N1** (`init_startup`, from `MbarRows`): an initialization by a launched thread is a startup
  use: the thread is in warp 0 and initializes the family `MbarFam.ofInit j` of its CTA with its
  count (the rows of the other roles have no initialization). Every use names an object of the
  thread's CTA (`use_cta`).
* Two threads of a CTA that won the election at pc 31 (full mask, `startup_elect`) are one thread
  (`won_unique`: warp 0 by N1, `elect_winner`); a thread initializes an object once before its
  barrier 0 (`init_once`), so an object has one initialization (`init_unique`).
* With barrier 0's publication (N3, `bar0_pub`) every other use of the object follows it
  (`use_after_bar0`), and the initialization exists (`won_inits` of the CTA's winner): the object's
  first record is its one initialization, `PairTmaRing.InitFirst X (mbarLoc L c f) f.count`
  (`initFirst`).

**Inputs not exported yet** (`InitRows`, lane A, from `startup_view`): an initialization is
before its thread's first barrier-0 event and after the thread's won election at pc 31 (`won`;
`startup_won` is the converse direction), and a thread past barrier 0 has a winner of the pc-31
election in its CTA that reaches barrier 0 (`winner`: barrier 0 needs warp 0, whose lanes elect
at pc 31). N3's inputs are `Bar0Rows` (`Protocol/Mbar/Bar0.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The startup facts the objects need beyond lane A's exports** (proposed exports). -/
structure InitRows (L : Launch) (X : Execution) : Prop where
  won : ∀ {g k n : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    e.kind = .mbInit l n → ((X.tr g).take k).countP isBar0 = 0 ∧
      ∃ j < k, ∃ mk inst, X.get (g, j) = some ⟨31, .elect mk inst (PTX.laneOf L g)⟩
  winner : ∀ {h f : Nat}, h < L.threads →
    (f < (X.tr h).length ∨ (f = (X.tr h).length ∧ Step.Released L X h)) →
    0 < ((X.tr h).take f).countP isBar0 →
    ∃ g j kb mk inst pcb cnt mode, g / L.block = h / L.block ∧
      X.get (g, j) = some ⟨31, .elect mk inst (PTX.laneOf L g)⟩ ∧
      X.get (g, kb) = some ⟨pcb, .bar 0 cnt mode⟩ ∧ ((X.tr g).take j).countP isBar0 = 0 ∧
      ((X.tr g).take kb).countP isBar0 = 0

/-- **Every use names an object of its thread's CTA.** -/
theorem use_cta {g k : Nat} {e : Event} {l : Loc} (hu : MbarUse L X g k e l) :
    ∃ f, l = MbarRow.loc L g f := by
  rcases hu with ⟨-, ⟨-, j, -, hl, -⟩⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨_, hl⟩
  all_goals cases h <;> exact ⟨_, ‹l = MbarRow.loc L g _›⟩

/-- **N1: only the startup initializes.** -/
theorem init_startup (hR : MbarRows P L X) {g k n : Nat} {e : Event} {l : Loc}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hk : e.kind = .mbInit l n) :
    MbarRow.warp L g = 0 ∧ ∃ j : Fin 23, l = MbarRow.loc L g (MbarFam.ofInit j) ∧
      n = (MbarFam.ofInit j).count := by
  have hm : Frame.MbarOf e l := by
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    rfl
  rcases mbar_use hR hg he hm with ⟨-, ⟨hw, j, -, hl, hk'⟩⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩ | ⟨-, h⟩
  · rw [hk] at hk'
    simp only [Kind.mbInit.injEq] at hk'
    exact ⟨hw, j, hl, hk'.2⟩
  all_goals
    cases h <;> simp_all [MbarRow.Wait, MbarRow.Arrive, MbarRow.Commit, MbarRow.Issue]

/-- The issuer of a record of `l` names `l`, and initializes it only for an initialization. -/
theorem record_issuer (hX : Consistent L kernel Assumptions.all m X) {l : Loc}
    {r} (hr : r ∈ X.objects l) :
    ∃ ev, X.get r.id.issuer = some ev ∧ Frame.MbarOf ev l ∧
      ((∃ c, ev.kind = .mbInit l c) → ∃ n, r.action = .init n) := by
  have hn : ∀ {k : Kind}, (∀ c, k ≠ .mbInit l c) →
      (∃ c, k = .mbInit l c) → ∃ n, r.action = .init n := fun hk ⟨c, h⟩ => (hk c h).elim
  cases AsyncCopy.record_source hX.tma.2.2.1 hr with
  | init hid he ha => rw [hid]; exact ⟨_, he, rfl, fun _ => ⟨_, ha⟩⟩
  | inval hid he _ => rw [hid]; exact ⟨_, he, rfl, hn nofun⟩
  | arrive hid he _ => rw [hid]; exact ⟨_, he, rfl, hn nofun⟩
  | wait hid he _ => rw [hid]; exact ⟨_, he, rfl, hn nofun⟩
  | increment hid he _ => rw [hid]; exact ⟨_, he, rfl, hn nofun⟩
  | tensor hid he hm _ => rw [hid]; exact ⟨_, he, hm, hn nofun⟩
  | arriveOn hid he hm _ _ => rw [hid]; exact ⟨_, he, hm.symm, hn nofun⟩
  | bulk hid he hc _ _ => rw [hid]; exact ⟨_, he, hc, hn nofun⟩
  | commit hid he ht _ => rw [hid]; exact ⟨_, he, ⟨_, ht⟩, hn nofun⟩
  | clc hid he hm htg _ => rw [hid]; exact ⟨_, he, ⟨_, htg, hm⟩, hn nofun⟩

/-- A family's count is a valid arrival count. -/
theorem count_valid (f : MbarFam) : MBarrier.validCount f.count := by
  cases f <;> simp only [MbarFam.count, MBarrier.validCount, MBarrier.limit] <;> omega

/-- No barrier-0 event before a later position leaves none before an earlier one. -/
theorem bar0_none {g k k' : Nat} (hkk : k ≤ k') (h : ((X.tr g).take k').countP isBar0 = 0) :
    ((X.tr g).take k).countP isBar0 = 0 :=
  Nat.eq_zero_of_le_zero (h ▸ (List.take_sublist_take_left (l := X.tr g) hkk).countP_le)

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X)
include hp hX hFw hR

omit hR in
/-- **Two initializing threads of one CTA that won the election at pc 31 are one thread.** -/
theorem won_unique {g g' j j' mk mk' inst inst' : Nat} (hc : g / L.block = g' / L.block)
    (hg : g < L.threads) (hg' : g' < L.threads) (hw : MbarRow.warp L g = 0)
    (hw' : MbarRow.warp L g' = 0)
    (hj : X.get (g, j) = some ⟨31, .elect mk inst (PTX.laneOf L g)⟩)
    (hj' : X.get (g', j') = some ⟨31, .elect mk' inst' (PTX.laneOf L g')⟩)
    (h0 : ((X.tr g).take j).countP isBar0 = 0) (h0' : ((X.tr g').take j').countP isBar0 = 0) :
    g = g' := by
  obtain ⟨hm, -⟩ := startup_elect hp hX hFw hj rfl h0
  obtain ⟨hm', -⟩ := startup_elect hp hX hFw hj' rfl h0'
  subst hm hm'
  have hb := hp.block
  have hx := tidOf_x_eq hp g
  have hx' := tidOf_x_eq hp g'
  simp only [MbarRow.warp] at hw hw'
  have hs : SameWarp L g g' := ⟨⟨hg, hg', hc⟩, by rw [hb]; omega⟩
  exact sameWarp_eq_of_lane_eq hs (elect_winner hX (e := (g, j)) (f := (g', j')) hj hj' hs)

/-- **An object has one initialization**, with the family's count. -/
theorem init_unique (hI : InitRows L X) {c : Nat} {f : MbarFam} {i i' : EvId}
    {pc pc' n n' : Nat} (hi : X.get i = some ⟨pc, .mbInit (mbarLoc L c f) n⟩)
    (hi' : X.get i' = some ⟨pc', .mbInit (mbarLoc L c f) n'⟩) :
    i = i' ∧ n = f.count := by
  obtain ⟨g, k⟩ := i
  obtain ⟨g', k'⟩ := i'
  have hg := Frame.lt_of_get hX hi
  have hg' := Frame.lt_of_get hX hi'
  obtain ⟨hw, j, hl, hn⟩ := init_startup hR hg hi rfl
  obtain ⟨hw', j', hl', -⟩ := init_startup hR hg' hi' rfl
  obtain ⟨hc, hf⟩ := fam_eq hl
  obtain ⟨hc', -⟩ := fam_eq hl'
  obtain ⟨h0, a, ha, mk, inst, hja⟩ := hI.won hg hi rfl
  obtain ⟨h0', a', ha', mk', inst', hja'⟩ := hI.won hg' hi' rfl
  have hgg := won_unique hp hX hFw (hc.symm.trans hc') hg hg' hw hw' hja hja'
    (bar0_none ha.le h0) (bar0_none ha'.le h0')
  subst hgg
  refine ⟨by rw [init_once hp hX hFw hi hi' h0 h0'], ?_⟩
  rw [hn, hf]

/-- **Every object is initialized first**: the first record of `mbarLoc L c f` is its one
initialization, with the family's count, by the CTA's winner of the pc-31 election. -/
theorem initFirst (hI : InitRows L X) (hB : Bar0Rows L X) (c : Nat) (f : MbarFam) :
    PairTmaRing.InitFirst X (mbarLoc L c f) f.count := by
  intro r hr
  obtain ⟨ev, hget, hm, -⟩ := record_issuer hX hr
  generalize r.id.issuer = u at hget
  obtain ⟨h, k⟩ := u
  have hh := Frame.lt_of_get hX hget
  obtain ⟨f', hl⟩ := use_cta (mbar_use hR hh hget hm)
  obtain ⟨hch, -⟩ := fam_eq hl
  -- an initialization of the object before its thread's first barrier-0 event
  obtain ⟨g0, i0, pc0, he0, h00⟩ : ∃ g0 i0 pc0,
      X.get (g0, i0) = some ⟨pc0, .mbInit (mbarLoc L c f) f.count⟩ ∧
        ((X.tr g0).take (i0 + 1)).countP isBar0 = 0 := by
    by_cases hi : ∃ n, ev.kind = .mbInit (mbarLoc L c f) n
    · obtain ⟨n, hn⟩ := hi
      obtain ⟨pce, kd⟩ := ev
      simp only at hn
      subst hn
      obtain ⟨-, hn'⟩ := init_unique hp hX hFw hR hI hget hget
      subst hn'
      obtain ⟨h0, -⟩ := hI.won hh hget rfl
      exact ⟨h, k, pce, hget, by rw [countP_take_succ_false hget rfl]; exact h0⟩
    · have hpos := use_after_bar0 hp hX hFw hget hm (fun c' hc => hi ⟨c', hc⟩)
      have hlen : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hget).1
      obtain ⟨g, j, kb, mk, inst, pcb, cnt, mode, hcg, hj, hb, h0j, h0b⟩ :=
        hI.winner hh (.inl hlen) hpos
      obtain ⟨i, hikb, pc, hgi⟩ := won_inits hp hX hFw hj rfl hb h0j h0b f
      rw [hcg, ← hch] at hgi
      exact ⟨g, i, pc, hgi, bar0_none hikb h0b⟩
  have hg0 := Frame.lt_of_get hX he0
  obtain ⟨-, j0, hl0, -⟩ := init_startup hR hg0 he0 rfl
  obtain ⟨hc0, -⟩ := fam_eq hl0
  refine initFirst_of_published hX ⟨pc0, he0⟩ (count_valid f)
    (fun i pc n hi => init_unique hp hX hFw hR hI hi he0) (fun s hs hn => ?_) _ hr
  obtain ⟨ev', hget', hm', hnot⟩ := record_issuer hX hs
  generalize s.id.issuer = u' at hget' ⊢
  obtain ⟨h', k'⟩ := u'
  have hh' := Frame.lt_of_get hX hget'
  have hpos := use_after_bar0 hp hX hFw hget' hm' (fun c' hc => by
    obtain ⟨n, hn'⟩ := hnot ⟨c', hc⟩
    exact hn n hn')
  obtain ⟨f'', hl'⟩ := use_cta (mbar_use hR hh' hget' hm')
  obtain ⟨hch', -⟩ := fam_eq hl'
  refine .inl (bar0_pub hp hX hFw hB ⟨hg0, hh', hc0.symm.trans hch'⟩ h00
    (List.getElem?_eq_some_iff.mp (show (X.tr h')[k']? = some ev' from hget')).1 hpos)
end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

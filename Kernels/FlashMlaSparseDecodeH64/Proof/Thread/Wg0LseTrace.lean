-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Lemmas.Flow.WriteSpace

public section

/-! # Coverage of the logical LSE rows by complete traces -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0LseTrace
open PTX PTX.Flow Wg0

noncomputable section

private def sitePhase (s : Wg0.Site) : Nat :=
  if s = .lseStore then 1 else if s.needsRowTotal then 2 else 0

private def phase (d : Option Machine.ThreadD) : Nat :=
  match d with
  | some (.wg0 d) => sitePhase d.site
  | some .done => 2
  | _ => 0

private def followsWg0 : Option Machine.ThreadD → Prop
  | none | some (.prologue _) | some (.wg0 _) | some .done => True
  | _ => False

private theorem lse_advance {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hw : tidOf L g % 128 < 64) (hn : Wg0.next P L g d e = some (some d')) :
    sitePhase d'.site ≤ sitePhase d.site + 1 := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        simp_all [sitePhase, Wg0.Site.needsRowTotal]
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      simp_all [sitePhase, Wg0.Site.needsRowTotal]
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [sitePhase, Wg0.Site.needsRowTotal, Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink,
      Wg0.epiAfterBar]
  all_goals try (split_ifs <;> simp_all)

private theorem phase_init {P : Params} {L : Launch} {g : Nat} :
    sitePhase (Wg0.init P L g).site = 0 := by
  unfold Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  dsimp only
  split_ifs <;> rfl

private theorem phase_advance {P : Params} {L : Launch} {g : Nat}
    {d d' : Option Machine.ThreadD} {e : Event} (hwg : wgOf L g = 0)
    (hhalf : tidOf L g % 128 < 64) (ha : followsWg0 d)
    (hn : (Machine.machine P L g).next d e = some d') :
    followsWg0 d' ∧ phase d' ≤ phase d + 1 := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    exact ⟨trivial, Nat.zero_le _⟩
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact ⟨trivial, Nat.zero_le _⟩
      · split at hn
        · rename_i w _
          split_ifs at hn with hw
          · have hw0 : w = 0 := Fin.ext (hw.symm.trans hwg)
            subst w
            cases hn
            exact ⟨trivial, by
              change sitePhase (Wg0.init P L g).site ≤ 1
              rw [phase_init (P := P) (L := L) (g := g)]
              decide⟩
          · cases hn
            exact ⟨trivial, Nat.zero_le _⟩
        · cases hn
          exact ⟨trivial, Nat.zero_le _⟩
      · cases hn
    case wg0 s =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i t hstep
        cases hn
        exact ⟨trivial, lse_advance hhalf hstep⟩
      · split_ifs at hn with hexit
        · cases hn
          rcases hexit with h | h <;>
            exact ⟨trivial, by simp [phase, sitePhase, h, Wg0.Site.needsRowTotal]⟩
        · cases hn
          exact ⟨trivial, Nat.zero_le _⟩
      · cases hn
    case done => cases hn
    all_goals exact ha.elim

private theorem phase_one {d : Option Machine.ThreadD} (h : phase d = 1) :
    ∃ s : D, d = some (.wg0 s) ∧ s.site = .lseStore := by
  cases d with
  | none => cases h
  | some d =>
    cases d <;> try cases h
    case wg0 s =>
      refine ⟨s, rfl, ?_⟩
      change sitePhase s.site = 1 at h
      unfold sitePhase at h
      split_ifs at h with he
      · exact he
      all_goals contradiction

private def LseHistory (P : Params) (L : Launch) (g : Nat)
    (d : Option Machine.ThreadD) (es : List Event) : Prop :=
  followsWg0 d ∧
    (Machine.machine P L g).after (Machine.machine P L g).init es = some d ∧
    (phase d = 2 →
      ∃ i < es.length, ∃ s : D,
        (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
          some (some (.wg0 s)) ∧ s.site = .lseStore ∧
          ∃ ev a bs, es[i]? = some ev ∧ ev.kind = .wr a bs)

private theorem lse_history_step {P : Params} {L : Launch} {g : Nat}
    {es : List Event} {e : Event} {d d' : Option Machine.ThreadD}
    (hwg : wgOf L g = 0) (hhalf : tidOf L g % 128 < 64)
    (hh : LseHistory P L g d es) (hn : (Machine.machine P L g).next d e = some d') :
    LseHistory P L g d' (es ++ [e]) := by
  obtain ⟨ha, hp⟩ := phase_advance hwg hhalf hh.1 hn
  refine ⟨ha, ?_, ?_⟩
  · rw [PTX.Flow.Machine.after_snoc, hh.2.1]
    exact hn
  · intro he
    by_cases hbefore : phase d = 2
    · obtain ⟨i, hi, v, hv, hs, ev, a, bs, hget, hkind⟩ := hh.2.2 hbefore
      exact ⟨i, by simp; omega, v,
        by simpa only [List.take_append_of_le_length hi.le] using hv, hs, ev, a, bs,
        by simpa only [List.getElem?_append_left hi] using hget, hkind⟩
    · have hcap : phase d ≤ 2 := by
        rcases d with _ | d
        · decide
        cases d <;> simp only [phase, sitePhase]
        all_goals (try split_ifs) <;> decide
      have hone : phase d = 1 := by omega
      obtain ⟨v, rfl, hs⟩ := phase_one hone
      have htake : (es ++ [e]).take es.length = es :=
        (List.take_append_of_le_length (Nat.le_refl es.length)).trans List.take_length
      refine ⟨es.length, by simp, v, htake.symm ▸ hh.2.1, hs, e, ?_⟩
      have hwrite : ∃ a bs, e.kind = .wr a bs := by
        change Machine.next P L g (.wg0 v) e = some d' at hn
        cases he' : e.kind <;> simp [Machine.next, Wg0.next, Wg0.nextSite, hs, he'] at hn
        case wr => exact ⟨_, _, rfl⟩
      obtain ⟨a, bs, hkind⟩ := hwrite
      exact ⟨a, bs, by simp, hkind⟩

/-- Every complete lane in the two LSE warps has the actual global LSE write. -/
theorem complete_lse_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomplete : Complete L X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads) (hw : warpOf L g < 2) :
    ∃ i d a, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
      d.site = .lseStore ∧ X.Writes (g, i) a (lseReg d).toBytes ∧
      a.loc = lseLocOf P L g ∧ a.size = 4 := by
  have hwg : wgOf L g = 0 := by
    have h := Wg0.tid_eq L g
    have hl := Wg0.laneLt L g
    change tidOf L g / 128 = 0
    omega
  have hhalf : tidOf L g % 128 < 64 := by
    have h := Wg0.tid_eq L g
    have hl := Wg0.laneLt L g
    omega
  obtain ⟨i, e, he, _, hst⟩ := Wg0OutputVisits.completeDone hX hcomplete
    (fun _ hg => (hs _ hg).machine) ht hg hwg
  have h := ((hs g hg).machine.produces (hX.thr g hg)).prefix_induction
    (LseHistory P L g) ⟨trivial, rfl, fun h => by cases h⟩
    (fun _ _ _ _ _ hprev _ hnext => lse_history_step hwg hhalf hprev hnext)
    i (some .done) hst
  obtain ⟨k, hk, d, hd, hdsite, ev, a₀, bs₀, heget, hekind₀⟩ := h.2.2 rfl
  have hki : k < i := lt_of_lt_of_le hk (List.length_take_le _ _)
  have hget : X.get (g, k) = some ev := by
    change (X.tr g)[k]? = some ev
    simpa [List.getElem?_take, hki] using heget
  have hstate : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) := by
    have htake : ((X.tr g).take i).take k = (X.tr g).take k := by
      rw [List.take_take, Nat.min_eq_left hki.le]
    change (Machine.machine P L g).after (Machine.machine P L g).init
      ((X.tr g).take k) = some (some (.wg0 d))
    exact htake ▸ hd
  obtain ⟨idx, kind⟩ := ev
  change kind = .wr a₀ bs₀ at hekind₀
  subst kind
  obtain ⟨t, ins, o, ha, hi, hc, hf⟩ := Frame.fired_site hs hX hget hstate
  have ho : o.isSome := by
    rcases fires_write_tmpl hf with ⟨u, hu⟩ | ⟨u, hu, _⟩
    · rw [hu] at hf
      rcases hf with ⟨_, rfl⟩
      rfl
    · rw [hu] at hf
      rcases hf with ⟨_, _, _, rfl⟩
      rfl
  obtain ⟨u, rfl⟩ := Option.isSome_iff_exists.mp ho
  obtain ⟨a, hekind, hloc, hsize, _⟩ :=
    fires_lseStore hpre (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg) hdsite ha hi hc hf
  obtain ⟨rfl, rfl⟩ := Kind.wr.inj hekind
  exact ⟨k, d, _, hstate, hdsite, ⟨idx, hget⟩, hloc, hsize⟩

private theorem site_after_store {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hp : 0 < sitePhase d.site) (hn : Wg0.next P L g d e = some (some d')) :
    sitePhase d'.site = 2 := by
  cases hd : d.site <;> simp [sitePhase, hd] at hp
  all_goals simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [sitePhase, Wg0.epiAfterBar]
  all_goals split_ifs <;> simp_all

private theorem after_store_step {P : Params} {L : Launch} {g : Nat}
    {d d' : Option Machine.ThreadD} {e : Event} (hp : d = none ∨ 0 < phase d)
    (hn : (Machine.machine P L g).next d e = some d') :
    d' = none ∨ phase d' = 2 := by
  cases d with
  | none =>
    change some none = some d' at hn
    exact .inl (Option.some.inj hn).symm
  | some d =>
    change Machine.next P L g d e = some d' at hn
    have h := hp.resolve_left (by simp)
    cases d <;> try contradiction
    case wg0 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i v hv
        cases hn
        exact .inr (site_after_store h hv)
      · split_ifs at hn
        · cases hn
          exact .inr rfl
        · cases hn
          exact .inl rfl
      · cases hn

private theorem lse_reached_by_first_half {P : Params} {L : Launch} {g : Nat} {d d' : D}
    {e : Event} (hh : d.site = .lseStore → tidOf L g % 128 < 64)
    (hn : Wg0.next P L g d e = some (some d')) (hd' : d'.site = .lseStore) :
    tidOf L g % 128 < 64 := by
  by_contra h
  have hne : d.site ≠ .lseStore := fun hd => h (hh hd)
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        cases hd'
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases hd'
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink, Wg0.epiAfterBar]
  all_goals split_ifs at hd'

private def WriterHalf (L : Launch) (g : Nat) (d : Option Machine.ThreadD) : Prop :=
  ∀ v, d = some (.wg0 v) →
    wgOf L g = 0 ∧ (v.site = .lseStore → tidOf L g % 128 < 64)

private theorem writer_half_step {P : Params} {L : Launch} {g : Nat}
    {d d' : Option Machine.ThreadD} {e : Event} (hh : WriterHalf L g d)
    (hn : (Machine.machine P L g).next d e = some d') : WriterHalf L g d' := by
  rintro v rfl
  cases d with
  | none => cases hn
  | some d =>
    change Machine.next P L g d e = some (some (.wg0 v)) at hn
    cases d <;> simp only [Machine.next] at hn
    case prologue s =>
      split at hn
      · cases hn
      · split at hn
        · rename_i w _
          split_ifs at hn with hw
          · fin_cases w <;> simp [Machine.roleStart] at hn
            subst v
            refine ⟨hw, fun hv => ?_⟩
            have hz := phase_init (P := P) (L := L) (g := g)
            rw [hv] at hz
            contradiction
          · cases hn
        · cases hn
      · cases hn
    case wg0 d =>
      split at hn
      · rename_i d' hd'
        cases hn
        exact ⟨(hh d rfl).1, fun hv => lse_reached_by_first_half (hh d rfl).2 hd' hv⟩
      · split_ifs at hn <;> cases hn
      · cases hn
    case head =>
      have hhead : Machine.headStart P L g ≠ some (.wg0 v) := by
        unfold Machine.headStart
        split_ifs <;> simp
      split at hn
      · split_ifs at hn
        · cases hhstart : Machine.headStart P L g with
          | none => simp [hhstart] at hn
          | some d =>
            simp [hhstart] at hn
            exact (hhead (hhstart.trans (congrArg some hn))).elim
        · simp at hn
      · cases hn
    all_goals repeat' split at hn
    all_goals simp at hn

/-- A global LSE store can only come from the two warps that own the 64 rows. -/
theorem writer_warp {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (hg : g < L.threads) {v : D}
    (hv : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 v)))
    (hsite : v.site = .lseStore) : warpOf L g < 2 := by
  have h := ((hs g hg).machine.produces (hX.thr g hg)).prefix_induction
    (fun d _ => WriterHalf L g d) (by rintro _ h; cases h)
    (fun _ _ _ _ _ h _ hn => writer_half_step h hn) k (some (.wg0 v)) hv v rfl
  have hhalf := h.2 hsite
  have hwg := h.1
  change tidOf L g / 128 = 0 at hwg
  have ht := Wg0.tid_eq L g
  omega

private def PassedStore (P : Params) (L : Launch) (g : Nat)
    (d : Option Machine.ThreadD) (es : List Event) : Prop :=
  (Machine.machine P L g).after (Machine.machine P L g).init es = some d ∧
    (∀ k < es.length, ∀ v,
      (Machine.machine P L g).after (Machine.machine P L g).init (es.take k) =
        some (some (.wg0 v)) → v.site = .lseStore → d = none ∨ phase d = 2)

private theorem passed_store_step {P : Params} {L : Launch} {g : Nat}
    {es : List Event} {e : Event} {d d' : Option Machine.ThreadD}
    (hh : PassedStore P L g d es) (hn : (Machine.machine P L g).next d e = some d') :
    PassedStore P L g d' (es ++ [e]) := by
  refine ⟨?_, ?_⟩
  · rw [PTX.Flow.Machine.after_snoc, hh.1]
    exact hn
  · intro k hk v hv hs
    have hle : k ≤ es.length := by simpa using hk
    apply after_store_step ?_ hn
    rw [List.take_append_of_le_length hle] at hv
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · rw [List.take_length, hh.1] at hv
      injection hv with hd
      exact .inr (by rw [hd]; simp [phase, sitePhase, hs])
    · rcases hh.2 k hlt v hv hs with hd | hd
      · exact .inl hd
      · exact .inr (by omega)

/-- The machine has at most one LSE store per lane. -/
theorem store_unique {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k j : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (hg : g < L.threads) (hk : k < (X.tr g).length) (hj : j < (X.tr g).length)
    {v w : D} (hv : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 v)))
    (hw : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 w)))
    (hsv : v.site = .lseStore) (hsw : w.site = .lseStore) : k = j := by
  have hnot : ∀ {a b : Nat} {u v : D}, b < (X.tr g).length → a < b →
      Frame.stateAt (Machine.code P L) X g a = some (some (.wg0 u)) →
      Frame.stateAt (Machine.code P L) X g b = some (some (.wg0 v)) →
      u.site = .lseStore → v.site = .lseStore → False := by
    intro a b u v hb hab hu hv hsu hsv
    have h := ((hs g hg).machine.produces (hX.thr g hg)).prefix_induction
      (PassedStore P L g) ⟨rfl, by simp⟩
      (fun _ _ _ _ _ h _ hn => passed_store_step h hn)
      b (some (.wg0 v)) hv
    have ha : a < ((X.tr g).take b).length := by simp [List.length_take, hab, hab.trans hb]
    have htake : ((X.tr g).take b).take a = (X.tr g).take a := by
      rw [List.take_take, Nat.min_eq_left hab.le]
    change (Machine.machine P L g).after (Machine.machine P L g).init
      ((X.tr g).take a) = some (some (.wg0 u)) at hu
    have hphase := h.2 a ha u (htake.symm ▸ hu) hsu
    simp [phase, sitePhase, hsv] at hphase
  rcases Nat.lt_trichotomy k j with hlt | he | hgt
  · exact (hnot hj hlt hv hw hsv hsw).elim
  · exact he
  · exact (hnot hk hgt hw hv hsw hsv).elim


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0LseTrace

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitObject

@[expose] public section

/-! # A unit object whose arrivals are gated by its consumers' polls

A proof tool. A unit object (`Unit.Obj`) whose consumers `cons` poll it with offset `δ` and whose
producers reuse it only after their partner consumers' polls (`Gate`): each producer `a` has a
partner consumer, each consumer `h` a partner producer (`pair`), and producer `a`'s arrival of use
`s` follows each partner `h`'s successful poll with `s + δ - 1` earlier successful polls
(`gate`, a dependency path (`DepStep`) from the poll's return, through any other
synchronization: FA4's statistics credit, where the correction's credit arrival follows its
`bar.sync` on a named barrier, released by its partner softmax warp's `bar.arrive`, which follows
the softmax's credit poll). The gate's dependency path need not cross the object, so no other
object's attribution is used.

* **Arrivals lie in the phase of their use** (`phase_eq`), by induction on the history position:
  the gating poll is before the arrival in the object's history (DEP-ORDER) and found a
  phase of at least the use (`selected_poll_phase_ge`); a later phase would hold, before the
  arrival, the arrivals of its use of every producer (`Obj.phase_all`), the arriving one's too.
* **A consumer's poll with `q + δ` earlier successful polls found phase `q + 1`**
  (`poll_found`): a later phase would hold its partner producer's arrival of use `q + 1`, which the
  poll precedes in the dependency order.
* **The unit handoff** (`handoff`): that poll observes phase `q`, which holds every producer's
  arrival of use `q` (`MbarRing.UnitHandoff`, with release arrivals, acquire polls and producers
  and consumers of one CTA). -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- **A unit object gated by its consumers' polls.** -/
structure Gate (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (m : Loc)
    (N : Nat) (prod : Fin N → Nat) (δ : Nat) (cons : Nat → Prop) (pair : Fin N → Nat → Prop) :
    Prop extends Obj X m N prod δ where
  /-- Every consumer has a partner producer. -/
  cover : ∀ h, cons h → ∃ a, pair a h
  /-- Every producer has a partner consumer. -/
  partner : ∀ a, ∃ h, pair a h
  /-- A producer's arrival of use `s` (with `s + δ ≥ 1`) follows, in the dependency order, each
  partner's poll with `s + δ - 1` earlier successful ones. -/
  gate : ∀ {a : Fin N} {h i pc : Nat} {sc : MbarScope}, pair a h →
    X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ →
    1 ≤ arrivals m ((X.tr (prod a)).take i) + δ →
      ∃ j pc' p acq sc', X.get (h, j) = some ⟨pc', .wait m p true acq sc'⟩ ∧
        okPolls m ((X.tr h).take j) + 1 = arrivals m ((X.tr (prod a)).take i) + δ ∧
        Relation.TransGen (DepStep L K X) (.thread (h, j), true) (.thread (prod a, i), false)
  /-- A consumer's successful poll acquires. -/
  acq : ∀ {h j pc p : Nat} {acq : Bool} {sc : MbarScope}, cons h →
    X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ → acq = true
  /-- Producers and consumers are threads of one CTA. -/
  cta : ∀ a h, cons h → SameCta L (prod a) h

namespace Gate

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N δ : Nat} {prod : Fin N → Nat} {cons : Nat → Prop} {pair : Fin N → Nat → Prop}

/-- The record of a successful poll, with its thread's earlier successful polls selected. -/
theorem poll_record (hX : Consistent L K A mem0 X) (G : Gate L K A X m N prod δ cons pair)
    {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩) :
    ∃ k w, (X.objects m)[k]? = some w ∧ w.id = .thread (h, j) ∧ w.reply.waited = some true ∧
      w.fault = none ∧ objectThreadSelected h w.id = true ∧
      selectedBefore (objectThreadSelected h) (X.objects m) k = okPolls m ((X.tr h).take j) := by
  have hlt : okPolls m ((X.tr h).take j) < okPolls m (X.tr h) := by
    have h1 := MbarRing.Poll.okPoll_get he
    have h2 := MbarRing.Poll.okPolls_mono m (X.tr h) (show j + 1 ≤ (X.tr h).length from
      (List.getElem?_eq_some_iff.mp he).1)
    rw [List.take_length] at h2
    omega
  obtain ⟨k, w, -, hk, hwid, -, hww, hwf, hsel⟩ := MbarRing.Poll.record hX (G.pclean hX) hlt
  rw [MbarRing.Poll.nth_eq he] at hwid
  exact ⟨k, w, hk, hwid, hww, hwf, objectThreadSelected_iff.mpr ⟨_, hwid⟩, hsel⟩

/-- A record that a successful poll precedes in the dependency order is after it in the
history. -/
theorem poll_before (hX : Consistent L K A mem0 X) {h j k kw : Nat} {u : Ref}
    {r w : Record Ref} (hp : Relation.TransGen (DepStep L K X) (.thread (h, j), true) (u, false))
    (hk : (X.objects m)[k]? = some r) (hid : r.id = u) (hkw : (X.objects m)[kw]? = some w)
    (hwid : w.id = .thread (h, j)) (hne : r.action ≠ w.action) : kw < k := by
  rcases Nat.lt_trichotomy kw k with hlt | rfl | hgt
  · exact hlt
  · rw [hk] at hkw
    cases hkw
    exact absurd rfl hne
  · exact absurd ⟨k, kw, r, w, hk, hid, hkw, hwid, hgt⟩
      (MbarRing.Round.Slot.not_before_of_reach hX hp)

/-- **Every arrival lies in the phase of its use.** -/
theorem phase_eq (hX : Consistent L K A mem0 X) (G : Gate L K A X m N prod δ cons pair) :
    ∀ k (r : Record Ref) (a : Fin N) (i c tx : Nat), (X.objects m)[k]? = some r →
      r.fault = none → r.action = .arrive c tx → r.id = .thread (prod a, i) →
      phaseAt (X.objects m) k = some (arrivals m ((X.tr (prod a)).take i)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro r a i c tx hk hf ha hid
  have hch := X.objects_checked hX m
  have hni := G.noInval
  obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX G.init hni hk
    (by intro n; rw [ha]; simp)
  have hkl : k < (X.objects m).length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨pc, sc, he⟩ := G.arrive_of_id hk ha hid
  rw [show phaseAt (X.objects m) k = some st.phase by simp [phaseAt, hst]]
  congr 1
  set s := arrivals m ((X.tr (prod a)).take i) with hs
  -- lower bound: the gating poll found a phase of at least `s`
  have hlo : s ≤ st.phase := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · omega
    obtain ⟨h, hpair⟩ := G.partner a
    obtain ⟨j, pcw, p, acq, scw, hw, hcnt, hpath⟩ := G.gate hpair he (by omega)
    obtain ⟨kw, w, hkw, hwid, hww, -, hsel, hsb⟩ := G.poll_record hX hw
    obtain ⟨stw, hstw, hge, -⟩ := hch.selected_poll_phase_ge hni _ G.δ_le (G.alt hX h) hkw hsel hww
    have hwa : w.action ≠ r.action := by
      obtain ⟨-, p', -, hpa, -⟩ := hch.okPoll hkw hww
      rw [hpa, ha]
      simp
    have hlt := poll_before hX hpath hk hid hkw hwid (Ne.symm hwa)
    obtain ⟨st', hst', hle⟩ := hch.phase_mono hni hlt.le hkl.le hstw
    rw [hst] at hst'
    cases hst'
    omega
  -- upper bound: a later phase would hold this producer's arrival of use `s` before it
  by_contra hne
  obtain ⟨p, r', i', hpk, hp, -, ha', hid', -, hu'⟩ := G.phase_all hX (j := k) (q := s) hkl.le
    hst (by omega) (fun p hpk r a i c tx hp hf ha hid hph => by
      have := ih p hpk r a i c tx hp hf ha hid
      rw [hph] at this
      exact (Option.some.inj this).symm) a
  obtain ⟨pc', sc', he'⟩ := G.arrive_of_id hp ha' hid'
  have hii := arr_index_eq he he' (hu'.symm ▸ hs.symm ▸ rfl)
  subst hii
  have := ObjectInit.checked_record_index_eq hch hp hk (hid'.trans hid.symm)
  omega

/-- **A consumer's poll with `q + δ` earlier successful polls found phase `q + 1`** and observed
phase `q`. -/
theorem poll_found (hX : Consistent L K A mem0 X) (G : Gate L K A X m N prod δ cons pair)
    {h j pc p q : Nat} {acq : Bool} {sc : MbarScope} (hh : cons h)
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩)
    (hq : okPolls m ((X.tr h).take j) = q + δ) :
    ∃ k w st, (X.objects m)[k]? = some w ∧ w.id = .thread (h, j) ∧
      w.reply.waited = some true ∧ w.fault = none ∧
      stateBefore (X.objects m) k = some st ∧ st.phase = q + 1 ∧
      observedAt (X.objects m) k = some q := by
  have hch := X.objects_checked hX m
  have hni := G.noInval
  obtain ⟨k, w, hk, hwid, hww, hwf, hsel, hsb⟩ := G.poll_record hX he
  have hkl : k < (X.objects m).length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨st, hst, hph⟩ := hch.selected_poll_phase_eq hni _ G.δ_le (G.alt hX h) hk hsel hww
    (fun st hst => by
      rw [hsb, hq]
      by_contra hgt
      obtain ⟨a, hpair⟩ := G.cover h hh
      obtain ⟨p', r, i, hpk, hp, -, ha, hid, -, hu⟩ := G.phase_all hX (j := k) (q := q + 1)
        hkl.le hst (by have := G.δ_le; omega)
        (fun p' _ r a i c tx hp hf ha hid hph => by
          have := G.phase_eq hX p' r a i c tx hp hf ha hid
          rw [hph] at this
          exact (Option.some.inj this).symm) a
      obtain ⟨pca, sca, hea⟩ := G.arrive_of_id hp ha hid
      obtain ⟨j', pcw, p'', acq', scw, hw', hcnt, hpath⟩ := G.gate hpair hea (by omega)
      have hjj := MbarRing.Poll.okPoll_index_unique hw' he (by omega)
      subst hjj
      have hwa : w.action ≠ r.action := by
        obtain ⟨-, p', -, hpa, -⟩ := hch.okPoll hk hww
        rw [hpa, ha]
        simp
      have := poll_before hX hpath hp hid hk hwid (Ne.symm hwa)
      omega)
  rw [hsb, hq] at hph
  obtain ⟨st', hst', -, ho⟩ := MbarRing.Poll.observed_some hch hni G.δ_le (G.alt hX h) hk hsel hww
    (by rw [hsb, hq]; omega)
  rw [hst] at hst'
  cases hst'
  exact ⟨k, w, st, hk, hwid, hww, hwf, hst, by omega, by rw [ho]; congr 1; omega⟩

/-- Scopes of two threads of one CTA meet. -/
theorem scopesMeet {g h : Nat} (hs : SameCta L g h) (us ws : MbarScope) :
    ScopesMeet L us g ws h := by
  obtain ⟨hg, hh, hc⟩ := hs
  constructor
  · cases us
    · exact ⟨hg, hh, hc⟩
    · exact ⟨hg, hh, congrArg _ hc⟩
    · exact ⟨hg, hh⟩
    · exact ⟨hg, hh⟩
  · cases ws
    · exact ⟨hh, hg, hc.symm⟩
    · exact ⟨hh, hg, congrArg _ hc.symm⟩
    · exact ⟨hh, hg⟩
    · exact ⟨hh, hg⟩

/-- **The unit handoff.** A consumer's successful poll with `q + δ` earlier ones synchronizes with
every producer's arrival of use `q`. -/
theorem handoff (hX : Consistent L K A mem0 X) (G : Gate L K A X m N prod δ cons pair) :
    MbarRing.UnitHandoff L X m (fun g => ∃ a, g = prod a) cons δ := by
  intro h j pc p acq sc q hh he hq g ⟨a, hga⟩
  subst hga
  have hch := X.objects_checked hX m
  obtain ⟨k, w, st, hk, hwid, hww, hwf, hst, hph, ho⟩ := G.poll_found hX hh he hq
  obtain ⟨p', r, i, -, hp, hf, ha, hid, hrph, huse⟩ := G.phase_all hX (j := k) (q := q)
    (List.getElem?_eq_some_iff.mp hk).1.le hst (by omega)
    (fun p' _ r a i c tx hp hf ha hid hph => by
      have := G.phase_eq hX p' r a i c tx hp hf ha hid
      rw [hph] at this
      exact (Option.some.inj this).symm) a
  obtain ⟨pca, sca, hea⟩ := G.arrive_of_id hp ha hid
  have hacq := G.acq hh he
  subst hacq
  have hu := MbarRing.Slot.updateBeforeWait_of_phase hch G.noInval hp hf hk hwf hww hrph ho
  rw [hid, hwid] at hu
  exact ⟨i, huse, sca, ⟨0, 1, pca, hea⟩, sc, ⟨⟨pc, p, he⟩, hu⟩, scopesMeet (G.cta a h hh) _ _⟩

end Gate
end
end PTX.MbarRing.Unit
